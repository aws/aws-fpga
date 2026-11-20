// ============================================================================
// Amazon FPGA Hardware Development Kit
//
// Copyright 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
//
// Licensed under the Amazon Software License (the "License"). You may not use
// this file except in compliance with the License. A copy of the License is
// located at
//
//    http://aws.amazon.com/asl/
//
// or in the "license" file accompanying this file. This file is distributed on
// an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, express or
// implied. See the License for the specific language governing permissions and
// limitations under the License.
// ============================================================================

#define _POSIX_C_SOURCE 200809L

#include "test_dram_hbm_dma.h"

#include <errno.h>
#include <fcntl.h>
#include <inttypes.h>
#include <poll.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <unistd.h>

#include "fpga_clkgen.h"
#include "fpga_dma.h"
#include "fpga_dma_mem.h"
#include "fpga_mgmt.h"
#include "fpga_pci.h"
#include "test_dram_dma_common.h"
#include "utils/lcd.h"

#define GIB(x) ((size_t)((x)*1024 * 1024 * 1024ull))

/* 256 MiB is chosen as the DMA call size for its high throughput. For each
 * call the driver allocates one physically contiguous list of 4 KiB page
 * pointers, 512 KiB at this size. On a host with fragmented memory that
 * allocation can fail, and the call returns ENOMEM. The regression suite
 * overrides the size to keep its buffers small. */
#ifndef CHUNK_SIZE
#define CHUNK_SIZE ((size_t)256 << 20)
#endif
#define STAMP_SIZE sizeof(uint64_t)
#define ARENA_SIZE (2 * CHUNK_SIZE)

/* Memory map of cl_dram_hbm_dma and cl_mem_perf: HBM starts where DDR ends, so
 * the 80 GiB form one contiguous range.
 * DDR: 0x00_0000_0000 - 0x0F_FFFF_FFFF (64 GiB)
 * HBM: 0x10_0000_0000 - 0x13_FFFF_FFFF (16 GiB)
 * The regression suite overrides the sizes to keep its buffers small. */
#ifndef DDR_SIZE
#define DDR_SIZE GIB(64)
#endif
#ifndef HBM_SIZE
#define HBM_SIZE GIB(16)
#endif

#define ENOMEM_HINT                                                                                      \
  ". The driver could not allocate memory for one DMA call. Lower CHUNK_SIZE in test_dram_hbm_dma.c " \
  "and rebuild, or compact host memory with 'sudo sysctl vm.compact_memory=1' and rerun."

/* use the standard out logger */
static const struct logger* logger = &logger_stdout;

/* AXI Master register offsets */
#define AXI_MSTR_CCR_OFFSET 0x500
#define AXI_MSTR_CAHR_OFFSET 0x504
#define AXI_MSTR_CALR_OFFSET 0x508
#define AXI_MSTR_CWDR_OFFSET 0x50C
#define AXI_MSTR_CRDR_OFFSET 0x510

#define DDR_BASE_ADDR_HI  0x00000000
#define DDR_BASE_ADDR_LO  0x00001000  /* Small offset into DDR */
#define HBM_BASE_ADDR_HI  0x00000010  /* 64GB = 0x10_0000_0000 */
#define HBM_BASE_ADDR_LO  0x00001000  /* Small offset into HBM */

enum dma_operation { DMA_WRITE, DMA_READ }; /* WRITE is H2C; READ is C2H and verifies what it reads */

struct memory {
  uint64_t base;
  size_t size;
};

static const struct memory ddr = {.base = 0, .size = DDR_SIZE};
static const struct memory hbm = {.base = DDR_SIZE, .size = HBM_SIZE};

struct dma_resources {
  uint8_t* arena;
  int h2c_fd;
  int c2h_fd;
};

struct chunk_result {
  int rc;
  double dma_seconds;
};

/* Static function definitions */

static double get_time_seconds(void) {
  struct timespec ts;
  clock_gettime(CLOCK_MONOTONIC, &ts);
  return ts.tv_sec + ts.tv_nsec / 1e9;
}

static int poll_register_bit(pci_bar_handle_t pci_bar_handle, uint32_t offset, uint32_t mask, uint32_t value,
                             int timeout) {
  int rc = FPGA_ERR_OK;
  fail_on_with_code(timeout <= 0, out, rc, FPGA_ERR_SOFTWARE_PROBLEM, "Invalid timeout value: %d (must be > 0)", timeout);

  uint32_t read_data;

  while (timeout > 0) {
    rc = fpga_pci_peek(pci_bar_handle, offset, &read_data);
    fail_on(rc, out, "fpga_pci_peek failed at offset 0x%x", offset);
    if ((read_data & mask) == value) {
      return FPGA_ERR_OK;  // Success - masked bit(s) match expected value
    }
    timeout--;
  }
  return FPGA_ERR_UNRESPONSIVE;  // Timeout

out:
  return FPGA_ERR_SOFTWARE_PROBLEM;
}

/* Every chunk carries the same pattern; the 8-byte address stamp is what tells
 * one chunk from another. */
static bool stamp_matches(const uint8_t* buffer, uint64_t address) {
  uint64_t stamp;
  memcpy(&stamp, buffer, STAMP_SIZE);
  return stamp == address;
}

static bool body_matches(const uint8_t* buffer, const uint8_t* pattern, size_t length) {
  return memcmp(buffer + STAMP_SIZE, pattern + STAMP_SIZE, length - STAMP_SIZE) == 0;
}

static uint64_t verify_chunk(uint8_t* buffer, uint8_t* pattern, size_t length, uint64_t address) {
  bool stamp_valid = stamp_matches(buffer, address);
  bool body_valid = body_matches(buffer, pattern, length);
  if (stamp_valid && body_valid) return 0;

  uint64_t differ = 0;
  if (!stamp_valid) {
    log_error("Stamp mismatch for chunk at 0x%" PRIx64, address);
    differ += buffer_compare((uint8_t*)&address, buffer, STAMP_SIZE);
  }
  if (!body_valid) {
    log_error("Data mismatch in chunk at 0x%" PRIx64 " (%zu bytes); positions below are relative to 0x%" PRIx64,
              address, length, address + STAMP_SIZE);
    differ += buffer_compare(pattern + STAMP_SIZE, buffer + STAMP_SIZE, length - STAMP_SIZE);
  }
  return differ;
}

static const char* failure_hint(int rc) { return rc == -ENOMEM ? ENOMEM_HINT : ""; }

static struct chunk_result write_chunk(const struct dma_resources* resources, uint64_t address, size_t length) {
  double start = get_time_seconds();
  memcpy(resources->arena, &address, STAMP_SIZE);
  int rc = fpga_dma_burst_write(resources->h2c_fd, resources->arena, length, address);
  return (struct chunk_result){.rc = rc, .dma_seconds = get_time_seconds() - start};
}

/* Only the DMA call is timed, so the rate excludes the buffer clearing and comparison. */
static struct chunk_result read_chunk(const struct dma_resources* resources, uint64_t address, size_t length) {
  uint8_t* pattern = resources->arena;
  uint8_t* buffer = resources->arena + CHUNK_SIZE;

  /* Clear first so a read that fills only part of the chunk cannot pass on the previous chunk's tail. Every chunk
   * carries the same pattern, so only the stamp tells chunks apart. */
  memset(buffer, 0, length);
  double start = get_time_seconds();
  int rc = fpga_dma_burst_read(resources->c2h_fd, buffer, length, address);
  double dma_seconds = get_time_seconds() - start;
  if (!rc && verify_chunk(buffer, pattern, length, address)) rc = FPGA_ERR_FAIL;
  return (struct chunk_result){.rc = rc, .dma_seconds = dma_seconds};
}

static struct chunk_result transfer_chunk(enum dma_operation operation, const struct dma_resources* resources,
                                          uint64_t address, size_t length) {
  struct chunk_result result = {.rc = FPGA_ERR_OK, .dma_seconds = 0};
  fail_on_with_code(!resources || !resources->arena, out, result.rc, FPGA_ERR_SOFTWARE_PROBLEM,
                    "No DMA buffers to transfer with");
  /* A chunk holds the stamp plus at least one byte of body, and must fit the buffers. */
  fail_on_with_code(length <= STAMP_SIZE || length > CHUNK_SIZE, out, result.rc, FPGA_ERR_SOFTWARE_PROBLEM,
                    "Invalid chunk length %zu: must be above %zu and at most %zu bytes", length, STAMP_SIZE,
                    CHUNK_SIZE);

  result = operation == DMA_WRITE ? write_chunk(resources, address, length) : read_chunk(resources, address, length);

out:
  return result;
}

static int run_phase(const char* name, enum dma_operation operation, const struct dma_resources* resources,
                     const struct memory* memory) {
  int rc = FPGA_ERR_OK;
  double dma_seconds = 0;

  for (size_t offset = 0; offset < memory->size; offset += CHUNK_SIZE) {
    uint64_t address = memory->base + offset;
    size_t length = min(CHUNK_SIZE, memory->size - offset);
    struct chunk_result result = transfer_chunk(operation, resources, address, length);
    rc = result.rc;
    fail_on(rc, out, "%s: %zu bytes at 0x%" PRIx64 " failed (rc=%d)%s", name, length, address, rc, failure_hint(rc));
    dma_seconds += result.dma_seconds;
  }

  double gib = (double)memory->size / GIB(1);
  log_info("%s: %s %.2f GiB in %.2f s = %.2f GiB/s", name, operation == DMA_WRITE ? "H2C" : "C2H", gib, dma_seconds,
           gib / dma_seconds);

out:
  return rc;
}

int dma_example(int slot_id) {
  int rc = FPGA_ERR_OK;
  struct dma_resources resources = {.arena = NULL, .h2c_fd = -1, .c2h_fd = -1};
  uint64_t arena_address = 0;
  uint64_t arena_physical_address;  /* the SDK helper requires it; XDMA does not use it */

  log_info("Testing %zu GiB of DDR then %zu GiB of HBM on XDMA channel 0, %zu MiB chunks", ddr.size / GIB(1),
           hbm.size / GIB(1), CHUNK_SIZE >> 20);

  rc = fpga_dma_mem_map_anon(ARENA_SIZE, &arena_address, &arena_physical_address);
  fail_on(rc, out, "Unable to map %zu bytes of DMA buffers", ARENA_SIZE);
  resources.arena = (uint8_t*)arena_address;
  rc = fill_buffer_urandom(resources.arena, CHUNK_SIZE);
  fail_on(rc, out, "Unable to fill the pattern buffer");

  resources.h2c_fd = fpga_dma_open_queue(FPGA_DMA_XDMA, slot_id, 0, false);
  fail_on_with_code(resources.h2c_fd < 0, out, rc, FPGA_ERR_FAIL, "Unable to open H2C queue 0");
  resources.c2h_fd = fpga_dma_open_queue(FPGA_DMA_XDMA, slot_id, 0, true);
  fail_on_with_code(resources.c2h_fd < 0, out, rc, FPGA_ERR_FAIL, "Unable to open C2H queue 0");

  rc = run_phase("DDR write", DMA_WRITE, &resources, &ddr);
  fail_on(rc, out, "DDR write failed");
  rc = run_phase("HBM write", DMA_WRITE, &resources, &hbm);
  fail_on(rc, out, "HBM write failed");
  rc = run_phase("DDR read", DMA_READ, &resources, &ddr);
  fail_on(rc, out, "DDR read failed");
  rc = run_phase("HBM read", DMA_READ, &resources, &hbm);
  fail_on(rc, out, "HBM read failed");

out:
  if (resources.h2c_fd >= 0) close(resources.h2c_fd);
  if (resources.c2h_fd >= 0) close(resources.c2h_fd);
  /* A failed mapping is already unmapped by the SDK, but it leaves arena_address set. */
  if (resources.arena) fpga_dma_mem_unmap(&arena_address, ARENA_SIZE);
  return rc;
}

void usage(const char* program_name) { printf("usage: %s [--slot <slot>]\n", program_name); }

static int parse_arguments(int argc, char** argv, test_parameters_t* params) {
  for (int i = 1; i < argc; ++i) {
    if (strcmp(argv[i], "--slot") != 0 || ++i >= argc) {
      goto invalid;
    }

    char* end;
    errno = 0;
    unsigned long long value = strtoull(argv[i], &end, 10);
    if (errno || end == argv[i] || *end || argv[i][0] < '0' || argv[i][0] > '9' || value >= FPGA_SLOT_MAX) {
      goto invalid;
    }
    params->slot_id = value;
  }
  return 0;

invalid:
  usage(argv[0]);
  return 1;
}

int main(int argc, char** argv) {
  test_parameters_t params = {.slot_id = 0};
  int rc = parse_arguments(argc, argv, &params);
  if (rc) return rc;
  const int slot_id = params.slot_id;

  /* setup logging to print to stdout */
  rc = log_init("test_dram_hbm_dma");
  fail_on(rc, out, "Unable to initialize the log.");
  rc = log_attach(logger, NULL, 0);
  fail_on(rc, out, "%s", "Unable to attach to the log.");

  log_info("Testing FPGA slot %u", slot_id);

  /* initialize the fpga_plat library */
  rc = fpga_mgmt_init();
  fail_on(rc, out, "Unable to initialize the fpga_mgmt library");

  rc = deassert_clk_resets(slot_id);
  fail_on(rc, out, "Failed to deassert clock resets");

  /* run the dma test example */
  rc = dma_example(slot_id);
  fail_on(rc, out, "DMA example failed on slot %u", slot_id);

  /* run axi master example */
  rc = axi_mstr_example(slot_id);
  fail_on(rc, out, "AXI Master example failed");

  /* Test all 16 MSI-X interrupts */
  log_info("Starting interrupt tests for all %d interrupts", USER_INTERRUPTS_MAX);
  for (int i = 0; i < USER_INTERRUPTS_MAX; i++) {
    rc = interrupt_example(slot_id, i);
    fail_on(rc, out, "Interrupt example %d failed", i);
  }
  log_info("All %d interrupt tests passed", USER_INTERRUPTS_MAX);

out:
  log_info("Slot %u: TEST %s", slot_id, (rc == 0) ? "PASSED" : "FAILED");
  return rc;
}

int interrupt_example(int slot_id, int interrupt_number) {
  int rc = FPGA_ERR_OK;
  int fd = -1, rd;
  pci_bar_handle_t pci_bar_handle = PCI_BAR_HANDLE_INIT;
  fail_on_with_code(interrupt_number < 0 || interrupt_number >= USER_INTERRUPTS_MAX, out, rc, FPGA_ERR_SOFTWARE_PROBLEM, "Invalid interrupt_number: %d (must be 0-%d)", interrupt_number, USER_INTERRUPTS_MAX - 1);
  struct pollfd fds[1];
  uint32_t read_data;
  char event_file_name[256];
  int poll_timeout = 1000;
  int num_fds = 1;
  int pf_id = 0;
  int bar_id = 0;
  int fpga_attach_flags = 0;
  int poll_limit = 20;
  uint32_t interrupt_reg_offset = 0xd00;

  int device_num = 0;
  rc = fpga_pci_get_dma_device_num(FPGA_DMA_XDMA, slot_id, &device_num);
  fail_on((rc = (rc != 0) ? 1 : 0), out, "Unable to get xdma device number.");

  rc = sprintf(event_file_name, "/dev/xdma%i_events_%i", device_num, interrupt_number);
  fail_on((rc = (rc < 0) ? 1 : 0), out, "Unable to format event file name.");

  log_info("Starting MSI-X Interrupt test");
  rc = fpga_pci_attach(slot_id, pf_id, bar_id, fpga_attach_flags, &pci_bar_handle);
  fail_on(rc, out, "Unable to attach to the AFI on slot id %d", slot_id);

  log_info("Polling device file: %s for interrupt events", event_file_name);
  if ((fd = open(event_file_name, O_RDONLY)) == -1) {
    log_error("Error - invalid device\n");
    fail_on((rc = FPGA_ERR_FAIL), out, "Unable to open event device");
  }
  fds[0].fd = fd;
  fds[0].events = POLLIN;

  log_info("Triggering MSI-X Interrupt %d", interrupt_number);
  rc = fpga_pci_poke(pci_bar_handle, interrupt_reg_offset, 1 << interrupt_number);
  fail_on(rc, out, "Unable to write to the fpga !");

  // Poll checks whether an interrupt was generated.
  rd = poll(fds, num_fds, poll_timeout);
  if ((rd > 0) && (fds[0].revents & POLLIN)) {
    uint32_t events_user;

    // Check how many interrupts were generated, and clear the interrupt so we
    // can detect future interrupts.
    rc = pread(fd, &events_user, sizeof(events_user), 0);
    fail_on((rc = (rc < 0) ? 1 : 0), out, "call to pread failed.");

    log_info("Interrupt present for Interrupt %i, events %i. It worked!", interrupt_number, events_user);

    // Clear the interrupt register
    rc = fpga_pci_poke(pci_bar_handle, interrupt_reg_offset, 0x1 << (16 + interrupt_number));
    fail_on(rc, out, "Unable to write to the fpga !");
  } else {
    log_error("No interrupt generated- something went wrong.");
    fail_on((rc = FPGA_ERR_FAIL), out, "Interrupt generation failed");
  }
  close(fd);
  fd = -1;

  // Clear the interrupt register
  do {
    // In this CL, a successful interrupt is indicated by the CL setting bit
    // <interrupt_number + 16> of the interrupt register. Here we check that bit
    // is set and write 1 to it to clear.
    rc = fpga_pci_peek(pci_bar_handle, interrupt_reg_offset, &read_data);
    fail_on(rc, out, "Unable to read from the fpga !");
    read_data = read_data & (1 << (interrupt_number + 16));

    rc = fpga_pci_poke(pci_bar_handle, interrupt_reg_offset, read_data);
    fail_on(rc, out, "Unable to write to the fpga !");

    poll_limit--;
  } while (!read_data && poll_limit > 0);

out:
  if (fd >= 0) {
    close(fd);
  }
  if (pci_bar_handle != PCI_BAR_HANDLE_INIT) {
    fpga_pci_detach(pci_bar_handle);
  }
  return rc;
}

int axi_mstr_example(int slot_id) {
  int rc;
  pci_bar_handle_t pci_bar_handle = PCI_BAR_HANDLE_INIT;
  int pf_id = 0;
  int bar_id = 0;
  int fpga_attach_flags = 0;
  uint32_t axi_mstr_test_addr_upper, axi_mstr_test_addr_lower, axi_mstr_test_data;

  rc = fpga_pci_attach(slot_id, pf_id, bar_id, fpga_attach_flags, &pci_bar_handle);
  fail_on(rc, out, "Unable to attach to the AFI on slot id %d", slot_id);

  log_info("Starting AXI Master to ADDR test");

  /* DDR Access - DDR is at base address 0x00_0000_0000, 64GB range */
  axi_mstr_test_addr_upper = DDR_BASE_ADDR_HI;
  axi_mstr_test_addr_lower = DDR_BASE_ADDR_LO;
  axi_mstr_test_data = 0xBEEFCAFE;

  rc = axi_mstr_addr_access(slot_id, pci_bar_handle, axi_mstr_test_addr_upper, axi_mstr_test_addr_lower, axi_mstr_test_data);
  fail_on(rc, out, "Unable to access DDR");

  /* HBM Access - HBM is at base address 0x10_0000_0000, 16GB range */
  axi_mstr_test_addr_upper = HBM_BASE_ADDR_HI;
  axi_mstr_test_addr_lower = HBM_BASE_ADDR_LO;
  axi_mstr_test_data = 0xBEEFCAFE;

  rc = axi_mstr_addr_access(slot_id, pci_bar_handle, axi_mstr_test_addr_upper, axi_mstr_test_addr_lower, axi_mstr_test_data);
  fail_on(rc, out, "Unable to access HBM");

out:
  return rc;
}

/* Helper function for accessing DDR controllers via AXI Master block */
int axi_mstr_addr_access(int slot_id, pci_bar_handle_t pci_bar_handle, uint32_t axi_mstr_test_addr_upper, uint32_t axi_mstr_test_addr_lower,
                         uint32_t axi_mstr_test_data) {
  int rc;
  uint32_t read_data;

  (void)slot_id;  // unused but kept for API consistency

  /* Issue AXI Master Write Command */
  rc = fpga_pci_poke(pci_bar_handle, AXI_MSTR_CAHR_OFFSET, axi_mstr_test_addr_upper);
  fail_on(rc, out, "Unable to write to AXI Master CAHR register!");
  rc = fpga_pci_poke(pci_bar_handle, AXI_MSTR_CALR_OFFSET, axi_mstr_test_addr_lower);
  fail_on(rc, out, "Unable to write to AXI Master CALR register!");
  rc = fpga_pci_poke(pci_bar_handle, AXI_MSTR_CWDR_OFFSET, axi_mstr_test_data);
  fail_on(rc, out, "Unable to write to AXI Master CWDR register!");
  rc = fpga_pci_poke(pci_bar_handle, AXI_MSTR_CCR_OFFSET, 0x1);
  fail_on(rc, out, "Unable to write to AXI Master CCR register!");

  /* Poll for write done */
  rc = poll_register_bit(pci_bar_handle, AXI_MSTR_CCR_OFFSET, 0x2, 0x2, 20);
  fail_on(rc, out, "AXI Master write did not complete. Done bit not set in CCR.");

  /* Issue AXI Master Read Command */
  rc = fpga_pci_poke(pci_bar_handle, AXI_MSTR_CCR_OFFSET, 0x5);
  fail_on(rc, out, "Unable to write to AXI Master CCR register!");

  /* Poll for read done */
  rc = poll_register_bit(pci_bar_handle, AXI_MSTR_CCR_OFFSET, 0x2, 0x2, 20);
  fail_on(rc, out, "AXI Master read did not complete. Done bit not set in CCR.");

  /* Compare Read/Write Data */
  rc = fpga_pci_peek(pci_bar_handle, AXI_MSTR_CRDR_OFFSET, &read_data);
  fail_on(rc, out, "Unable to read AXI Master CRDR from the fpga !");

  if (read_data == axi_mstr_test_data) {
    log_info("Resulting value at address 0x%02x%08x matched expected value 0x%08x. It worked!", axi_mstr_test_addr_upper, axi_mstr_test_addr_lower,
             axi_mstr_test_data);
    rc = FPGA_ERR_OK;
  } else {
    log_error("Resulting value 0x%08x did not match expected value 0x%08x at address 0x%02x%08x", read_data, axi_mstr_test_data,
              axi_mstr_test_addr_upper, axi_mstr_test_addr_lower);
    rc = FPGA_ERR_FAIL;
  }

out:
  return rc;
}
