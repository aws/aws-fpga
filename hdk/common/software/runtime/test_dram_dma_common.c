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

#include <errno.h>
#include <fcntl.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/random.h>
#include <sys/stat.h>
#include <sys/types.h>
#include <unistd.h>
#include <utils/sh_dpi_tasks.h>

#include <hal/fpga_common.h>
#include <utils/lcd.h>

#if !defined(SV_TEST)
#include <fpga_clkgen.h>
#include <fpga_mgmt.h>
#include <fpga_pci.h>
#endif

#include "test_dram_dma_common.h"

#if !defined(SV_TEST)
static const uint16_t AMZ_PCI_VENDOR_ID = 0x1D0F; /* Amazon PCI Vendor ID */
static const uint16_t PCI_DEVICE_ID = 0xF001;
#endif

int fill_buffer_urandom(uint8_t *buf, size_t size) {
  int rc = FPGA_ERR_OK;
  fail_on_with_code(!buf, out, rc, FPGA_ERR_SOFTWARE_PROBLEM, "Null buffer supplied to fill_buffer_urandom()");
  fail_on_with_code(!size, out, rc, FPGA_ERR_SOFTWARE_PROBLEM, "Zero-size buffer supplied to fill_buffer_urandom()");

  size_t filled = 0;
  while (filled < size) {
    ssize_t got = getrandom(buf + filled, size - filled, 0);
    if (got < 0 && errno == EINTR) {
      continue;
    }
    fail_on_with_code(got < 0, out, rc, FPGA_ERR_SOFTWARE_PROBLEM, "getrandom() failed: %s", strerror(errno));
    filled += (size_t)got;
  }

out:
  return rc;
}

int dump_buffer(const char *prefix, uint8_t *buffer, size_t size, size_t offset) {
  int rc = FPGA_ERR_OK;
  fail_on_with_code(!prefix, out, rc, FPGA_ERR_SOFTWARE_PROBLEM, "Null prefix cannot be used in buffer data dump");
  fail_on_with_code(!buffer, out, rc, FPGA_ERR_SOFTWARE_PROBLEM, "Null buffer cannot be data dumped");
  fail_on_with_code(!size, out, rc, FPGA_ERR_SOFTWARE_PROBLEM, "Zero-size buffer can't be data dumped");
  fail_on_with_code(offset >= size, out, rc, FPGA_ERR_SOFTWARE_PROBLEM, "Offset is out of bounds of buffer to be data dumped");

  printf("%s (offset %zu): ", prefix, offset);
  for (size_t i = offset; i < offset + 32 && i < size; i++) {
    printf("%02x ", buffer[i]);
  }
  printf("\n");

out:
  return rc;
}

uint64_t buffer_compare(uint8_t *bufa, uint8_t *bufb, size_t buffer_size) {
  uint64_t differ = 0;
  int rc = FPGA_ERR_OK;
  fail_on_with_code(!bufa, out, rc, FPGA_ERR_SOFTWARE_PROBLEM, "NULL bufa buffer detected in comparison");
  fail_on_with_code(!bufb, out, rc, FPGA_ERR_SOFTWARE_PROBLEM, "NULL bufb buffer detected in comparison");
  fail_on_with_code(!buffer_size, out, rc, FPGA_ERR_SOFTWARE_PROBLEM, "Zero-size buffers have nothing to compare");

  size_t first_diff_pos = 0;
  bool first_diff_found = false;
  for (size_t i = 0; i < buffer_size; i++) {
    if (bufa[i] != bufb[i]) {
      differ++;
      if (!first_diff_found) {
        first_diff_pos = i;
        first_diff_found = true;

        printf("ERROR: First difference found at position %zu\n", first_diff_pos);
        printf("ERROR: Expected vs Actual at diff point: 0x%02x vs 0x%02x\n", bufa[i], bufb[i]);

        dump_buffer("Expected data", bufa, buffer_size, (first_diff_pos > 16) ? first_diff_pos - 16 : 0);
        dump_buffer("Actual data", bufb, buffer_size, (first_diff_pos > 16) ? first_diff_pos - 16 : 0);
      }
      if (differ % 1000000 == 0) {
        printf("INFO: Found %lu differences so far...\n", differ);
      }
    }
  }

  if (differ > 0) {
    printf("ERROR: Total number of differences: %lu (%0.2f%%)\n", differ, (float)differ * 100.0 / buffer_size);
  }
out:
  return rc ? buffer_size : differ;
}

#if !defined(SV_TEST)
int check_slot_config(int slot_id) {
  struct fpga_mgmt_image_info info = {0};

  /* get local image description, contains status, vendor id, and device id */
  int rc = fpga_mgmt_describe_local_image(slot_id, &info, 0);
  fail_on(rc, out, "Can't fetch AFI information. Are you running as root?");

  /* check to see if the slot is ready */
  rc = info.status != FPGA_STATUS_LOADED;
  fail_on(rc, out, "Slot %d is not ready", slot_id);

  /* confirm that the AFI that we expect is in fact loaded */
  if (info.spec.map[FPGA_APP_PF].vendor_id != AMZ_PCI_VENDOR_ID ||
      info.spec.map[FPGA_APP_PF].device_id != PCI_DEVICE_ID) {
    rc = FPGA_ERR_CL_ID_MISMATCH;
    char sdk_path_buf[512];
    char *sdk_env_var;
    sdk_env_var = getenv("SDK_DIR");
    snprintf(sdk_path_buf, sizeof(sdk_path_buf), "%s", (sdk_env_var != NULL) ? sdk_env_var : "<aws-fpga>");
    log_error(
        "...\n"
        "  The slot appears loaded, but the pci vendor or device ID doesn't match the\n"
        "  expected values. You may need to rescan the fpga with \n"
        "    fpga-describe-local-image -S %i -R\n"
        "  Note that rescanning can change which device file in /dev/ a FPGA will map to.\n",
        slot_id);
    log_error(
        "...\n"
        "  To remove and re-add your xdma driver and reset the device file mappings, run\n"
        "    sudo rmmod xdma && sudo insmod \"%s/sdk/linux_kernel_drivers/xdma/xdma.ko\"\n",
        sdk_path_buf);
    fail_on(rc, out,
            "The PCI vendor id and device of the loaded image are "
            "not the expected values.");
  }

  char dbdf[16];
  snprintf(dbdf, sizeof(dbdf), PCI_DEV_FMT, info.spec.map[FPGA_APP_PF].domain, info.spec.map[FPGA_APP_PF].bus,
           info.spec.map[FPGA_APP_PF].dev, info.spec.map[FPGA_APP_PF].func);
  log_info("Operating on slot %d with id: %s", slot_id, dbdf);

out:
  return rc;
}

int deassert_clk_resets(int slot_id) {
  printf("__INFO__: deassert_clk_resets()\n");

  /* aws_clkgen_deassert_resets() probes for the IP itself via
   * aws_clkgen_check_id(), so designs without aws_clk_gen are detected from
   * the return code rather than from a hard-coded CL device ID. */
  int rc = aws_clkgen_deassert_resets(slot_id);
  if (rc == FPGA_ERR_CLKGEN_NOT_FOUND) {
    printf("__INFO__: This design does not include aws_clk_gen - skipping clock reset\n");
    rc = FPGA_ERR_OK;
    goto out;
  }
  fail_on(rc, out, "Failed to deassert clock resets");

out:
  return rc;
}
#else
/* Unused link-time stub. No testbench calls send_rdbuf_to_c; it moves no data
 * and exists only so the import "DPI-C" ... send_rdbuf_to_c in
 * hdk/common/verif/include/sh_dpi_tasks.svh resolves at elaboration. */
int send_rdbuf_to_c(char *rd_buf) {
  (void)rd_buf;
  return 0;
}
#endif
