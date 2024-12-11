/*
 * Amazon FPGA Hardware Development Kit
 *
 * Copyright 2018 Amazon.com, Inc. or its affiliates. All Rights Reserved.
 *
 * Licensed under the Amazon Software License (the "License"). You may not use
 * this file except in compliance with the License. A copy of the License is
 * located at
 *
 *    http://aws.amazon.com/asl/
 *
 * or in the "license" file accompanying this file. This file is distributed on
 * an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, express or
 * implied. See the License for the specific language governing permissions and
 * limitations under the License.
 */
//--------------------------------------------------------------------------------------
// Measure HBM performance by enabling all the 32 channels in HBM
// NOTE: Works only on cl_dram_hbm_dma bitstreams
//--------------------------------------------------------------------------------------

#include <stdio.h>
#include <fcntl.h>
#include <errno.h>
#include <string.h>
#include <stdlib.h>
#include <unistd.h>
#include <poll.h>

#include "fpga_pci.h"
#include "fpga_mgmt.h"
#include "fpga_dma.h"
#include "utils/lcd.h"

#include "test_dram_dma_common.h"

#define	MEM_16G              (1ULL << 34)
#define USER_INTERRUPTS_MAX  (16)
#define MAX_LOOP_COUNT       (1000000)

/* use the standard out logger */
static const struct logger *logger = &logger_stdout;

// Function declarations
void usage(const char* program_name);
int initialize_hbm(int slot_id);
int enable_hbm_kernl(int slot_id, uint32_t value);
int run_hbm_write_test(int slot_id, uint32_t cfg_axlen, uint32_t cfg_wdata, uint32_t cfg_wr_ctl, int cfg_runtime);
int run_hbm_read_test(int slot_id, uint32_t cfg_axlen, uint32_t cfg_rd_ctl, int cfg_runtime);
int display_results(int slot_id, uint32_t cfg_axlen, uint32_t cfg_wr_ctl, uint32_t cfg_rd_ctl);
int calculate_perf(int slot_id, uint64_t base_addr, uint32_t cfg_axlen, char prefix[]);

//
// HBM Kernel Register Address
//
#define OCL_OFFSET         ((uint64_t) 0x400)
#define KERN_CFG_REG       ((uint64_t) (OCL_OFFSET + 0x00))
#define CHANNEL_AVAIL_REG  ((uint64_t) (OCL_OFFSET + 0x04))
#define NUM_OT_REG         ((uint64_t) (OCL_OFFSET + 0x08))
#define CHNL_SEL_REG       ((uint64_t) (OCL_OFFSET + 0x0C))
#define AXLEN_REG          ((uint64_t) (OCL_OFFSET + 0x10))
#define WDATA_PATTERN_REG  ((uint64_t) (OCL_OFFSET + 0x14))
#define WR_CTL_REG         ((uint64_t) (OCL_OFFSET + 0x18))
#define RD_CTL_REG         ((uint64_t) (OCL_OFFSET + 0x1C))
#define WR_CYC_CNT_LO_REG  ((uint64_t) (OCL_OFFSET + 0x30))
#define WR_CYC_CNT_HI_REG  ((uint64_t) (OCL_OFFSET + 0x34))
#define WR_TIMER_LO_REG    ((uint64_t) (OCL_OFFSET + 0x38))
#define WR_TIMER_HI_REG    ((uint64_t) (OCL_OFFSET + 0x3c))
#define WR_LATENCY_REG     ((uint64_t) (OCL_OFFSET + 0x40))
#define WR_OT_REG          ((uint64_t) (OCL_OFFSET + 0x44))
#define BRESP_ERR_REG      ((uint64_t) (OCL_OFFSET + 0x48))
#define RD_CYC_CNT_LO_REG  ((uint64_t) (OCL_OFFSET + 0x50))
#define RD_CYC_CNT_HI_REG  ((uint64_t) (OCL_OFFSET + 0x54))
#define RD_TIMER_LO_REG    ((uint64_t) (OCL_OFFSET + 0x58))
#define RD_TIMER_HI_REG    ((uint64_t) (OCL_OFFSET + 0x5C))
#define RD_LATENCY_REG     ((uint64_t) (OCL_OFFSET + 0x60))
#define RD_OT_REG          ((uint64_t) (OCL_OFFSET + 0x64))
#define RRESP_ERR_REG      ((uint64_t) (OCL_OFFSET + 0x68))


//=================================================================
//
// MAIN
//
//=================================================================
int main(int argc, char **argv) {
    int rc;
    int slot_id = 0;
    uint32_t cfg_axlen  = 0xF;
    uint32_t cfg_wdata  = 0x12345678;
    uint32_t cfg_wr_ctl = 0xFFFFFFFF;
    uint32_t cfg_rd_ctl = 0xFFFFFFFF;
    uint32_t cfg_runtime = 30;

    switch (argc) {
    case 1:
        break;
    case 3:
        sscanf(argv[2], "%x", &slot_id);
        break;
    default:
        usage(argv[0]);
        return 1;
    }

    // setup logging to print to stdout
    rc = log_init("test_hbm_perf32");
    fail_on(rc, out, "Unable to initialize the log.");
    rc = log_attach(logger, NULL, 0);
    fail_on(rc, out, "%s", "Unable to attach to the log.");

    // initialize the fpga_plat library
    rc = fpga_mgmt_init();
    fail_on(rc, out, "Unable to initialize the fpga_mgmt library");

    //
    // Display Test Variables
    //
    printf("===================================================\n");
    printf("Running test_hbm_perf32 \n");
    printf("===================================================\n");
    printf("slot_id     = %d\n", slot_id);
    printf("cfg_axlen   = 0x%08x\n", cfg_axlen );
    printf("cfg_wdata   = 0x%08x\n", cfg_wdata );
    printf("cfg_wr_ctl  = 0x%08x\n", cfg_wr_ctl);
    printf("cfg_rd_ctl  = 0x%08x\n", cfg_rd_ctl);
    printf("cfg_runtime = 0x%08x\n", cfg_runtime);
    printf("===================================================\n");

    //=============================================================
    // Run the test
    //=============================================================
    rc = deassert_clk_resets(slot_id);
    fail_on(rc, out, "Failed deassert_clk_resets()");

    rc = initialize_hbm(slot_id);
    fail_on(rc, out, "Failed initialize_hbm()");

    rc = enable_hbm_kernl(slot_id, 1);
    fail_on(rc, out, "Failed enable_hbm_kernl()");

    rc = run_hbm_write_test(slot_id, cfg_axlen, cfg_wdata, cfg_wr_ctl, cfg_runtime);
    fail_on(rc, out, "Failed run_hbm_write_test()");

    rc = run_hbm_read_test(slot_id, cfg_axlen, cfg_rd_ctl, cfg_runtime);
    fail_on(rc, out, "Failed run_hbm_read_test()");

    rc = enable_hbm_kernl(slot_id, 0);
    fail_on(rc, out, "Failed enable_hbm_kernl()");

    rc = display_results(slot_id, cfg_axlen, cfg_wr_ctl, cfg_rd_ctl);
    fail_on(rc, out, "Failed display_results()");

out:
    log_info("TEST %s", (rc == 0) ? "PASSED" : "FAILED");
    return rc;
}

//=============================================================
//
// usage()
//
//=============================================================
void usage(const char* program_name) {
    printf("usage: %s [--slot <slot>]\n", program_name);
}


//=============================================================
//
// initialize_hbm()
//
//=============================================================
int initialize_hbm(int slot_id) {
    int rc;
    pci_bar_handle_t pci_bar_handle = PCI_BAR_HANDLE_INIT;
    int fpga_attach_flags = 0;
    int loop_count = 0;
    uint32_t wdata = 0;
    uint32_t read_data = 0;
    uint32_t expected_init_val = 0x6;

    // HBM Config space is on PF0-BAR0
    int pf_id  = 0;
    int bar_id = 0;

    // HBM Reset/Init register
    uint64_t init_reg = 0x300;

    printf("__INFO__: initialize_hbm()\n");
    rc = fpga_pci_attach(slot_id, pf_id, bar_id, fpga_attach_flags, &pci_bar_handle);
    fail_on(rc, out, "Unable to attach to the AFI on slot id %d", slot_id);

    rc = fpga_pci_peek(pci_bar_handle, init_reg, &read_data);
    fail_on(rc, out, "Failed to read from register @0x%08x", (uint32_t) init_reg);

    if (read_data != expected_init_val) {
      printf("__INFO__: HBM is uninitialized. Initializing now...\n");
      wdata = 0x1;
      rc = fpga_pci_poke(pci_bar_handle, init_reg, wdata);
      fail_on(rc, out, "Failed to write to register @ 0x%08x, value = 0x%08x", (uint32_t) init_reg, wdata);

      wdata = 0x0;
      rc = fpga_pci_poke(pci_bar_handle, init_reg, wdata);
      fail_on(rc, out, "Failed to write to register @ 0x%08x, value = 0x%08x", (uint32_t) init_reg, wdata);

      // Now Wait for MMCM lock
      loop_count = 0;
      do {
        rc = fpga_pci_peek(pci_bar_handle, init_reg, &read_data);
        fail_on(rc, out, "Failed to read from register @0x%08x", (uint32_t) init_reg);
        loop_count++;
      } while ((read_data != expected_init_val) && (loop_count < MAX_LOOP_COUNT));

      if (loop_count >= MAX_LOOP_COUNT) {
        rc = 1;
        fail_on(rc, out, "Timeout: Failed to achieve HBM Init after %d iterations", loop_count);
      }
    }

out:
    return rc;
}


//=============================================================
//
// enable_hbm_kernl(slot_id, 1);
//
//=============================================================
int enable_hbm_kernl(int slot_id, uint32_t value) {
    int rc;
    pci_bar_handle_t pci_bar_handle = PCI_BAR_HANDLE_INIT;
    int fpga_attach_flags = 0;
    uint32_t wdata = 0;

    // HBM Kernel is on PF0-BAR0, offset = 0x400
    int      pf_id  = 0;
    int      bar_id = 0;

    printf("__INFO__: enable_hbm_kernl()\n");
    rc = fpga_pci_attach(slot_id, pf_id, bar_id, fpga_attach_flags, &pci_bar_handle);
    fail_on(rc, out, "Unable to attach to the AFI on slot id %d", slot_id);

    // Write to Kernel Cfg Reg
    wdata = value;
    rc = fpga_pci_poke(pci_bar_handle, KERN_CFG_REG, wdata);
    fail_on(rc, out, "Failed to write to register @ 0x%08x, value = 0x%08x", (uint32_t) KERN_CFG_REG, wdata);

 out:
    return rc;
}


//=============================================================
//
// run_hbm_write_test()
//
//=============================================================
int run_hbm_write_test(int slot_id, uint32_t cfg_axlen, uint32_t cfg_wdata, uint32_t cfg_wr_ctl, int cfg_runtime) {
    int rc;
    pci_bar_handle_t pci_bar_handle = PCI_BAR_HANDLE_INIT;
    int fpga_attach_flags = 0;
    int loop_count = 0;
    uint32_t wdata = 0;
    uint32_t read_data = 0;
    uint64_t addr = 0;

    // PF-BAR to use
    int pf_id  = 0;
    int bar_id = 0;

    printf("__INFO__: run_hbm_write_test() for %ds\n", cfg_runtime);
    rc = fpga_pci_attach(slot_id, pf_id, bar_id, fpga_attach_flags, &pci_bar_handle);
    fail_on(rc, out, "Unable to attach to the AFI on slot id %d", slot_id);

    // Configure HBM Kernel Regs
    addr  = AXLEN_REG;
    wdata = cfg_axlen;
    rc = fpga_pci_poke(pci_bar_handle, addr, wdata);
    fail_on(rc, out, "Failed to write to register @ 0x%08x, value = 0x%08x", (uint32_t) addr, wdata);

    addr  = WDATA_PATTERN_REG;
    wdata = cfg_wdata;
    rc = fpga_pci_poke(pci_bar_handle, addr, wdata);
    fail_on(rc, out, "Failed to write to register @ 0x%08x, value = 0x%08x", (uint32_t) addr, wdata);

    addr  = WR_CYC_CNT_LO_REG;
    wdata = 0x0;
    rc = fpga_pci_poke(pci_bar_handle, addr, wdata);
    fail_on(rc, out, "Failed to write to register @ 0x%08x, value = 0x%08x", (uint32_t) addr, wdata);

    addr  = WR_TIMER_LO_REG;
    wdata = 0x0;
    rc = fpga_pci_poke(pci_bar_handle, addr, wdata);
    fail_on(rc, out, "Failed to write to register @ 0x%08x, value = 0x%08x", (uint32_t) addr, wdata);

    addr  = WR_LATENCY_REG;
    wdata = 0x0;
    rc = fpga_pci_poke(pci_bar_handle, addr, wdata);
    fail_on(rc, out, "Failed to write to register @ 0x%08x, value = 0x%08x", (uint32_t) addr, wdata);

    addr  = WR_CTL_REG;
    wdata = cfg_wr_ctl;
    rc = fpga_pci_poke(pci_bar_handle, addr, wdata);
    fail_on(rc, out, "Failed to write to register @ 0x%08x, value = 0x%08x", (uint32_t) addr, wdata);

    // Run for a while
    sleep(cfg_runtime);

    // Stop data transfers
    addr  = WR_CTL_REG;
    wdata = 0x0;
    rc = fpga_pci_poke(pci_bar_handle, addr, wdata);
    fail_on(rc, out, "Failed to write to register @ 0x%08x, value = 0x%08x", (uint32_t) addr, wdata);

    // Waiting for all pending txns to complete
    loop_count = 0;

    do {
      addr = WR_OT_REG;
      rc = fpga_pci_peek(pci_bar_handle, addr, &read_data);
      fail_on(rc, out, "Failed to read from register @0x%08x", (uint32_t) addr);
      loop_count++;
    } while ((read_data != 0) && (loop_count < MAX_LOOP_COUNT));

    if (loop_count >= MAX_LOOP_COUNT) {
      rc = 1;
      fail_on(rc, out, "Timeout: waiting for pending write transactions to complete after %d iterations", loop_count);
    }

out:
    return rc;
}


//=============================================================
//
// run_hbm_read_test()
//
//=============================================================
int run_hbm_read_test(int slot_id, uint32_t cfg_axlen, uint32_t cfg_rd_ctl, int cfg_runtime) {
    int rc;
    pci_bar_handle_t pci_bar_handle = PCI_BAR_HANDLE_INIT;
    int fpga_attach_flags = 0;
    int loop_count = 0;
    uint32_t wdata = 0;
    uint32_t read_data = 0;
    uint64_t addr = 0;

    // PF-BAR to use
    int pf_id  = 0;
    int bar_id = 0;

    printf("__INFO__: run_hbm_read_test() for %ds\n", cfg_runtime);
    rc = fpga_pci_attach(slot_id, pf_id, bar_id, fpga_attach_flags, &pci_bar_handle);
    fail_on(rc, out, "Unable to attach to the AFI on slot id %d", slot_id);

    // Configure HBM Kernel Regs
    addr  = AXLEN_REG;
    wdata = cfg_axlen;
    rc = fpga_pci_poke(pci_bar_handle, addr, wdata);
    fail_on(rc, out, "Failed to write to register @ 0x%08x, value = 0x%08x", (uint32_t) addr, wdata);

    addr  = RD_CYC_CNT_LO_REG;
    wdata = 0x0;
    rc = fpga_pci_poke(pci_bar_handle, addr, wdata);
    fail_on(rc, out, "Failed to write to register @ 0x%08x, value = 0x%08x", (uint32_t) addr, wdata);

    addr  = RD_TIMER_LO_REG;
    wdata = 0x0;
    rc = fpga_pci_poke(pci_bar_handle, addr, wdata);
    fail_on(rc, out, "Failed to write to register @ 0x%08x, value = 0x%08x", (uint32_t) addr, wdata);

    addr  = RD_LATENCY_REG;
    wdata = 0x0;
    rc = fpga_pci_poke(pci_bar_handle, addr, wdata);
    fail_on(rc, out, "Failed to write to register @ 0x%08x, value = 0x%08x", (uint32_t) addr, wdata);

    addr  = RD_CTL_REG;
    wdata = cfg_rd_ctl;
    rc = fpga_pci_poke(pci_bar_handle, addr, wdata);
    fail_on(rc, out, "Failed to write to register @ 0x%08x, value = 0x%08x", (uint32_t) addr, wdata);

    // Run for a while
    sleep(cfg_runtime);

    // Stop data transfers
    addr  = RD_CTL_REG;
    wdata = 0x0;
    rc = fpga_pci_poke(pci_bar_handle, addr, wdata);
    fail_on(rc, out, "Failed to write to register @ 0x%08x, value = 0x%08x", (uint32_t) addr, wdata);

    // Waiting for all pending txns to complete
    loop_count = 0;

    do {
      addr = RD_OT_REG;
      rc = fpga_pci_peek(pci_bar_handle, addr, &read_data);
      fail_on(rc, out, "Failed to read from register @0x%08x", (uint32_t) addr);
      loop_count++;
    } while ((read_data != 0) && (loop_count < MAX_LOOP_COUNT));

    if (loop_count >= MAX_LOOP_COUNT) {
      rc = 1;
      fail_on(rc, out, "Timeout: waiting for pending read transactions to complete after %d iterations", loop_count);
    }

out:
    return rc;
}


//=============================================================
//
// display_results()
//
//=============================================================
int display_results(int slot_id, uint32_t cfg_axlen, uint32_t cfg_wr_ctl, uint32_t cfg_rd_ctl) {
    int rc;
    pci_bar_handle_t pci_bar_handle = PCI_BAR_HANDLE_INIT;
    int fpga_attach_flags = 0;

    // PF-BAR to use
    int pf_id  = 0;
    int bar_id = 0;

    printf("__INFO__: display_results()\n");
    rc = fpga_pci_attach(slot_id, pf_id, bar_id, fpga_attach_flags, &pci_bar_handle);
    fail_on(rc, out, "Unable to attach to the AFI on slot id %d", slot_id);

    if (cfg_wr_ctl != 0) {
      printf("__INFO__: -------------------------\n");
      printf("__INFO__: Write Performance Results\n");
      printf("__INFO__: -------------------------\n");
      rc = calculate_perf(slot_id, WR_CYC_CNT_LO_REG, cfg_axlen, "WR");
      fail_on(rc, out, "Failed to compute write performance");
    }

    if (cfg_rd_ctl != 0) {
      printf("__INFO__: -------------------------\n");
      printf("__INFO__: Read Performance Results\n");
      printf("__INFO__: -------------------------\n");
      rc = calculate_perf(slot_id, RD_CYC_CNT_LO_REG, cfg_axlen, "RD");
      fail_on(rc, out, "Failed to compute read performance");
    }

out:
    return rc;
}


//=============================================================
//
// calculate_perf()
//
//=============================================================
int calculate_perf(int slot_id, uint64_t base_addr, uint32_t cfg_axlen, char prefix[]) {
    int rc;
    pci_bar_handle_t pci_bar_handle = PCI_BAR_HANDLE_INIT;
    int fpga_attach_flags = 0;
    uint64_t addr = 0;
    uint64_t offset = 0;
    uint32_t read_data [8];

    // PF-BAR to use
    int pf_id  = 0;
    int bar_id = 0;

    uint64_t cyc_count;
    uint64_t timer;
    int      latency;
    uint32_t ot;
    uint32_t resp_err;
    float    perf;

    printf("__INFO__: calculate_perf()\n");
    rc = fpga_pci_attach(slot_id, pf_id, bar_id, fpga_attach_flags, &pci_bar_handle);
    fail_on(rc, out, "Unable to attach to the AFI on slot id %d", slot_id);

    // read statistic registers from HBM Kernel
    for (offset = 0; offset <= 0x18; offset += 0x4) {
      addr = base_addr + offset;
      rc = fpga_pci_peek(pci_bar_handle, addr, &read_data[offset>>2]);
      fail_on(rc, out, "Failed to read from register @0x%08x", (uint32_t) addr);
    }

    cyc_count = (((uint64_t) read_data[1]) << 32) | ((uint64_t) read_data[0]);
    timer     = (((uint64_t) read_data[3]) << 32) | ((uint64_t) read_data[2]);
    latency   = read_data[4] * 4;
    ot        = read_data[5];
    resp_err  = read_data[6];

    // calculate throughput
    if (timer == 0) {
      perf = 0;
    } else {
      perf = (cyc_count * (cfg_axlen + 1) * 32) / (timer * 4.0);
    }

    printf("__INFO__: %s CycCount     = 0x%016lx\n"       ,prefix, cyc_count);
    printf("__INFO__: %s Timer        = 0x%016lx\n"       ,prefix, timer    );
    printf("__INFO__: %s Latency      = %dns\n"           ,prefix, latency  );
    printf("__INFO__: %s Pending Txns = %d\n"             ,prefix, ot       );
    printf("__INFO__: %s RespError    = 0x%08x\n"         ,prefix, resp_err );
    printf("__INFO__: %s Bandwidth    = %4.2f GBytes/s\n" ,prefix, perf     );

out:
    return rc;
}
