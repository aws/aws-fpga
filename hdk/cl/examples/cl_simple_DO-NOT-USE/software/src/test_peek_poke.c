#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>

// Vivado does not support svGetScopeFromName
#ifdef INCLUDE_DPI_CALLS
#ifndef VIVADO_SIM
#include "svdpi.h"
#endif
#endif

#include "sh_dpi_tasks.h"

#define CFG_REG           UINT64_C(0x00)
#define CNTL_REG          UINT64_C(0x08)
#define NUM_INST          UINT64_C(0x10)
#define MAX_RD_REQ        UINT64_C(0x14)

#define WR_INSTR_INDEX    UINT64_C(0x1c)
#define WR_ADDR_LOW       UINT64_C(0x20)
#define WR_ADDR_HIGH      UINT64_C(0x24)
#define WR_DATA           UINT64_C(0x28)
#define WR_LEN            UINT64_C(0x2c)

#define RD_INSTR_INDEX    UINT64_C(0x3c)
#define RD_ADDR_LOW       UINT64_C(0x40)
#define RD_ADDR_HIGH      UINT64_C(0x44)
#define RD_DATA           UINT64_C(0x48)
#define RD_LEN            UINT64_C(0x4c)

#define RD_ERR            UINT64_C(0xb0)
#define RD_ERR_ADDR_LOW   UINT64_C(0xb4)
#define RD_ERR_ADDR_HIGH  UINT64_C(0xb8)
#define RD_ERR_INDEX      UINT64_C(0xbc)

#define WR_CYCLE_CNT_LOW  UINT64_C(0xf0)
#define WR_CYCLE_CNT_HIGH UINT64_C(0xf4)
#define RD_CYCLE_CNT_LOW  UINT64_C(0xf8)
#define RD_CYCLE_CNT_HIGH UINT64_C(0xfc)

#define WR_START_BIT   0x00000001
#define RD_START_BIT   0x00000002

void test_main(uint32_t *exit_code) {

// Vivado does not support svGetScopeFromName
#ifdef INCLUDE_DPI_CALLS
#ifndef VIVADO_SIM
  svScope scope;
#endif
#endif

  uint8_t *buffer;
  uint32_t pcim_data;

  uint32_t read_data;

  uint64_t cycle_count;
  uint64_t error_addr;

  uint8_t error_index;

  int timeout_count;

  int error_count;
  int fail;

  int debug;
  int j;

  // NOTE: Set debug to 1 to dump buffer contents
  debug = 0;

  error_count = 0;
  fail = 0;

// Vivado does not support svGetScopeFromName
#ifdef INCLUDE_DPI_CALLS
#ifndef VIVADO_SIM
  scope = svGetScopeFromName("tb");
  svSetScope(scope);
#endif
#endif

  buffer = (uint8_t *)malloc(1024);
  // Align to 64 byte boundary
  buffer += 0x3fUL;
  buffer = (uint8_t *)((uint64_t)buffer & ~(0x3fUL));
  sv_map_host_memory(buffer);

  pcim_data = 0x6c93af50;

  log_printf("Programming cl_tst registers for PCIe\n");

  cl_poke(CFG_REG, 0x01000018);

  cl_poke(MAX_RD_REQ, 0x0000000f);

  cl_poke(WR_INSTR_INDEX, 0x00000000);
  cl_poke(WR_ADDR_LOW,   LOW_32b(buffer));
  cl_poke(WR_ADDR_HIGH, HIGH_32b(buffer));
  cl_poke(WR_DATA, pcim_data);
  cl_poke(WR_LEN, 0x00000001);

  cl_poke(RD_INSTR_INDEX, 0x00000000);
  cl_poke(RD_ADDR_LOW,   LOW_32b(buffer));
  cl_poke(RD_ADDR_HIGH, HIGH_32b(buffer));
  cl_poke(RD_DATA, pcim_data);
  cl_poke(RD_LEN, 0x00000001);

  cl_poke(NUM_INST, 0x00000000);

  cl_poke(CNTL_REG, WR_START_BIT | RD_START_BIT);      // start read & write

  log_printf("Waiting for PCIe write and read activity to complete\n");
  sv_pause(2);                                         // wait 2us

  // Make sure writes and reads completed successfully
  timeout_count = 0;
  do {
    cl_peek(CNTL_REG, &read_data);
    read_data &= 0x00000007;
    timeout_count++;
  } while ((read_data != 0x0) && (timeout_count < 100));

  if ((timeout_count == 100) && (read_data != 0x0)) {
    log_printf("*** ERROR *** Timeout waiting for writes and reads to complete.\n");
    error_count++;
  } else {
    cl_poke(CNTL_REG, 0x00000000);

    log_printf("Checking some register values\n");

    cycle_count = 0x0;
    cl_peek(WR_CYCLE_CNT_LOW, &read_data);
    cycle_count = read_data;
    cl_peek(WR_CYCLE_CNT_HIGH, &read_data);
    cycle_count |= (read_data << 32);
    if (cycle_count == 0x0) {
      log_printf("*** ERROR *** Write Timer value was 0x0 at end of test.\n");
      error_count++;
    }

    cycle_count = 0x0;
    cl_peek(RD_CYCLE_CNT_LOW, &read_data);
    cycle_count = read_data;
    cl_peek(RD_CYCLE_CNT_HIGH, &read_data);
    cycle_count |= (read_data << 32);
    if (cycle_count == 0x0) {
      log_printf("*** ERROR *** Read Timer value was 0x0 at end of test.\n");
      error_count++;
    }

    log_printf("Checking for read compare errors\n");

    cl_peek(RD_ERR, &read_data);
    if (read_data != 0x0) {
      cl_peek(RD_ERR_ADDR_LOW, &read_data);
      error_addr = read_data;
      cl_peek(RD_ERR_ADDR_HIGH, &read_data);
      error_addr |= (read_data << 32);
      cl_peek(RD_ERR_INDEX, &read_data);
      error_index = read_data & 0x0000000f;
      log_printf("*** ERROR *** Read compare error from address 0x%08x %08x, index 0x%1x\n", (error_addr >> 32), error_addr, error_index);
      error_count++;
    }

    // For debug, print out the incrementing pattern
    //  that was written by the CL
    if (debug == 1) {
      printf("Printing out buffer contents\n");
      for (j=0; j<64; j++)
        printf("buffer[%2d] = 0x%0x\n", j, buffer[j]);
    }

  }

  // Report pass/fail status
  log_printf("Checking total error count...\n");
  if (error_count > 0) {
    fail = 1;
  }
  log_printf("Detected %3d errors during this test\n", error_count);

  if (fail != 0) {
    log_printf("*** TEST FAILED ***\n");
  } else {
    log_printf("*** TEST PASSED ***\n");
  }

  *exit_code = 0;
}
