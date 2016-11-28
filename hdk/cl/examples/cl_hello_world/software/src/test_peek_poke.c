#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>

#include "sh_dpi_tasks.h"

#define WR_INSTR_INDEX UINT64_C(0x1c)
#define WR_ADDR_LOW    UINT64_C(0x20)
#define WR_ADDR_HIGH   UINT64_C(0x24)
#define WR_DATA        UINT64_C(0x28)
#define WR_SIZE        UINT64_C(0x2c)

#define RD_INSTR_INDEX UINT64_C(0x3c)
#define RD_ADDR_LOW    UINT64_C(0x40)
#define RD_ADDR_HIGH   UINT64_C(0x44)
#define RD_DATA        UINT64_C(0x48)
#define RD_SIZE        UINT64_C(0x4c)

#define CNTL_REG       UINT64_C(0x08)

#define WR_START_BIT   0x00000001
#define RD_START_BIT   0x00000002

void test_main(uint32_t *exit_code) {
  long long addr;
  uint8_t *buffer;
  int j;

  buffer = (uint8_t *)malloc(1024);

  sv_map_host_memory(buffer);

  log_printf("test_main is running...");

  cl_poke(WR_INSTR_INDEX, 0);
  cl_poke(WR_ADDR_LOW,   LOW_32b(buffer));
  cl_poke(WR_ADDR_HIGH, HIGH_32b(buffer));
  cl_poke(WR_DATA, 0);
  cl_poke(WR_SIZE, 2);

  cl_poke(RD_INSTR_INDEX, 0);
  cl_poke(RD_ADDR_LOW,   LOW_32b(buffer));
  cl_poke(RD_ADDR_HIGH, HIGH_32b(buffer));
  cl_poke(RD_DATA, 0);
  cl_poke(RD_SIZE, 2);

  cl_poke(CNTL_REG, WR_START_BIT | RD_START_BIT);      // start read & write

  sv_pause(2);                                         // wait 2us

  // for fun print out the incrementing pattern
  // written by the CL
  for (j=0; j<64; j++)
    printf("buffer[%d] = %0x\n", j, buffer[j]);

  log_printf("test_main is done.");

  *exit_code = 0;
}
