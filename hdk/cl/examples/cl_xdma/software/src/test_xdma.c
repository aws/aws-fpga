#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>

// Vivado does not support svGetScopeFromName
#ifndef VIVADO_SIM
#include "svdpi.h"
#endif

#include "sh_dpi_tasks.h"

#include "cl_xdma.h"

XDMA_DESC *h2c_desc_list_head;

// XDMA Target IDs
#define H2C_TGT 0x0
#define C2H_TGT 0x1
#define IRQ_TGT 0x2
#define CFG_TGT 0x3
#define H2C_SGDMA_TGT 0x4
#define C2H_SGDMA_TGT 0x5
#define SGDMA_CMN_TGT 0x6
#define MSIX_TGT 0x8

// XDMA H2C Channel Register Space
#define H2C_ID           0x00
#define H2C_CTRL0        0x04
#define H2C_CTRL1        0x08
#define H2C_CTRL2        0x0c
#define H2C_STAT0        0x40
#define H2C_STAT1        0x44
#define H2C_CMP_DESC_CNT 0x48
#define H2C_ALGN         0x4c
#define H2C_POLL_ADDR_LO 0x88
#define H2C_POLL_ADDR_HI 0x8c
#define H2C_INT_MSK0     0x90
#define H2C_INT_MSK1     0x94
#define H2C_INT_MSK2     0x98
#define H2C_PMON_CTRL    0xc0
#define H2C_PCYC_CNT0    0xc4
#define H2C_PCYC_CNT1    0xc4
#define H2C_PDAT_CNT0    0xcc
#define H2C_PDAT_CNT1    0xd0

static XDMA_DESC *h2c_desc_table;
static int h2c_desc_index = 0;

uint32_t dma_reg_addr(uint32_t target, uint32_t channel, uint32_t offset) {
  return ((target << 12) | (channel << 8) | offset);
}

void que_buffer_to_cl(int chan, uint8_t *buf, size_t len) {

  // setup descriptor table if this is first call
  if (h2c_desc_index == 0) {
    h2c_desc_table = (XDMA_DESC *)memalign(4096, 4096);  // allocate 4k aligned to a 4k boundary
    
    sv_map_host_memory(h2c_desc_table);
  
  }

  h2c_desc_table[h2c_desc_index].header.word = 0; // make sure reserved bits and unused bits are 0
  h2c_desc_table[h2c_desc_index].header.fields.control = 0x01;
  h2c_desc_table[h2c_desc_index].header.fields.nxt_adj = 0;
  h2c_desc_table[h2c_desc_index].header.fields.magic = 0xad4b;
  h2c_desc_table[h2c_desc_index].len = len;
  h2c_desc_table[h2c_desc_index].src_adr_lo = LOW_32b(buf);
  h2c_desc_table[h2c_desc_index].src_adr_hi = HIGH_32b(buf);
  h2c_desc_table[h2c_desc_index].dst_adr_lo = 0;
  h2c_desc_table[h2c_desc_index].dst_adr_hi = 0;
  h2c_desc_table[h2c_desc_index].nxt_adr_lo = 0;
  h2c_desc_table[h2c_desc_index].nxt_adr_hi = 0;

  // remove stop bit from previous descriptor
  if (h2c_desc_index > 0) {
    h2c_desc_table[h2c_desc_index-1].header.fields.control &= 0xfe;
  }

  h2c_desc_index++;
}

void que_cl_to_buffer(int chan, uint8_t *buf, size_t len) {
}

void start_move_to_cl(int chan) {
  uint64_t base_addr;
  uint32_t data;

  get_base_addr_of_func(2, 0, &base_addr);
  log_printf("base_addr: %16lx", base_addr);

  reg_read(base_addr, &data);
  log_printf("data: %08x", data);

  reg_read(base_addr+4, &data);
  log_printf("data: %08x", data);

  reg_write(base_addr+dma_reg_addr(H2C_SGDMA_TGT, 0, 0x80), LOW_32b(h2c_desc_table));
  reg_write(base_addr+dma_reg_addr(H2C_SGDMA_TGT, 0, 0x84), HIGH_32b(h2c_desc_table));

  reg_write(base_addr+dma_reg_addr(H2C_SGDMA_TGT, 0, 0x88), h2c_desc_index-1);  // don't count the first entry

  reg_read(base_addr+dma_reg_addr(H2C_SGDMA_TGT, 0, 0x80), &data);
  log_printf("data: %08x", data);

  reg_read(base_addr+dma_reg_addr(H2C_SGDMA_TGT, 0, 0x84), &data);
  log_printf("data: %08x", data);

  reg_read(base_addr+dma_reg_addr(H2C_SGDMA_TGT, 0, 0x88), &data);
  log_printf("data: %08x", data);

  // sett pollmode_wb, ie_completed & run bit
  reg_write(base_addr+dma_reg_addr(H2C_TGT, 0, H2C_CTRL0), 0x04000005);
  reg_read(base_addr+dma_reg_addr(H2C_TGT, 0, H2C_CTRL0), &data);
  log_printf("data: %08x", data);

}

void start_move_to_buffer(int chan) {
}

void is_move_to_cl_done(int chan) {
}

void is_move_to_buffer_done(int chan) {
}

void test_main(uint32_t *exit_code) {

// Vivado does not support svGetScopeFromName
#ifndef VIVADO_SIM
  svScope scope;
#endif

  uint64_t cycle_count;
  uint64_t error_addr;

  uint8_t error_index;

  int timeout_count;

  int error_count;
  int fail;

  XDMA_DESC *h2c_desc;

  error_count = 0;
  fail = 0;

// Vivado does not support svGetScopeFromName
#ifndef VIVADO_SIM
  scope = svGetScopeFromName("tb");
  svSetScope(scope);
#endif

  {
    uint8_t *buf;

    buf = (uint8_t *)malloc(64);
    que_buffer_to_cl(0, buf, 64);

    buf = (uint8_t *)malloc(128);
    que_buffer_to_cl(0, buf, 128);

    start_move_to_cl(0);
  }

  sv_pause(50);

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
