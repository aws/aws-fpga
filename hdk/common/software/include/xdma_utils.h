// Amazon FPGA Hardware Development Kit
//
// Copyright 2016 Amazon.com, Inc. or its affiliates. All Rights Reserved.
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


typedef struct xdma_desc_tag {
  union {
    struct {
      uint32_t control:8;
      uint32_t nxt_adj:6;
      uint32_t :2;
      uint32_t magic:16;
    } fields;
    uint32_t word;
  } header;
  uint32_t len;
  uint32_t src_adr_lo;
  uint32_t src_adr_hi;
  uint32_t dst_adr_lo;
  uint32_t dst_adr_hi;
  uint32_t nxt_adr_lo;
  uint32_t nxt_adr_hi;
} XDMA_DESC;

void que_buffer_to_cl(int chan, uint8_t *buf, size_t len);
void que_cl_to_buffer(int chan, uint8_t *buf, size_t len);
void start_move_to_cl(int chan);
void start_move_to_buffer(int chan);
void is_move_to_cl_done(int chan);
void is_move_to_buffer_done(int chan);
