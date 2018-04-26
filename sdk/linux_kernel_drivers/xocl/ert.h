/**
 *  Copyright (C) 2018 Xilinx, Inc
 *
 *  This file is dual licensed.  It may be redistributed and/or modified
 *  under the terms of the Apache 2.0 License OR version 2 of the GNU
 *  General Public License.
 *
 *  Apache License Verbiage
 *
 *  Licensed under the Apache License, Version 2.0 (the "License");
 *  you may not use this file except in compliance with the License.
 *  You may obtain a copy of the License at
 *
 *  http://www.apache.org/licenses/LICENSE-2.0
 *
 *  Unless required by applicable law or agreed to in writing, software
 *  distributed under the License is distributed on an "AS IS" BASIS,
 *  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 *  See the License for the specific language governing permissions and
 *  limitations under the License.
 *
 *  GPL license Verbiage:
 *
 *  This program is free software; you can redistribute it and/or
 *  modify it under the terms of the GNU General Public License as
 *  published by the Free Software Foundation; either version 2 of the
 *  License, or (at your option) any later version.  This program is
 *  distributed in the hope that it will be useful, but WITHOUT ANY
 *  WARRANTY; without even the implied warranty of MERCHANTABILITY or
 *  FITNESS FOR A PARTICULAR PURPOSE. See the GNU General Public
 *  License for more details.  You should have received a copy of the
 *  GNU General Public License along with this program; if not, write
 *  to the Free Software Foundation, Inc., 59 Temple Place, Suite 330,
 *  Boston, MA 02111-1307 USA
 *
 */

/**
 *  Xilinx SDAccel Embedded Runtime definition
 *  Copyright (C) 2018, Xilinx Inc - All rights reserved
 *
 *  This file is dual licensed.  It may be redistributed and/or modified
 *  under the terms of the Apache 2.0 License OR version 2 of the GNU
 *  General Public License.
 */

#ifndef _ERT_H_
#define _ERT_H_

#if defined(__KERNEL__)
# include <linux/types.h>
#else
# include <stdint.h>
#endif

/**
 * ERT generic packet format
 *
 * @state:   [3-0] current state of a command
 * @custom:  [11-4] custom per specific commands
 * @count:   [22-12] number of words in payload (data)
 * @opcode:  [27-23] opcode identifying specific command
 * @type:    [31-27] type of command (currently 0)
 * @data:    count number of words representing packet payload
 */
struct ert_packet {
  union {
    struct {
      uint32_t state:4;   /* [3-0]   */
      uint32_t custom:8;  /* [11-4]  */
      uint32_t count:11;  /* [22-12] */
      uint32_t opcode:5;  /* [27-23] */
      uint32_t type:4;    /* [31-27] */
    };
    uint32_t header;
  };
  uint32_t data[1];   /* count number of words */
};

/**
 * ERT start kernel command format
 *
 * @state:           [3-0] current state of a command
 * @extra_cu_masks:  [11-10] extra CU masks in addition to mandatory mask
 * @count:           [22-12] number of words in payload (data)
 * @opcode:          [27-23] 0, opcode for start_kernel
 * @type:            [31-27] 0, type of start_kernel
 *
 * @cu_mask:         first mandatory CU mask
 * @data:            count number of words representing command payload
 *
 * The packet payload is comprised of 1 mandatory CU mask plus
 * extra_cu_masks per header field, followed a CU register map of size
 * (count - (1 + extra_cu_masks)) uint32_t words.
 */
struct ert_start_kernel_cmd {
  union {
    struct {
      uint32_t state:4;          /* [3-0]   */
      uint32_t unused:6;         /* [9-4]  */
      uint32_t extra_cu_masks:2; /* [11-10]  */
      uint32_t count:11;         /* [22-12] */
      uint32_t opcode:5;         /* [27-23] */
      uint32_t type:4;           /* [31-27] */
    };
    uint32_t header;
  };

  /* payload */
  uint32_t cu_mask;          /* mandatory cu mask */
  uint32_t data[1];          /* count-1 number of words */
};

/**
 * ERT configure command format
 *
 * @state:           [3-0] current state of a command
 * @count:           [22-12] 5, number of words in payload 
 * @opcode:          [27-23] 1, opcode for configure
 * @type:            [31-27] 0, type of configure
 *
 * @slot_size:       command queue slot size
 * @num_cus:         number of compute units in program
 * @cu_shift:        shift value to convert CU idx to CU addr
 * @cu_base_addr:    base address to add to CU addr for actual physical address
 *
 * @ert:1            enable embedded HW scheduler
 * @polling:1        poll for command completion
 * @cu_dma:1         enable CUDMA custom module for HW scheduler
 * @cu_isr:1         enable CUISR custom module for HW scheduler
 * @cq_int:1         enable interrupt from host to HW scheduler
 */
struct ert_configure_cmd {
  union {
    struct {
      uint32_t state:4;          /* [3-0]   */
      uint32_t unused:8;         /* [11-4]  */
      uint32_t count:11;         /* [22-12] */
      uint32_t opcode:5;         /* [27-23] */
      uint32_t type:4;           /* [31-27] */
    };
    uint32_t header;
  };
  
  /* payload */
  uint32_t slot_size;
  uint32_t num_cus;
  uint32_t cu_shift;
  uint32_t cu_base_addr;

  /* features */
  uint32_t ert:1;
  uint32_t polling:1;
  uint32_t cu_dma:1;
  uint32_t cu_isr:1;
  uint32_t cq_int:1;
  uint32_t unusedf:27;
};

/**
 * ERT command state 
 *
 * @ERT_CMD_STATE_NEW:      Set by host before submitting a command to scheduler
 * @ERT_CMD_STATE_QUEUED:   Internal scheduler state
 * @ERT_CMD_STATE_RUNNING:  Internal scheduler state
 * @ERT_CMD_STATE_COMPLETE: Set by scheduler when command completes
 * @ERT_CMD_STATE_ERROR:    Set by scheduler if command failed
 * @ERT_CMD_STATE_ABORT:    Set by scheduler if command abort
 */
enum ert_cmd_state {
  ERT_CMD_STATE_NEW = 1,
  ERT_CMD_STATE_QUEUED = 2,
  ERT_CMD_STATE_RUNNING = 3,
  ERT_CMD_STATE_COMPLETED = 4,
  ERT_CMD_STATE_ERROR = 5,
  ERT_CMD_STATE_ABORT = 6,
};

/**
 * Opcode types for commands
 *
 * @ERT_START_CU:       start a workgroup on a CU
 * @ERT_START_KERNEL:   currently aliased to ERT_START_CU
 * @ERT_CONFIGURE:      configure command scheduler
 */
enum ert_cmd_opcode {
  ERT_START_CU     = 0,
  ERT_START_KERNEL = 0,
  ERT_CONFIGURE    = 1,
};

/**
 * Address constants per spec
 */
#define ERT_WORD_SIZE                     4          /* 4 bytes */
#define ERT_CQ_SIZE                       0x10000    /* 64K */
#define ERT_CQ_BASE_ADDR                  0x190000
#define ERT_CSR_ADDR                      0x180000

/**
 * The STATUS REGISTER is for communicating completed CQ slot indices
 * MicroBlaze write, host reads.  MB(W) / HOST(COR)
 */
#define ERT_STATUS_REGISTER_ADDR          (ERT_CSR_ADDR)      
#define ERT_STATUS_REGISTER_ADDR0         (ERT_CSR_ADDR)      
#define ERT_STATUS_REGISTER_ADDR1         (ERT_CSR_ADDR + 0x4)
#define ERT_STATUS_REGISTER_ADDR2         (ERT_CSR_ADDR + 0x8)
#define ERT_STATUS_REGISTER_ADDR3         (ERT_CSR_ADDR + 0xC)

/**
 * The CU DMA REGISTER is for communicating which CQ slot is to be started
 * on a specific CU.  MB selects a free CU on which the command can
 * run, then writes the 1<<CU back to the command slot CU mask and 
 * writes the slot index to the CU DMA REGISTER.  HW is notified when
 * the register is written and now does the DMA transfer of CU regmap
 * map from command to CU, while MB continues its work. MB(W) / HW(R)
 */
#define ERT_CU_DMA_ENABLE_ADDR            (ERT_CSR_ADDR + 0x18)
#define ERT_CU_DMA_REGISTER_ADDR          (ERT_CSR_ADDR + 0x1C)
#define ERT_CU_DMA_REGISTER_ADDR0         (ERT_CSR_ADDR + 0x1C)
#define ERT_CU_DMA_REGISTER_ADDR1         (ERT_CSR_ADDR + 0x20)
#define ERT_CU_DMA_REGISTER_ADDR2         (ERT_CSR_ADDR + 0x24)
#define ERT_CU_DMA_REGISTER_ADDR3         (ERT_CSR_ADDR + 0x28)

/**
 * The SLOT SIZE is the size of slots in command queue, it is
 * configurable per xclbin. MB(W) / HW(R)
 */
#define ERT_CQ_SLOT_SIZE_ADDR             (ERT_CSR_ADDR + 0x2C)

/**
 * The CU_OFFSET is the size of a CU's address map in power of 2.  For
 * example a 64K regmap is 2^16 so 16 is written to the CU_OFFSET_ADDR.
 * MB(W) / HW(R)
 */
#define ERT_CU_OFFSET_ADDR                (ERT_CSR_ADDR + 0x30)

/**
 * The number of slots is command_queue_size / slot_size.  
 * MB(W) / HW(R)
 */
#define ERT_CQ_NUMBER_OF_SLOTS_ADDR       (ERT_CSR_ADDR + 0x34)

/**
 * All CUs placed in same address space separated by CU_OFFSET. The
 * CU_BASE_ADDRESS is the address of the first CU. MB(W) / HW(R)
 */
#define ERT_CU_BASE_ADDRESS_ADDR          (ERT_CSR_ADDR + 0x38)

/** 
 * The CQ_BASE_ADDRESS is the base address of the command queue.
 * MB(W) / HW(R)
 */
#define ERT_CQ_BASE_ADDRESS_ADDR          (ERT_CSR_ADDR + 0x3C)

/**
 * The CU_ISR_HANDLER_ENABLE (MB(W)/HW(R)) enables the HW handling of
 * CU interrupts.  When a CU interrupts (when done), hardware handles
 * the interrupt and writes the index of the CU that completed into
 * the CU_STATUS_REGISTER (HW(W)/MB(COR)) as a bitmask
 */
#define ERT_CU_ISR_HANDLER_ENABLE_ADDR    (ERT_CSR_ADDR + 0x40)
#define ERT_CU_STATUS_REGISTER_ADDR       (ERT_CSR_ADDR + 0x44)
#define ERT_CU_STATUS_REGISTER_ADDR0      (ERT_CSR_ADDR + 0x44)
#define ERT_CU_STATUS_REGISTER_ADDR1      (ERT_CSR_ADDR + 0x48)
#define ERT_CU_STATUS_REGISTER_ADDR2      (ERT_CSR_ADDR + 0x4C)
#define ERT_CU_STATUS_REGISTER_ADDR3      (ERT_CSR_ADDR + 0x50)

/**
 * The CQ_STATUS_ENABLE (MB(W)/HW(R)) enables interrupts from HOST to
 * MB to indicate the presense of a new command in some slot.  The
 * slot index is written to the CQ_STATUS_REGISTER (HOST(W)/MB(R))
 */
#define ERT_CQ_STATUS_ENABLE_ADDR         (ERT_CSR_ADDR + 0x54) 
#define ERT_CQ_STATUS_REGISTER_ADDR       (ERT_CSR_ADDR + 0x58)
#define ERT_CQ_STATUS_REGISTER_ADDR0      (ERT_CSR_ADDR + 0x58)
#define ERT_CQ_STATUS_REGISTER_ADDR1      (ERT_CSR_ADDR + 0x5C)
#define ERT_CQ_STATUS_REGISTER_ADDR2      (ERT_CSR_ADDR + 0x60)
#define ERT_CQ_STATUS_REGISTER_ADDR3      (ERT_CSR_ADDR + 0x64)

/**
 * The NUMBER_OF_CU (MB(W)/HW(R) is the number of CUs per current
 * xclbin.  This is an optimization that allows HW to only check CU
 * completion on actual CUs.
 */
#define ERT_NUMBER_OF_CU_ADDR             (ERT_CSR_ADDR + 0x68)

/** 
 * Enable global interrupts from MB to HOST on command completion.
 * When enabled writing to STATUS_REGISTER causes an interrupt in HOST.
 * MB(W)
 */
#define ERT_HOST_INTERRUPT_ENABLE_ADDR    (ERT_CSR_ADDR + 0x100)

/**
 * Interrupt controller base address
 * This value is per hardware BSP (XPAR_INTC_SINGLE_BASEADDR)
 */
#define ERT_INTC_ADDR                     0x41200000

/**
 * Interrupt address masks written by MB when interrupts from
 * CU are enabled
 */
#define ERT_INTC_IPR_ADDR                 (ERT_INTC_ADDR + 0x4)  /* pending */
#define ERT_INTC_IER_ADDR                 (ERT_INTC_ADDR + 0x8)  /* enable */
#define ERT_INTC_IAR_ADDR                 (ERT_INTC_ADDR + 0x0C) /* acknowledge */
#define ERT_INTC_MER_ADDR                 (ERT_INTC_ADDR + 0x1C) /* master enable */

#endif
