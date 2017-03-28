/*
 * Copyright 2015-2017 Amazon.com, Inc. or its affiliates. All Rights Reserved.
 *
 * Licensed under the Apache License, Version 2.0 (the "License"). You may
 * not use this file except in compliance with the License. A copy of the
 * License is located at
 *
 *     http://aws.amazon.com/apache2.0/
 *
 * or in the "license" file accompanying this file. This file is distributed
 * on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 * express or implied. See the License for the specific language governing
 * permissions and limitations under the License.
 */

#pragma once

#include <fpga_pci.h>

int open_port(uint32_t slot_id, pci_bar_handle_t* jtag_pci_bar);

void close_port(pci_bar_handle_t jtag_pci_bar);

void set_tck(unsigned long nsperiod, unsigned long *result);

void shift_tms_tdi(
    pci_bar_handle_t jtag_pci_bar,
    uint32_t bitcount,
    unsigned char *tms_buf,
    unsigned char *tdi_buf,
    unsigned char *tdo_buf);

int xvcserver_start(
    uint32_t slot_id,
    char* tcp_port);

typedef struct _XvcClient {
    unsigned buf_len;
    unsigned buf_max;
    uint8_t * buf;
    pci_bar_handle_t jtag_pci_bar;
    int fd;
    int locked;
    int enable_locking;
    int enable_status;
    char pending_error[1024];
} XvcClient;

static const size_t XVC_VSEC_ID = 0x0008;
 
#define VALID_OFFSET(a) (a < 0x1000 && a >= 0x100)
 
struct xvc_offsets {
        size_t debug_id_reg_offset;
        size_t length_reg_offset;
        size_t tms_reg_offset;
        size_t tdi_reg_offset;
        size_t tdo_reg_offset;
        size_t control_reg_offset;
};

static const struct xvc_offsets xvc_offsets =
        {0x00, 0x00, 0x04, 0x08, 0x0C, 0x10};  // XVC_ALGO_BAR

#define DEBUG_ID_REG_OFFSET (xvc_offsets.debug_id_reg_offset)
#define LENGTH_REG_OFFSET   (xvc_offsets.length_reg_offset)
#define TMS_REG_OFFSET      (xvc_offsets.tms_reg_offset)
#define TDI_REG_OFFSET      (xvc_offsets.tdi_reg_offset)
#define TDO_REG_OFFSET      (xvc_offsets.tdo_reg_offset)
#define CONTROL_REG_OFFSET  (xvc_offsets.control_reg_offset)


