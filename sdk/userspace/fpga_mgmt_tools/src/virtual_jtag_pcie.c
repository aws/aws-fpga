/*
 * Copyright 2015-2016 Amazon.com, Inc. or its affiliates. All Rights Reserved.
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

/*
 * PCIe xvcserver
 *
 */

#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <fcntl.h>
#include <sys/mman.h>
#include <assert.h>

#include <unistd.h>

#include <sys/time.h>

#include <fpga_pci.h>

#include <sys/ioctl.h>
#include <errno.h>

#include "virtual_jtag.h"


int open_port(uint32_t slot_id, pci_bar_handle_t* jtag_pci_bar) {
   int ret;
/* attach to slot S */
  ret = fpga_pci_attach(slot_id, FPGA_MGMT_PF, MGMT_PF_BAR2,0, jtag_pci_bar);
  
  if (ret) {
  // FIXME
    return ret;
  }
  
  return (0);
}

void close_port(pci_bar_handle_t jtag_pci_bar) {
  if (jtag_pci_bar >=0)
    fpga_pci_detach(jtag_pci_bar);
  
}

void set_tck( unsigned long nsperiod, unsigned long *result) {
    *result = nsperiod;
}

static int xvc_shift_bits(pci_bar_handle_t jtag_pci_bar, uint32_t tms_bits, uint32_t tdi_bits, uint32_t *tdo_bits) {
	int status;
	uint32_t control_reg_data;
	int count = 100;

	// Set tms bits
	status = fpga_pci_poke(jtag_pci_bar, TMS_REG_OFFSET, tms_bits);
	if (status != 0) {
		return status;
	}

	// Set tdi bits and shift data out
	status = fpga_pci_poke(jtag_pci_bar, TDI_REG_OFFSET, tdi_bits);
	if (status != 0) {
		return status;
	}
	// Enable shift operation
	status = fpga_pci_poke(jtag_pci_bar, CONTROL_REG_OFFSET, 0x01);
	if (status != 0) {
		return status;
	}
	while (count) {
	// Read control reg to check shift operation completion
		status = fpga_pci_peek(jtag_pci_bar, CONTROL_REG_OFFSET, &control_reg_data);
		if (status != 0) {
			return status;
		}
	
		if ((control_reg_data & 0x01) == 0)	{
			break;
		}
		count--;

		if (count == 0)	{
			//printk(KERN_ERR LOG_PREFIX "XVC bar transaction timed out (%0X)\n", control_reg_data);
			return -ETIMEDOUT;
		}
	}
  
  // Read tdo bits back out
	// note that tdo_bits already defined as pointer to an integer and not an integer
  status = fpga_pci_peek(jtag_pci_bar, TDO_REG_OFFSET, tdo_bits);
	return status;
}


void shift_tms_tdi(
    	pci_bar_handle_t jtag_pci_bar,
    	uint32_t bitcount,
    	unsigned char *tms_buf,
    	unsigned char *tdi_buf,
    	unsigned char *tdo_buf) {

    	struct timeval  start;
	uint32_t num_bits;
	uint32_t current_bit;
	uint32_t tms_store=0, tdi_store=0, tdo_store=0;
	unsigned char* tms_buf_tmp;
	unsigned char* tdi_buf_tmp;
	unsigned char* tdo_buf_tmp;

	int status = 0;

	num_bits = bitcount;
    	
	gettimeofday(&start, NULL);

	// Set length register to 32 initially if more than one word-transaction is to be done
	if (num_bits >= 32) {
		status = fpga_pci_poke(jtag_pci_bar, LENGTH_REG_OFFSET, 0x20);
		if (status) {
			goto cleanup;
		}
	}
	current_bit = 0;
	while (current_bit < num_bits) {
		int shift_num_bytes;
		unsigned int shift_num_bits = 32;
		if (num_bits - current_bit < shift_num_bits) {
			shift_num_bits = num_bits - current_bit;
			// do LENGTH_REG_OFFSET here
			// Set number of bits to shift out
			status = fpga_pci_poke(jtag_pci_bar, LENGTH_REG_OFFSET, shift_num_bits);
			if (status != 0) {
				goto cleanup;
			}
		}

		shift_num_bytes = (shift_num_bits + 7) / 8;
		tms_buf_tmp = tms_buf + (current_bit / 8);
		tdi_buf_tmp = tdi_buf + (current_bit / 8);
		tdo_buf_tmp = tdo_buf + (current_bit / 8);
	
		memcpy(&tms_store, tms_buf_tmp, shift_num_bytes);
		memcpy(&tdi_store, tdi_buf_tmp, shift_num_bytes);

		// Shift data out and copy to output buffer
		status = xvc_shift_bits(jtag_pci_bar, tms_store, tdi_store, &tdo_store);
		if (status) {
			goto cleanup;
		}

		memcpy(tdo_buf_tmp, &tdo_store, shift_num_bytes);

		current_bit += shift_num_bits;
	}

cleanup:
	return;
}
