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


int open_port(uint32_t slot_id, pci_bar_handle_t* jtag_pci_bar) {
   int ret;
/* attach to slot S */
  ret = fpga_pci_attach(FPGA_MGMT_PF, MGMT_PF_2, jtag_pci_bar);
  
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

void set_tck(pci_bar_handle_t jtag_pci_bar, unsigned long nsperiod, unsigned long *result) {
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
    	unsigned long bitcount,
    	unsigned char *tms_buf,
    	unsigned char *tdi_buf,
    	unsigned char *tdo_buf) {

    	struct timeval  start;
	uint32_t num_bits;
	int current_bit;
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
		int shift_num_bits = 32;
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
