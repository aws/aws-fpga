/**
 *  Copyright (C) 2015-2016 Xilinx, Inc. All rights reserved.
 *  Author: Sonal Santan
 *  Portions of ICAP code borrowed from SDAccel XDMA HAL
 *  Portions of MCAP code borrowed from Xilinx AR 64761
 *
 *  This program is free software; you can redistribute it and/or modify
 *  it under the terms of the GNU General Public License as published by
 *  the Free Software Foundation; either version 2 of the License, or
 *  (at your option) any later version.
 *
 *  This program is distributed in the hope that it will be useful,
 *  but WITHOUT ANY WARRANTY; without even the implied warranty of
 *  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 *  GNU General Public License for more details.
 */

#include <linux/module.h>
#include <linux/cdev.h>
#include <linux/delay.h>
#include <linux/uaccess.h>
#include <linux/fs.h>
#include <linux/io.h>
#include <linux/kernel.h>
#include <linux/firmware.h>
#include <linux/pci.h>
#include <linux/vmalloc.h>

#include "xdma-core.h"
#include "xdma-ioctl.h"
#include "xclbin.h"
#include "xbar_sys_parameters.h"
#include "mcap_registers.h"

#define SWAP_ENDIAN_32(x) \
	(unsigned)((((x) & 0xFF000000) >> 24) | (((x) & 0x00FF0000) >> 8) | \
		   (((x) & 0x0000FF00) << 8)  | (((x) & 0x000000FF) << 24))

/*
 * The bitstream is expected in big endian format
 */
const static unsigned fpga_boot_seq[] = {SWAP_ENDIAN_32(DUMMY_WORD),	\
		SWAP_ENDIAN_32(SYNC_WORD),				\
		SWAP_ENDIAN_32(TYPE1_NOOP),				\
		SWAP_ENDIAN_32(TYPE1_WRITE_CMD),			\
		SWAP_ENDIAN_32(IPROG_CMD),				\
		SWAP_ENDIAN_32(TYPE1_NOOP),				\
		SWAP_ENDIAN_32(TYPE1_NOOP)};

static long bitstream_mcap(struct xdma_dev *lro, const char *buffer, unsigned length);

static inline void MCapRegWrite(struct xdma_dev *lro, int offset, u32 value)
{
	pci_write_config_dword(lro->pci_dev, lro->mcap_base + offset, value);
}


static inline u32 MCapRegRead(struct xdma_dev *mdev, int offset)
{
	u32 value;
	pci_read_config_dword(mdev->pci_dev, mdev->mcap_base + offset, &value);
	return value;
}


#define IsResetSet(mdev)			\
	(MCapRegRead(mdev, MCAP_CONTROL) &	\
	 MCAP_CTRL_RESET_MASK ? 1 : 0)

#define IsModuleResetSet(mdev)			\
	(MCapRegRead(mdev, MCAP_CONTROL) &	\
	 MCAP_CTRL_MOD_RESET_MASK ? 1 : 0)

#define IsConfigureMCapReqSet(mdev)		\
	(MCapRegRead(mdev, MCAP_STATUS) &	\
	 MCAP_STS_CFG_MCAP_REQ_MASK ? 1 : 0)

#define IsErrSet(mdev)				\
	(MCapRegRead(mdev, MCAP_STATUS) &	\
	 MCAP_STS_ERR_MASK ? 1 : 0)

#define IsRegReadComplete(mdev)			\
	(MCapRegRead(mdev, MCAP_STATUS) &	\
	 MCAP_STS_REG_READ_CMP_MASK ? 1 : 0)

#define IsFifoOverflow(mdev)			\
	(MCapRegRead(mdev, MCAP_STATUS) &	\
	 MCAP_STS_FIFO_OVERFLOW_MASK ? 1 : 0)

#define GetRegReadCount(mdev)			\
	((MCapRegRead(mdev, MCAP_STATUS) &	\
	  MCAP_STS_REG_READ_COUNT_MASK) >> 5)



static int MCapClearRequestByConfigure(struct xdma_dev *mdev, u32 *restore)
{
	u32 set;
	int loop = MCAP_LOOP_COUNT;

	*restore = MCapRegRead(mdev, MCAP_CONTROL);
	set = *restore;

	if (IsConfigureMCapReqSet(mdev)) {
		/* Set 'Mode' and 'In Use by PCIe' bits */
		set |= (MCAP_CTRL_MODE_MASK | MCAP_CTRL_IN_USE_MASK);
		MCapRegWrite(mdev, MCAP_CONTROL, set);

		do {
			if (!(IsConfigureMCapReqSet(mdev)))
				break;
		} while (loop--);

		if (!loop) {
			printk(KERN_ERR "Failed to clear MCAP Request by config bit\n");
			MCapRegWrite(mdev, MCAP_CONTROL, *restore);
			return -EIO;
		}
	}

	printk(KERN_DEBUG "Request by Configure bit cleared!!\n");

	return 0;
}


static int Checkforcompletion(struct xdma_dev *mdev)
{
	unsigned long retry_count = 0;
	int sr, i;

	sr = MCapRegRead(mdev, MCAP_STATUS);
	while (!(sr & MCAP_STS_EOS_MASK)) {

		msleep(2000);
		for (i=0 ; i < EMCAP_EOS_LOOP_COUNT; i++) {
			MCapRegWrite(mdev, MCAP_DATA, EMCAP_NOOP_VAL);
		}
		sr = MCapRegRead(mdev, MCAP_STATUS);
		retry_count++;
		if (retry_count > EMCAP_EOS_RETRY_COUNT) {
			printk(KERN_ERR "Error: The MCAP EOS bit did not assert after");
			printk(KERN_ERR "programming the specified programming file\n");
			return -ETIMEDOUT;
		}
	}
	return 0;
}

static int MCapFullReset(struct xdma_dev *mdev)
{
	u32 set, restore;
	int err;

	err = MCapClearRequestByConfigure(mdev, &restore);
	if (err)
		return err;

	/* Set 'Mode', 'In Use by PCIe' and 'Module Reset' bits */
	set = MCapRegRead(mdev, MCAP_CONTROL);
	set |= MCAP_CTRL_MODE_MASK | MCAP_CTRL_IN_USE_MASK |
		MCAP_CTRL_RESET_MASK | MCAP_CTRL_MOD_RESET_MASK;
	MCapRegWrite(mdev, MCAP_CONTROL, set);

	if (IsErrSet(mdev) || !(IsModuleResetSet(mdev)) ||
	    !(IsResetSet(mdev))) {
		printk(KERN_ERR "Failed to Full Reset\n");
		MCapRegWrite(mdev, MCAP_CONTROL, restore);
		return -EIO;
	}

	MCapRegWrite(mdev, MCAP_CONTROL, restore);
	printk(KERN_INFO "Full Reset Done!!\n");

	return 0;
}

static int wait_for_done(struct xdma_dev *lro)
{
	u32 w;
	int i = 0;

//	printk(KERN_DEBUG "IOCTL %s:%d\n", __FILE__, __LINE__);
	for (i = 0; i < 10; i++) {
		udelay(5);
		w = read_register(lro->bar[USER_BAR] + XHWICAP_SR);
		printk(KERN_DEBUG "XHWICAP_SR %x\n", w);
		if (w & 0x5)
			return 0;
	}
	printk(KERN_DEBUG "%d us timeout waiting for FPGA after bitstream download\n", 5 * 10);
	return -EIO;
}


static int hwicapWrite(struct xdma_dev *lro, const u32 *word_buf, int size)
{
	u32 value = 0;
	int i = 0;

	for (i = 0; i < size; i++) {
		value = be32_to_cpu(word_buf[i]);
		write_register(value, lro->bar[USER_BAR] + XHWICAP_WF);
	}

	value = 0x1;
	write_register(value, lro->bar[USER_BAR] + XHWICAP_CR);
	for (i = 0; i < 20; i++) {
		value = read_register(lro->bar[USER_BAR] + XHWICAP_SR);
		//printk(KERN_DEBUG "XHWICAP_CR %x\n", value);
		if ((value & 0x1) == 0)
			return 0;
		ndelay(50);

	}
	printk(KERN_DEBUG "%d us timeout waiting for FPGA after writing %d dwords\n", 50 * 10, size);
	return -EIO;
}

static int bitstream_parse_header(const unsigned char *Data, unsigned int Size, XHwIcap_Bit_Header *Header)
{
	unsigned int I;
	unsigned int Len;
	unsigned int Tmp;
	unsigned int Index;

	/* Start Index at start of bitstream */
	Index = 0;

	/* Initialize HeaderLength.  If header returned early inidicates
	 * failure.
	 */
	Header->HeaderLength = XHI_BIT_HEADER_FAILURE;

	/* Get "Magic" length */
	Header->MagicLength = Data[Index++];
	Header->MagicLength = (Header->MagicLength << 8) | Data[Index++];

	/* Read in "magic" */
	for (I = 0; I < Header->MagicLength - 1; I++) {
		Tmp = Data[Index++];
		if (I%2 == 0 && Tmp != XHI_EVEN_MAGIC_BYTE)
			return -1;   /* INVALID_FILE_HEADER_ERROR */

		if (I%2 == 1 && Tmp != XHI_ODD_MAGIC_BYTE)
			return -1;   /* INVALID_FILE_HEADER_ERROR */

	}

	/* Read null end of magic data. */
	Tmp = Data[Index++];

	/* Read 0x01 (short) */
	Tmp = Data[Index++];
	Tmp = (Tmp << 8) | Data[Index++];

	/* Check the "0x01" half word */
	if (Tmp != 0x01)
		return -1;	 /* INVALID_FILE_HEADER_ERROR */



	/* Read 'a' */
	Tmp = Data[Index++];
	if (Tmp != 'a')
		return -1;	  /* INVALID_FILE_HEADER_ERROR	*/


	/* Get Design Name length */
	Len = Data[Index++];
	Len = (Len << 8) | Data[Index++];

	/* allocate space for design name and final null character. */
	Header->DesignName = kmalloc(Len, GFP_KERNEL);

	/* Read in Design Name */
	for (I = 0; I < Len; I++)
		Header->DesignName[I] = Data[Index++];


	if (Header->DesignName[Len-1] != '\0')
		return -1;

	/* Read 'b' */
	Tmp = Data[Index++];
	if (Tmp != 'b')
		return -1;	/* INVALID_FILE_HEADER_ERROR */


	/* Get Part Name length */
	Len = Data[Index++];
	Len = (Len << 8) | Data[Index++];

	/* allocate space for part name and final null character. */
	Header->PartName = kmalloc(Len, GFP_KERNEL);

	/* Read in part name */
	for (I = 0; I < Len; I++)
		Header->PartName[I] = Data[Index++];

	if (Header->PartName[Len-1] != '\0')
		return -1;

	/* Read 'c' */
	Tmp = Data[Index++];
	if (Tmp != 'c')
		return -1;	/* INVALID_FILE_HEADER_ERROR */


	/* Get date length */
	Len = Data[Index++];
	Len = (Len << 8) | Data[Index++];

	/* allocate space for date and final null character. */
	Header->Date = kmalloc(Len, GFP_KERNEL);

	/* Read in date name */
	for (I = 0; I < Len; I++)
		Header->Date[I] = Data[Index++];

	if (Header->Date[Len - 1] != '\0')
		return -1;

	/* Read 'd' */
	Tmp = Data[Index++];
	if (Tmp != 'd')
		return -1;	/* INVALID_FILE_HEADER_ERROR  */

	/* Get time length */
	Len = Data[Index++];
	Len = (Len << 8) | Data[Index++];

	/* allocate space for time and final null character. */
	Header->Time = kmalloc(Len, GFP_KERNEL);

	/* Read in time name */
	for (I = 0; I < Len; I++)
		Header->Time[I] = Data[Index++];

	if (Header->Time[Len - 1] != '\0')
		return -1;

	/* Read 'e' */
	Tmp = Data[Index++];
	if (Tmp != 'e')
		return -1;	/* INVALID_FILE_HEADER_ERROR */

	/* Get byte length of bitstream */
	Header->BitstreamLength = Data[Index++];
	Header->BitstreamLength = (Header->BitstreamLength << 8) | Data[Index++];
	Header->BitstreamLength = (Header->BitstreamLength << 8) | Data[Index++];
	Header->BitstreamLength = (Header->BitstreamLength << 8) | Data[Index++];
	Header->HeaderLength = Index;

	printk(KERN_INFO "%s: Design \"%s\"\n%s: Part \"%s\"\n%s: Timestamp \"%s %s\"\n%s: Raw data size 0x%x\n",
	       DRV_NAME, Header->DesignName, DRV_NAME, Header->PartName, DRV_NAME, Header->Time,
	       Header->Date, DRV_NAME, Header->BitstreamLength);

	return 0;
}


static long bitstream_icap_helper(struct xdma_dev *lro, const u32 *word_buffer, unsigned word_count)
{
	unsigned remain_word = word_count;
	unsigned word_written = 0;
	int wr_fifo_vacancy = 0;
	long err = 0;

	for (remain_word = word_count; remain_word > 0; remain_word -= word_written) {
		wr_fifo_vacancy = read_register(lro->bar[USER_BAR] + XHWICAP_WFV);
		if (wr_fifo_vacancy <= 0) {
			err = -EIO;
			break;
		}
		word_written = (wr_fifo_vacancy < remain_word) ? wr_fifo_vacancy : remain_word;
		if (hwicapWrite(lro, word_buffer, word_written) != 0) {
			err = -EIO;
			break;
		}
		word_buffer += word_written;
	}
	return err;
}


static long bitstream_icap(struct xdma_dev *lro, const char *buffer, unsigned length)
{
	long err = 0;
	XHwIcap_Bit_Header bit_header;
	unsigned numCharsRead = DMA_HWICAP_BITFILE_BUFFER_SIZE;
	unsigned byte_read;

	printk(KERN_DEBUG "IOCTL %s:%s:%d\n", __func__, __FILE__, __LINE__);

	BUG_ON(!buffer);
	BUG_ON(!length);
	if (!buffer || !length)
		return 0;

	memset(&bit_header, 0, sizeof(bit_header));

	if (bitstream_parse_header(buffer, DMA_HWICAP_BITFILE_BUFFER_SIZE, &bit_header)) {
		err = -EINVAL;
		goto free_buffers;
	}

	printk(KERN_DEBUG "IOCTL %s:%s:%d\n", __func__, __FILE__, __LINE__);

	if ((bit_header.HeaderLength + bit_header.BitstreamLength) > length) {
		err = -EINVAL;
		goto free_buffers;
	}

	printk(KERN_DEBUG "IOCTL %s:%s:%d\n", __func__, __FILE__, __LINE__);

	buffer += bit_header.HeaderLength;

	printk(KERN_DEBUG "IOCTL %s:%d\n", __FILE__, __LINE__);

	for (byte_read = 0; byte_read < bit_header.BitstreamLength; byte_read += numCharsRead) {
		numCharsRead = bit_header.BitstreamLength - byte_read;
		if (numCharsRead > DMA_HWICAP_BITFILE_BUFFER_SIZE)
			numCharsRead = DMA_HWICAP_BITFILE_BUFFER_SIZE;

		if (bitstream_icap_helper(lro, (u32 *)buffer, numCharsRead / 4))
			goto free_buffers;
		buffer += numCharsRead;
	}
	printk(KERN_DEBUG "IOCTL %s:%d\n", __FILE__, __LINE__);

	if (wait_for_done(lro)) {
		err = -EIO;
		goto free_buffers;
	}

free_buffers:
	kfree(bit_header.DesignName);
	kfree(bit_header.PartName);
	kfree(bit_header.Date);
	kfree(bit_header.Time);
	printk(KERN_DEBUG "IOCTL %s:%d\n", __FILE__, __LINE__);
	return err;
}

long bitstream_clear_icap(struct xdma_dev *lro)
{
	long err = 0;
	const char *buffer;
	unsigned length;

//	printk(KERN_DEBUG "IOCTL %s:%d\n", __FILE__, __LINE__);
	buffer = lro->stash.clear_bitstream;
	if (!buffer)
		return 0;

	length = lro->stash.clear_bitstream_length;
	printk(KERN_INFO "%s: Downloading clearing bitstream of length 0x%x\n", DRV_NAME, length);
	err = bitstream_icap(lro, buffer, length);

	vfree(lro->stash.clear_bitstream);
	lro->stash.clear_bitstream = 0;
	lro->stash.clear_bitstream_length = 0;
	printk(KERN_DEBUG "IOCTL %s:%d\n", __FILE__, __LINE__);
	return err;
}


static long bitstream_ioctl_icap(struct xdma_dev *lro, const char __user *bit_buf, unsigned long length)
{
	long err = 0;
	XHwIcap_Bit_Header bit_header;
	char *buffer = NULL;
	unsigned numCharsRead = DMA_HWICAP_BITFILE_BUFFER_SIZE;
	unsigned byte_read;

	printk(KERN_DEBUG "%s: Using kernel mode ICAP bitstream download framework\n", DRV_NAME);
	memset(&bit_header, 0, sizeof(bit_header));

	freezeAXIGate(lro);
	err = bitstream_clear_icap(lro);

	if (err)
		goto free_buffers;

	buffer = kmalloc(DMA_HWICAP_BITFILE_BUFFER_SIZE, GFP_KERNEL);

	if (!buffer) {
		err = -ENOMEM;
		goto free_buffers;
	}

//	printk(KERN_DEBUG "IOCTL %s:%d\n", __FILE__, __LINE__);
//	printk(KERN_DEBUG "bitstream pointer %p length %lu\n", bit_buf, length);

	if (copy_from_user(buffer, bit_buf, DMA_HWICAP_BITFILE_BUFFER_SIZE)) {
		err = -EFAULT;
		goto free_buffers;
	}

//	printk(KERN_DEBUG "IOCTL %s:%d\n", __FILE__, __LINE__);

	if (bitstream_parse_header(buffer, DMA_HWICAP_BITFILE_BUFFER_SIZE, &bit_header)) {
		err = -EINVAL;
		goto free_buffers;
	}

	if ((bit_header.HeaderLength + bit_header.BitstreamLength) > length) {
		err = -EINVAL;
		goto free_buffers;
	}

	bit_buf += bit_header.HeaderLength;

//	printk(KERN_DEBUG "IOCTL %s:%d\n", __FILE__, __LINE__);

	for (byte_read = 0; byte_read < bit_header.BitstreamLength; byte_read += numCharsRead) {
		numCharsRead = bit_header.BitstreamLength - byte_read;
		if (numCharsRead > DMA_HWICAP_BITFILE_BUFFER_SIZE)
			numCharsRead = DMA_HWICAP_BITFILE_BUFFER_SIZE;
		if (copy_from_user(buffer, bit_buf, numCharsRead)) {
			err = -EFAULT;
			goto free_buffers;
		}

		bit_buf += numCharsRead;
		if (bitstream_icap_helper(lro, (u32 *)buffer, numCharsRead / 4))
			goto free_buffers;
	}
//	printk(KERN_DEBUG "IOCTL %s:%d\n", __FILE__, __LINE__);

	if (wait_for_done(lro)) {
		err = -ETIMEDOUT;
		goto free_buffers;
	}

	/**
	 * Perform frequency scaling since PR download can silenty overwrite MMCM settings
	 * in static region changing the clock frequencies although ClockWiz CONFIG registers
	 * will misleading report the older configuration from before bitstream download as
	 * if nothing has changed.
	 */
	if (!err)
		err = ocl_freqscaling2(lro, true);


free_buffers:
	freeAXIGate(lro);
	kfree(buffer);
	kfree(bit_header.DesignName);
	kfree(bit_header.PartName);
	kfree(bit_header.Date);
	kfree(bit_header.Time);
//	printk(KERN_DEBUG "IOCTL %s:%d\n", __FILE__, __LINE__);
	return err;
}


static long bitstream_mcap_setup(struct xdma_dev *lro, u32 *restore, bool design_switch)
{
	long err = 0;
	u32 set;

	err = MCapClearRequestByConfigure(lro, restore);
	if (err)
		return err;

	if (IsErrSet(lro) || IsRegReadComplete(lro) ||
	    IsFifoOverflow(lro)) {
		printk(KERN_ERR "Failed to initialize configuring FPGA\n");
		MCapRegWrite(lro, MCAP_CONTROL, *restore);
		err = -EIO;
		return err;
	}

	/* Set 'Mode', 'In Use by PCIe' and 'Data Reg Protect' bits */
	set = MCapRegRead(lro, MCAP_CONTROL);
	set |= MCAP_CTRL_MODE_MASK | MCAP_CTRL_IN_USE_MASK |
		MCAP_CTRL_DATA_REG_PROT_MASK;

	/* Clear 'Reset', 'Module Reset' and 'Register Read' bits */
	set &= ~(MCAP_CTRL_RESET_MASK | MCAP_CTRL_MOD_RESET_MASK |
		 MCAP_CTRL_REG_READ_MASK);
	if (design_switch)
		set &= ~MCAP_CTRL_DESIGN_SWITCH_MASK;

	MCapRegWrite(lro, MCAP_CONTROL, set);
	return err;
}

static long bitstream_mcap_helper(struct xdma_dev *lro, const u32 *word_buffer, unsigned word_count)
{
	unsigned i;
	u32 value;

	for (i = 0; i < word_count; i++) {
		value = be32_to_cpu(word_buffer[i]);
		MCapRegWrite(lro, MCAP_DATA, value);
	}
	return 0;
}

/*
 * This is called by bitstream_ioctl_mcap() after it has setup the MCAP
 * programming registers.
 */
long bitstream_clear_mcap(struct xdma_dev *lro)
{
	long err = 0;
	const char *buffer;
	unsigned length;
	XHwIcap_Bit_Header bit_header;

//	printk(KERN_DEBUG "IOCTL %s:%d\n", __FILE__, __LINE__);
	buffer = lro->stash.clear_bitstream;
	if (!buffer)
		return 0;

	memset(&bit_header, 0, sizeof(bit_header));
	length = lro->stash.clear_bitstream_length;
	printk(KERN_INFO "%s: Downloading clearing bitstream of length 0x%x\n", DRV_NAME, length);
	if (bitstream_parse_header(buffer, DMA_HWICAP_BITFILE_BUFFER_SIZE, &bit_header)) {
		err = -EINVAL;
		goto free_buffers;
	}

	if ((bit_header.HeaderLength + bit_header.BitstreamLength) > length) {
		err = -EINVAL;
		goto free_buffers;
	}

	buffer += bit_header.HeaderLength;
	bitstream_mcap_helper(lro, (u32 *)buffer, bit_header.BitstreamLength / 4);

	vfree(lro->stash.clear_bitstream);
	lro->stash.clear_bitstream = 0;
	lro->stash.clear_bitstream_length = 0;

free_buffers:
	kfree(bit_header.DesignName);
	kfree(bit_header.PartName);
	kfree(bit_header.Date);
	kfree(bit_header.Time);
	return err;
}

/*
 * This function enables the PR bitstream download ioctl for Ultrascale. It automatically downloads
 * clearing bitstream. It does NOT cause design switch.
 */
static long bitstream_ioctl_mcap(struct xdma_dev *lro, const void __user *bit_buf, unsigned long length)
{
	u32 restore;
	long err = 0;
	XHwIcap_Bit_Header bit_header;
	char *buffer = NULL;
	unsigned numCharsRead = DMA_HWICAP_BITFILE_BUFFER_SIZE;
	unsigned byte_read;

	printk(KERN_DEBUG "%s: Using kernel mode MCAP bitstream download framework\n", DRV_NAME);
	memset(&bit_header, 0, sizeof(bit_header));

	if (!bit_buf || !length) {
		return -EINVAL;
	}

	freezeAXIGate(lro);

	buffer = kmalloc(DMA_HWICAP_BITFILE_BUFFER_SIZE, GFP_KERNEL);

	if (!buffer) {
		err = -ENOMEM;
		goto free_buffers;
	}

	if (copy_from_user(buffer, bit_buf, DMA_HWICAP_BITFILE_BUFFER_SIZE)) {
		err = -EFAULT;
		goto free_buffers;
	}

	if (bitstream_parse_header(buffer, DMA_HWICAP_BITFILE_BUFFER_SIZE, &bit_header)) {
		err = -EINVAL;
		goto free_buffers;
	}

	if ((bit_header.HeaderLength + bit_header.BitstreamLength) > length) {
		err = -EINVAL;
		goto free_buffers;
	}

	bit_buf += bit_header.HeaderLength;

	err = bitstream_mcap_setup(lro, &restore, false);
	if (err)
		goto design_switch;

	/* first load the clear bitstream */
	err = bitstream_clear_mcap(lro);

	if (err)
	    goto design_switch;

	/* Write Data */
	for (byte_read = 0; byte_read < bit_header.BitstreamLength; byte_read += numCharsRead) {
		numCharsRead = bit_header.BitstreamLength - byte_read;
		if (numCharsRead > DMA_HWICAP_BITFILE_BUFFER_SIZE)
			numCharsRead = DMA_HWICAP_BITFILE_BUFFER_SIZE;
		if (copy_from_user(buffer, bit_buf, numCharsRead)) {
			err = -EFAULT;
			goto design_switch;
		}

		bit_buf += numCharsRead;
		bitstream_mcap_helper(lro, (u32 *)buffer, numCharsRead / 4);
	}

	err = Checkforcompletion(lro);

	if (err || IsErrSet(lro) || IsFifoOverflow(lro)) {
		printk(KERN_ERR "Failed to Write Bitstream\n");
		MCapRegWrite(lro, MCAP_CONTROL, restore);
		MCapFullReset(lro);
		err = -EIO;
		goto design_switch;
	}

design_switch:
	MCapRegWrite(lro, MCAP_CONTROL, restore);
	/**
	 * Perform frequency scaling since PR download can silenty overwrite MMCM settings
	 * in static region changing the clock frequencies although ClockWiz CONFIG registers
	 * will misleading report the older configuration from before bitstream download as
	 * if nothing has changed.
	 */
	if (!err)
		err = ocl_freqscaling2(lro, true);

free_buffers:
	freeAXIGate(lro);
	kfree(buffer);
	kfree(bit_header.DesignName);
	kfree(bit_header.PartName);
	kfree(bit_header.Date);
	kfree(bit_header.Time);
	return err;
}


long bitstream_ioctl(struct xdma_char *lro_char, unsigned int cmd, const void __user *arg)
{
	struct xdma_ioc_bitstream bitstream_obj;
	struct xclBin bin_obj;
	struct xdma_dev *lro = lro_char->lro;
	char __user *buffer;
	struct xdma_ioc_info2 obj;
	long err = 0;

	if (copy_from_user((void *)&bitstream_obj, arg, sizeof(struct xdma_ioc_bitstream)))
		return -EFAULT;
	if (copy_from_user((void *)&bin_obj, (void *)bitstream_obj.xclbin, sizeof(struct xclBin)))
		return -EFAULT;
	if (memcmp(bin_obj.m_magic, "xclbin0", 8))
		return -EINVAL;

	if ((bin_obj.m_primaryFirmwareOffset + bin_obj.m_primaryFirmwareLength) > bin_obj.m_length)
		return -EINVAL;

	if ((bin_obj.m_secondaryFirmwareOffset + bin_obj.m_secondaryFirmwareLength) > bin_obj.m_length)
		return -EINVAL;

	if ((lro->pci_dev->device == 0x7138) && bin_obj.m_secondaryFirmwareLength)
		return -EINVAL;

	buffer = (char __user *)bitstream_obj.xclbin;
	err = !access_ok(VERIFY_READ, buffer, bin_obj.m_length);
	if (err)
		return -EFAULT;

	buffer += bin_obj.m_primaryFirmwareOffset;
	if (cmd == XDMA_IOCICAPDOWNLOAD) {
		err = bitstream_ioctl_icap(lro, buffer, bin_obj.m_primaryFirmwareLength);
	} else if (cmd == XDMA_IOCMCAPDOWNLOAD) {
		err = bitstream_ioctl_mcap(lro, buffer, bin_obj.m_primaryFirmwareLength);
	} else {
		return -EINVAL;
	}

	if (!err && bin_obj.m_secondaryFirmwareLength) {
		vfree(lro->stash.clear_bitstream);
		lro->stash.clear_bitstream = vmalloc(bin_obj.m_secondaryFirmwareLength);
		if (!lro->stash.clear_bitstream) {
			lro->stash.clear_bitstream_length = 0;
			return -ENOMEM;
		}
		buffer = (char __user *)bitstream_obj.xclbin;
		buffer += bin_obj.m_secondaryFirmwareOffset;
		err = copy_from_user(lro->stash.clear_bitstream, buffer, bin_obj.m_secondaryFirmwareLength);
		if (err) {
			err = -EFAULT;
			vfree(lro->stash.clear_bitstream);
			lro->stash.clear_bitstream = NULL;
			lro->stash.clear_bitstream_length = 0;
		} else {
			lro->stash.clear_bitstream_length = bin_obj.m_secondaryFirmwareLength;
		}
	}
	if (!err && is_XPR(lro)) {
		// Check for MIG calibration
		msleep(100);
		err = device_info(lro, &obj);
		if (err)
			return err;
		if (!obj.mig_calibration)
			return -ETIMEDOUT;
	}
	return err;
}


long load_boot_firmware(struct xdma_dev *lro)
{
	const struct xclBin *bin_obj;
	const struct firmware *fw;
	char fw_name[64];
	XHwIcap_Bit_Header bit_header;
	long err = 0;

	printk(KERN_DEBUG "%s:%s:%d\n", __func__, __FILE__, __LINE__);
	memset(&bit_header, 0, sizeof(bit_header));

	snprintf(fw_name, sizeof(fw_name), "xilinx/%04x-%04x-%04x-%016llx.dsabin",
		 le16_to_cpu(lro->pci_dev->vendor),
		 le16_to_cpu(lro->pci_dev->device),
		 le16_to_cpu(lro->pci_dev->subsystem_device),
		 le64_to_cpu(lro->feature_id));

	err = request_firmware(&fw, fw_name, &lro->pci_dev->dev);

	if (err) {
		printk(KERN_WARNING "Unable to find firmware %s\n", fw_name);
		return err;
	}

	bin_obj = (const struct xclBin *)fw->data;

	if (bin_obj->m_length > fw->size) {
		err = -EINVAL;
		goto done;
	}

	if ((bin_obj->m_primaryFirmwareOffset + bin_obj->m_primaryFirmwareLength) > bin_obj->m_length) {
		err = -EINVAL;
		goto done;
	}

	if ((bin_obj->m_secondaryFirmwareOffset + bin_obj->m_secondaryFirmwareLength) > bin_obj->m_length) {
		err = -EINVAL;
		goto done;
	}

	if (bin_obj->m_primaryFirmwareLength) {
		printk(KERN_INFO "%s: Found second stage bitstream of size 0x%llx in %s\n", DRV_NAME, bin_obj->m_primaryFirmwareLength, fw_name);
		err = bitstream_mcap(lro, fw->data + bin_obj->m_primaryFirmwareOffset, bin_obj->m_primaryFirmwareLength);
		/* If we loaded a new second stage, we do not need the previously stashed clearing bitstream if any */
		vfree(lro->stash.clear_bitstream);
		lro->stash.clear_bitstream = 0;
		lro->stash.clear_bitstream_length = 0;
		if (err) {
			printk(KERN_ERR "%s: Failed to download second stage bitstream\n", DRV_NAME);
			goto done;
		}
		printk(KERN_INFO "%s: Downloaded second stage bitstream\n", DRV_NAME);
	}

	/*
	 * If both primary and secondary bitstreams have been provided then ignore the previously stashed bitstream
	 * if any. If only secondary bitstream was provided  but we found a previously stashed bitstream we should
	 * use the latter since it is more appropriate for the current state of the device
	 */
	if (bin_obj->m_secondaryFirmwareLength && (bin_obj->m_primaryFirmwareLength || !lro->stash.clear_bitstream)) {
		vfree(lro->stash.clear_bitstream);
		lro->stash.clear_bitstream = vmalloc(bin_obj->m_secondaryFirmwareLength);
		if (!lro->stash.clear_bitstream) {
			lro->stash.clear_bitstream_length = 0;
			err = -ENOMEM;
			goto done;
		}
		lro->stash.clear_bitstream_length = bin_obj->m_secondaryFirmwareLength;
		memcpy(lro->stash.clear_bitstream, fw->data + bin_obj->m_secondaryFirmwareOffset,
		       lro->stash.clear_bitstream_length);
		printk(KERN_INFO "%s: Found clearing bitstream of size 0x%x in %s\n", DRV_NAME,
		       lro->stash.clear_bitstream_length, fw_name);
	}
	else if (lro->stash.clear_bitstream) {
		printk(KERN_INFO "%s: Using previously stashed clearing bitstream of size 0x%x\n",
		       DRV_NAME, lro->stash.clear_bitstream_length);
	}

	if (lro->stash.clear_bitstream && bitstream_parse_header(lro->stash.clear_bitstream,
								 DMA_HWICAP_BITFILE_BUFFER_SIZE, &bit_header)) {
		err = -EINVAL;
		vfree(lro->stash.clear_bitstream);
		lro->stash.clear_bitstream = NULL;
		lro->stash.clear_bitstream_length = 0;
		goto done;
	}

done:
	release_firmware(fw);
	kfree(bit_header.DesignName);
	kfree(bit_header.PartName);
	kfree(bit_header.Date);
	kfree(bit_header.Time);
	return err;
}

/*
 * This function will be used in Tandem flow to load full stage2 on Ultrascale. It is
 * called from load_boot_firmware(). We do effect design switch in this flow
 * This function should NOT be used to download PR bitstreams or clearing bit streams
 */

long bitstream_mcap(struct xdma_dev *lro, const char *buffer, unsigned length)
{
	u32 restore;
	long err = 0;
	int len;
	u32 *data;
	XHwIcap_Bit_Header bit_header;

	BUG_ON(!buffer);
	BUG_ON(!length);
	if (!buffer || !length)
		return 0;

	memset(&bit_header, 0, sizeof(bit_header));

	if (bitstream_parse_header(buffer, DMA_HWICAP_BITFILE_BUFFER_SIZE, &bit_header)) {
		err = -EINVAL;
		goto free_buffers;
	}

	if ((bit_header.HeaderLength + bit_header.BitstreamLength) > length) {
		err = -EINVAL;
		goto free_buffers;
	}

	buffer += bit_header.HeaderLength;
	data = (u32 *)buffer;
	len = bit_header.BitstreamLength / 4;

	err = bitstream_mcap_setup(lro, &restore, true);
	if (err)
	    goto free_buffers;;

	bitstream_mcap_helper(lro, data, len);

	/* Check for Completion */
	err = Checkforcompletion(lro);

	if (err || IsErrSet(lro) || IsFifoOverflow(lro)) {
		printk(KERN_ERR "Failed to Write Bitstream\n");
		MCapRegWrite(lro, MCAP_CONTROL, restore);
		MCapFullReset(lro);
		err = -EIO;
		goto free_buffers;
	}

	/* Enable PCIe BAR reads/writes in the PCIe hardblock */
	restore |= MCAP_CTRL_DESIGN_SWITCH_MASK;
	MCapRegWrite(lro, MCAP_CONTROL, restore);

free_buffers:
	kfree(bit_header.DesignName);
	kfree(bit_header.PartName);
	kfree(bit_header.Date);
	kfree(bit_header.Time);
	return err;
}

static int mcap_reset_ministream(struct xdma_dev *lro)
{
	long err;
	u32 restore;

	err = bitstream_mcap_setup(lro, &restore, false);
	bitstream_mcap_helper(lro, fpga_boot_seq, sizeof(fpga_boot_seq) / 4);
	printk(KERN_DEBUG "%s: Downloaded reset ministream\n", DRV_NAME);
	vfree(lro->stash.clear_bitstream);
	lro->stash.clear_bitstream = 0;
	lro->stash.clear_bitstream_length = 0;
	msleep(4000);
	load_boot_firmware(lro);
	MCapRegWrite(lro, MCAP_CONTROL, restore);
	return 0;
}

static int icap_reset_ministream(struct xdma_dev *lro)
{
	u32 value;
	int i;

	for (i=0; i < (sizeof(fpga_boot_seq) / 4); i++) {
		value = be32_to_cpu(fpga_boot_seq[i]);
		write_register(value, lro->bar[USER_BAR] + XHWICAP_WF);
	}
	value = 0x1;
	write_register(value, lro->bar[USER_BAR] + XHWICAP_CR);
	printk(KERN_DEBUG "%s: Downloaded reset ministream\n", DRV_NAME);
	msleep(4000);
	return 0;
}

int load_reset_mini_bitstream(struct xdma_dev *lro)
{
	if (is_ultrascale(lro))
	    return mcap_reset_ministream(lro);
	else
	    return icap_reset_ministream(lro);
}
