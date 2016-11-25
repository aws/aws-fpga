/*
 * Copyright 2016-2016 Amazon.com, Inc. or its affiliates. All Rights Reserved.
 */

/** @file
 * FPGA HAL mailbox operations
 */

#include <assert.h>
#include <stdio.h>
#include <string.h>
#include <unistd.h>
#include <fcntl.h>
#include <sys/stat.h>
#include <time.h>
#include <errno.h>

#include <fpga_common.h>
#include <fpga_hal_mbox.h>
#include <fpga_hal_reg.h>
#include <lcd.h>

#include "fpga_hal_mbox_regs.h"

static struct fpga_hal_mbox_private {
	struct fpga_hal_mbox mbox;
} priv;

static void
fpga_hal_mbox_print_reg_offsets(void)
{
	log_debug("FMB_BASE=0x%08x, status=0x%08x", 
			FMB_BASE, FMB_REG_STATUS);

	log_debug("Reg Offsets: mb_wr_index=0x%08x, mb_wr_data=0x%08x, mb_wr_len=0x%08x", 
			FMB_REG_WR_INDEX, FMB_REG_WR_DATA, FMB_REG_WR_LEN);

	log_debug("Reg Offsets: mb_rd_index=0x%08x, mb_rd_data=0x%08x, mb_rd_len=0x%08x", 
			FMB_REG_RD_INDEX, FMB_REG_RD_DATA, FMB_REG_RD_LEN);
}

int
fpga_hal_mbox_init(struct fpga_hal_mbox *mbox)
{
	log_debug("enter");
	assert(mbox);
	assert(mbox->slot < FPGA_SLOT_MAX);

	priv.mbox = *mbox;

#if 1
	fpga_hal_mbox_print_reg_offsets();
#endif

	return 0;
}

int
fpga_hal_mbox_reset(void)
{
	/** Clear any existing state */
	uint32_t val;
	int ret = fpga_hal_reg_read(FMB_REG_STATUS, &val);
	fail_on(ret != 0, err, "fpga_hal_reg_read(status) failed");

	if (val & FMB_RX_EVT) {
		ret = fpga_hal_reg_write(FMB_REG_STATUS, FMB_RX_EVT);
		fail_on(ret != 0, err, "fpga_hal_reg_write(status) failed");
	}
	if (val & FMB_TX_EVT) {
		ret = fpga_hal_reg_write(FMB_REG_STATUS, FMB_TX_EVT);
		fail_on(ret != 0, err, "fpga_hal_reg_write(status) failed");
	}
	return 0;
err:
	return -1;
}

int 
fpga_hal_mbox_attach(bool clear_state)
{
	if (clear_state) {
		int ret = fpga_hal_mbox_reset();
		fail_on(ret != 0, err, "fpga_hal_mbox_reset failed");
	}
	return 0;
err:
	return -1;
}

int 
fpga_hal_mbox_detach(bool clear_state)
{
	if (clear_state) {
		int ret = fpga_hal_mbox_reset();
		fail_on(ret != 0, err, "fpga_hal_mbox_reset failed");
	}
	return 0;
err:
	return -1;
}

static int 
fpga_hal_mbox_check_len(uint32_t len)
{
	fail_on(len < sizeof(uint32_t), err, "len(%u) < %u", 
		len, (uint32_t) sizeof(uint32_t));
	fail_on(len & 0x3, err, "Len must be a multiple of 4");
	fail_on(len > FPGA_MBOX_MSG_DATA_LEN, err, "len(%u) > %u", 
			len, FPGA_MBOX_MSG_DATA_LEN);
	return 0;
err:
	return -1;
}

int 
fpga_hal_mbox_read_async(void *msg, uint32_t *len)
{
	log_debug("enter");
	assert(msg);
	assert(len);

	uint32_t val;
	int ret = fpga_hal_reg_read(FMB_REG_STATUS, &val);
	fail_on(ret != 0, err, "fpga_hal_reg_read(status) failed");

	/** Check if an RX event is available */
	if (!(val & FMB_RX_EVT)) {
		log_debug("RX msg not available");
		goto err_again;
	}

	/** Read and check the length */
	uint32_t mb_rd_len;
	ret = fpga_hal_reg_read(FMB_REG_RD_LEN, &mb_rd_len);
	fail_on(ret != 0, err, "fpga_hal_reg_read(mb_rd_len) failed");

	ret = fpga_hal_mbox_check_len(mb_rd_len << 2);
	fail_on(ret != 0, err, "fpga_hal_mbox_check_len failed");

	/** Reset the read index to 0 */
	ret = fpga_hal_reg_write(FMB_REG_RD_INDEX, 0);
	fail_on(ret != 0, err, "fpga_hal_reg_write(mb_rd_index) failed");

	/** Read the data.  Index is auto-incremented */
	uint32_t i;
	uint32_t *m32 = msg;
	for (i = 0; i < mb_rd_len; i++) {
		ret = fpga_hal_reg_read(FMB_REG_RD_DATA, m32);
		fail_on(ret != 0, err, "fpga_hal_reg_read(mb_rd_data) failed");

		m32++;
	}

	/** Acknowledge the RX event */
	ret = fpga_hal_reg_write(FMB_REG_STATUS, FMB_RX_EVT);
	fail_on(ret != 0, err, "fpga_hal_reg_write(status) failed");

	*len = mb_rd_len << 2;
	log_debug("Read len=%u", *len);
	return 0;

err_again:
	return -EAGAIN;
err:
	return -1;
}

/** Test and Clear (TC) async write acknowledgement */
int 
fpga_hal_mbox_write_async_tc_ack(bool *ack)
{
	uint32_t val;
	int ret = fpga_hal_reg_read(FMB_REG_STATUS, &val);
	fail_on(ret != 0, err, "fpga_hal_reg_read(status) failed");

	/** Check for TX event */
	if (val & FMB_TX_EVT) {
		/** Acknowledge the TX event */
		ret = fpga_hal_reg_write(FMB_REG_STATUS, FMB_TX_EVT);
		fail_on(ret != 0, err, "fpga_hal_reg_write(status) failed");

		/** Setup the return */
		*ack = true;
	} else {
		/** Setup the return */
		*ack = false;
	}
	return 0;
err:
	return -1;
}

int 
fpga_hal_mbox_write_async(void *msg, uint32_t len)
{
	log_debug("enter");
	assert(msg);

	int ret = fpga_hal_mbox_check_len(len);
	fail_on(ret != 0, err, "fpga_hal_mbox_check_len failed");

	/** Clear any previous async write state */
	bool ack;
	ret = fpga_hal_mbox_write_async_tc_ack(&ack);
	fail_on(ret != 0, err, "fpga_hal_mbox_write_async_tc_ack failed");

	/** Reset the write index to 0 */
	ret = fpga_hal_reg_write(FMB_REG_WR_INDEX, 0);
	fail_on(ret != 0, err, "fpga_hal_reg_write(mb_wr_index) failed");

	/** Write the data.  Index is auto-incremented */
	uint32_t mb_wr_len = len >> 2;
	uint32_t *m32 = msg;
	uint32_t i;
	for (i = 0; i < mb_wr_len; i++) {
		ret = fpga_hal_reg_write(FMB_REG_WR_DATA, *m32);
		fail_on(ret != 0, err, "fpga_hal_reg_write(mb_wr_data) failed");

		m32++;
	}

	/** Write the (32b word) data length */
	ret = fpga_hal_reg_write(FMB_REG_WR_LEN, mb_wr_len);
	fail_on(ret != 0, err, "fpga_hal_reg_write(mb_wr_len) failed");

	log_debug("Wrote len=%u", len);
	return 0;
err:
	return -1;
}

int 
fpga_hal_mbox_read(void *msg, uint32_t *len)
{
	log_debug("enter");
	assert(msg);
	assert(len);

	uint32_t count = priv.mbox.timeout;

	while (count) {
		int ret = fpga_hal_mbox_read_async(msg, len);
		if (ret == 0) {
			goto out;
		}
		/** Sleep and retry on EAGAIN, otherwise error out of loop */ 
		fail_on(ret != -EAGAIN, err, "fpga_hal_mbox_read_async failed");
		msleep(priv.mbox.delay_msec);
		count--;
	}

	fail_on(!count, err, "Timeout on mbox read, timeout=%u, delay_msec=%u", 
			priv.mbox.timeout, priv.mbox.delay_msec);
out:
	return 0;
err:
	return -1;
}

int 
fpga_hal_mbox_write(void *msg, uint32_t len)
{
	log_debug("enter");
	assert(msg);
	
	int ret = fpga_hal_mbox_write_async(msg, len);
	fail_on(ret != 0, err, "fpga_hal_mbox_write_async failed");

	uint32_t count = priv.mbox.timeout;
	while (count) {
		bool ack = false;;
		ret = fpga_hal_mbox_write_async_tc_ack(&ack);
		fail_on(ret != 0, err, "fpga_hal_mbox_write_async_tc_ack failed");

		if (ack) {
			goto out;
		}

		/** Sleep and try again */
		msleep(priv.mbox.delay_msec);
		count--;
	}

	fail_on(!count, err, "Timeout on mbox write, timeout=%u, delay_msec=%u", 
			priv.mbox.timeout, priv.mbox.delay_msec);
out:
	return 0;
err:
	return -1;
}
