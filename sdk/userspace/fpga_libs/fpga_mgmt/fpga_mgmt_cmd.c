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

#include <stdlib.h>
#include <string.h>
#include <errno.h>
#include <assert.h>

#include <fpga_mgmt.h>
#include <fpga_pci.h>
#include <afi_cmd_api.h>
#include <fpga_hal_mbox.h>
#include <utils/lcd.h>

#include "fpga_mgmt_internal.h"

/**
 * AFI command get payload length utility.
 *
 * @param[in]  cmd		the command buffer
 *
 * @returns
 * len	the command payload length
 */
static uint32_t
afi_cmd_hdr_get_len(const union afi_cmd *cmd)
{
	return cmd ? (cmd->hdr.len_flags & AFI_CMD_HDR_LEN_MASK) : ~0u;
}

/**
 * AFI command get flags utility.
 *
 * @param[in]  cmd		the command buffer
 *
 * @returns
 * flags	the command flags
 */
static uint32_t
afi_cmd_hdr_get_flags(const union afi_cmd *cmd)
{
	return cmd ? (cmd->hdr.len_flags >> AFI_CMD_HDR_FLAGS_SHIFT) : ~0u;
}

/**
 * AFI command set payload length utility.
 *
 * @param[in]  cmd		the command buffer
 * @param[in]  len		the payload length to set
 *
 * @returns
 *  0	on success 
 * -1	on failure
 */
static int
afi_cmd_hdr_set_len(union afi_cmd *cmd, size_t len)
{
	/* Null pointer or overflow? */
	if (!cmd || (len & ~AFI_CMD_HDR_LEN_MASK)) {
		return FPGA_ERR_FAIL;
	}

	cmd->hdr.len_flags &= ~AFI_CMD_HDR_LEN_MASK;
	cmd->hdr.len_flags |= (uint32_t)len;
	return 0;
}

/**
 * AFI command set flags utility.
 *
 * @param[in]  cmd		the command buffer
 * @param[in]  flags	the flags to set
 *
 * @returns
 *  0	on success 
 * -1	on failure
 */
static int
afi_cmd_hdr_set_flags(union afi_cmd *cmd, unsigned int flags)
{
	/* Null pointer or overflow? */
	if (!cmd || (flags & ~AFI_CMD_HDR_ALL_FLAGS)) {
		return FPGA_ERR_FAIL;
	}

	cmd->hdr.len_flags &= AFI_CMD_HDR_LEN_MASK;
	cmd->hdr.len_flags |= flags << AFI_CMD_HDR_FLAGS_SHIFT;
	return 0;
}



/**
 * Get the next command id.
 *
 * @returns
 * id
 */
static uint32_t
afi_get_next_id(void)
{
	static uint32_t id = 0;

	if (id == 0) {
		id = rand();
	}

	return id++;
}

/**
 * Generate the AFI_CMD_LOAD.
 *
 * @param[in]		cmd		cmd buffer 
 * @param[in,out]	len		cmd len
 */
void 
fpga_mgmt_cmd_init_load(union afi_cmd *cmd, uint32_t *len, union fpga_mgmt_load_local_image_options *opt)
{
	int i;
	assert(cmd);
	assert(len);
	struct afi_cmd_load_req *req = (void *)cmd->body;
	uint32_t payload_len = sizeof(struct afi_cmd_load_req);

	/** Fill in cmd header */
	cmd->hdr.version = AFI_CMD_API_VERSION;
	cmd->hdr.op = AFI_CMD_LOAD;
	cmd->hdr.id = afi_get_next_id();
	afi_cmd_hdr_set_len(cmd, payload_len);
	afi_cmd_hdr_set_flags(cmd, 0);

	/** Fill in cmd body */
	strncpy(req->ids.afi_id, opt->afi_id, sizeof(req->ids.afi_id)); 
	req->ids.afi_id[sizeof(req->ids.afi_id) - 1] = 0; 

	req->fpga_cmd_flags = opt->flags;
	for (i = 0; i<FPGA_MMCM_GROUP_MAX; i++){
		req->clock_frequencies[i].frequency[0] = 1000000 * opt->clock_mains[i];
	}

	*len = sizeof(struct afi_cmd_hdr) + payload_len;
}

/**
 * Generate the AFI_CMD_METRICS.
 *
 * @param[in]		cmd		cmd buffer 
 * @param[in,out]	len		cmd len
 */
void
fpga_mgmt_cmd_init_metrics(union afi_cmd *cmd, uint32_t *len, uint32_t flags)
{
	assert(cmd);
	assert(len);

	struct afi_cmd_metrics_req *req = (void *)cmd->body;
	uint32_t payload_len = sizeof(struct afi_cmd_metrics_req);

	/** Fill in cmd header */
	cmd->hdr.version = AFI_CMD_API_VERSION;
	cmd->hdr.op = AFI_CMD_METRICS;
	cmd->hdr.id = afi_get_next_id();
	afi_cmd_hdr_set_len(cmd, payload_len);
	afi_cmd_hdr_set_flags(cmd, 0);

	/** Fill in cmd body; only allow specific flags to be set */
	req->fpga_cmd_flags = flags &
		(FPGA_CMD_GET_HW_METRICS | FPGA_CMD_CLEAR_HW_METRICS);

	*len = sizeof(struct afi_cmd_hdr) + payload_len;
}

/**
 * Generate the AFI_CMD_CLEAR.
 *
 * @param[in]		cmd		cmd buffer 
 * @param[in,out]	len		cmd len
 */
void 
fpga_mgmt_cmd_init_clear(union afi_cmd *cmd, uint32_t *len)
{
	assert(cmd);
	assert(len);

	struct afi_cmd_clear_req *req = (void *)cmd->body;
	uint32_t payload_len = sizeof(struct afi_cmd_clear_req);

	/** Fill in cmd header */
	cmd->hdr.version = AFI_CMD_API_VERSION;
	cmd->hdr.op = AFI_CMD_CLEAR;
	cmd->hdr.id = afi_get_next_id();
	afi_cmd_hdr_set_len(cmd, payload_len);
	afi_cmd_hdr_set_flags(cmd, 0);

	/** Fill in cmd body */
	req->fpga_cmd_flags = 0;

	*len = sizeof(struct afi_cmd_hdr) + payload_len;
}

/**
 * Handle the AFI_CMD_METRICS response.
 *
 * @param[in]	cmd		cmd buffer 
 * @param[in]	rsp		rsp buffer 
 * @param[in]	len		rsp len
 *
 * @returns
 *  0	on success 
 * -1	on failure
 */
int
fpga_mgmt_cmd_handle_metrics(const union afi_cmd *rsp, uint32_t len,
	struct afi_cmd_metrics_rsp **metrics)
{
	uint32_t tmp_len = 
		sizeof(struct afi_cmd_hdr) + sizeof(struct afi_cmd_metrics_rsp);

	fail_on(len < tmp_len, err, "total_rsp_len(%u) < calculated_len(%u)", 
			len, tmp_len);

	/* We've already validated the header; copy the response into the out
	 * paramater. */
	*metrics = (void *)rsp->body;

	return 0;
err:
	return FPGA_ERR_FAIL;
}


int 
fpga_mgmt_mbox_attach(int slot_id)
{
	/* slot_id not validated on internal function */
	int ret;
	pci_bar_handle_t handle;

	ret = fpga_pci_attach(slot_id,
	                      FPGA_MGMT_PF,
	                      F1_MBOX_RESOURCE_NUM,
	                      0 /* flags */,
	                      &handle);
	fail_on(ret != 0, err, "Unable to attach to mbox bar");

	fpga_mgmt_state.slots[slot_id].handle = handle;

	struct fpga_hal_mbox mbox = {
		.timeout = fpga_mgmt_state.timeout,
		.delay_msec = fpga_mgmt_state.delay_msec,
	};

	ret = fpga_hal_mbox_init(&mbox);
	fail_on(ret != 0, err, "fpga_hal_mbox_init failed");

	ret = fpga_hal_mbox_attach(handle, true); /**< clear_state=true */
	fail_on(ret != 0, err, "fpga_hal_mbox_attach failed");

	return 0;
err:
	return FPGA_ERR_FAIL;
}

int 
fpga_mgmt_mbox_detach(int slot_id)
{
	if (fpga_mgmt_state.slots[slot_id].handle != PCI_BAR_HANDLE_INIT) {
		pci_bar_handle_t handle = fpga_mgmt_state.slots[slot_id].handle;

		int ret = fpga_hal_mbox_detach(handle, true); /**< clear_state=true */
		if (ret != 0) {
			log_error("fpga_hal_mbox_detach failed");
			/** Continue with plat detach */
		}

		ret = fpga_pci_detach(handle);
		if (ret != 0) {
			log_error("fpga_pci_detach failed");
			/* Continue with detach */
		}
		fpga_mgmt_state.slots[slot_id].handle = PCI_BAR_HANDLE_INIT;
	}

	return 0;
}

int 
fpga_mgmt_detach_all(void)
{
	int ret = 0;
	for (unsigned int i = 0; i < sizeof_array(fpga_mgmt_state.slots); ++i) {
		ret |= fpga_mgmt_mbox_detach(i);
	}
	return (ret == 0) ? 0 : -1;
}

/**
 * Handle AFI error response
 *
 * @param[in] rsp   the response that was received.
 * @param[in] len   the expected response payload len.
 *
 * @returns
 *  zero on success, non-zero on failure
 */
static int
fpga_mgmt_handle_afi_cmd_error_rsp(const union afi_cmd *rsp, uint32_t len)
{
	struct afi_cmd_err_rsp *err_rsp = (void *)rsp->body;

	uint32_t tmp_len =
		sizeof(struct afi_cmd_hdr) + sizeof(struct afi_cmd_err_rsp);

	fail_on(len < tmp_len, err, "total_rsp_len(%u) < calculated_len(%u)",
			len, tmp_len);

	/** Handle invalid API version error */
	if (err_rsp->error == FPGA_ERR_AFI_CMD_API_VERSION_INVALID) {
		union afi_err_info *err_info = (void *)err_rsp->error_info;

		tmp_len += sizeof(err_info->afi_cmd_version);
		fail_on(len < tmp_len, err, "total_rsp_len(%u) < calculated_len(%u)",
				len, tmp_len);
		log_error("Error: Please upgrade from aws-fpga github to AFI CMD API Version: v%u\n",
				err_info->afi_cmd_version);

	}

	return err_rsp->error;
err:
	return FPGA_ERR_FAIL;
}

/**
 * Validate the AFI response header, using the command header.
 *
 * @param[in] cmd   the command that was sent.
 * @param[in] rsp   the response that was received.
 * @param[in] len   the expected response payload len.
 *
 * @returns
 *  zero on success, non-zero on failure
 */
static int
fpga_mgmt_afi_validate_header(const union afi_cmd *cmd,
		const union afi_cmd *rsp, uint32_t len)
{
	uint32_t stored_flags = afi_cmd_hdr_get_flags(rsp);
	uint32_t is_response = stored_flags & AFI_CMD_HDR_IS_RSP;
	uint32_t payload_len = afi_cmd_hdr_get_len(rsp);

	fail_on(!cmd, err, "cmd == NULL");
	fail_on(!rsp, err, "rsp == NULL");

	/** Version */
	fail_on(MAJOR_VERSION(cmd->hdr.version) != MAJOR_VERSION(rsp->hdr.version), err,
			"cmd_ver(%u) != rsp_ver(%u), cmd_id=0x%08x",
			cmd->hdr.version, rsp->hdr.version, cmd->hdr.id);

	/** Opcode */
	fail_on(cmd->hdr.op != rsp->hdr.op, op_err, 
			"cmd_op(%u) != rsp_op(%u), cmd_id=0x%08x",
			cmd->hdr.op, rsp->hdr.op, cmd->hdr.id);

	/** Id */
	fail_on(cmd->hdr.id != rsp->hdr.id, id_err, 
			"cmd_id(0x%08x) != rsp_id(0x%08x)",
			cmd->hdr.id, rsp->hdr.id);

	/** Received len too small */
	fail_on(len < sizeof(struct afi_cmd_hdr), err,
			"Received length %u too small", len);

	/** Payload len too big */
	fail_on(payload_len + sizeof(struct afi_cmd_hdr) > AFI_CMD_DATA_LEN,
			err, "Payload length %u too big", payload_len);

	/** Not a response */
	fail_on(!is_response, err, "Command is not a response");
	return 0;

op_err:
	if (rsp->hdr.op == AFI_CMD_ERROR) {
		return fpga_mgmt_handle_afi_cmd_error_rsp(rsp, len);
	}
id_err:
	return -EAGAIN;
err:
	return FPGA_ERR_FAIL;
}

static int
fpga_mgmt_send_cmd(int slot_id,
	const union afi_cmd *cmd, union afi_cmd *rsp, uint32_t *len)
{
	int ret;

	/** Write the AFI cmd to the mailbox */
	pci_bar_handle_t handle = fpga_mgmt_state.slots[slot_id].handle;
	ret = fpga_hal_mbox_write(handle, (void *)cmd, *len);
	fail_on(ret != 0, err, "fpga_hal_mbox_write failed");

	/**
	 * Read the AFI rsp from the mailbox.
	 *  -also make a minimal attempt to drain stale responses
	 *   (if any).
	 */
	uint32_t retries = 0;
	bool done = false;
	while (!done) {
		ret = fpga_hal_mbox_read(handle, (void *)rsp, len);
		fail_on(ret = (ret) ? -ETIMEDOUT : 0, err_code, "Error: operation timed out");

		ret = fpga_mgmt_afi_validate_header(cmd, rsp, *len);
		if (ret == 0) {
			done = true;
		} else {
			fail_on(ret != -EAGAIN, err_code, 
				"fpga_mgmt_afi_validate_header failed");
			fail_on(retries >= AFI_MAX_RETRIES, err, "retries=%u, exceeded",
				retries);
			retries++;
		}
	}

	return 0;
err:
	return FPGA_ERR_FAIL;
err_code:
	return ret;
}

int
fpga_mgmt_process_cmd(int slot_id,
	const union afi_cmd *cmd, union afi_cmd *rsp, uint32_t *len)
{
	bool attached = false;
	int ret;

	fail_slot_id(slot_id, err, ret);

	ret = fpga_mgmt_mbox_attach(slot_id);
	fail_on(ret, err, "fpga_mgmt_mbox_attach failed");

	attached = true;

	ret = fpga_mgmt_send_cmd(slot_id, cmd, rsp, len);
	fail_on(ret, err, "fpga_mgmt_send_cmd failed");
err:
	if (attached) {
		fpga_mgmt_mbox_detach(slot_id);
	}	

	return ret;
}
