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

/**
 * Default timeout:
 *   CLI_TIMEOUT_DFLT * CLI_DELAY_MSEC_DFLT
 */
#define FPGA_MGMT_TIMEOUT_DFLT    25
#define FPGA_MGMT_DELAY_MSEC_DFLT 200

/** First flag bit, @see afi_cmd_hdr#len_flags */
#define AFI_CMD_HDR_FLAGS_SHIFT 24

/** Mask to get the length portion, @see afi_cmd_hdr#len_flags */
#define AFI_CMD_HDR_LEN_MASK    ((1 << AFI_CMD_HDR_FLAGS_SHIFT) - 1)

/** Max retries for draining presumed stale AFI CMD responses */
#define AFI_MAX_RETRIES		1

/** F1 Mailbox PF defines */
#define F1_MBOX_VENDOR_ID		0x1d0f
#define F1_MBOX_DEVICE_ID		0x1041
#define F1_MBOX_RESOURCE_NUM	0

extern struct fgpa_mgmt_state_s {
	struct {
		pci_bar_handle_t handle;
	} slots[FPGA_SLOT_MAX];
	uint32_t timeout;
	uint32_t delay_msec;
} fpga_mgmt_state;

// FIXME
#define	F1_VIRTUAL_LED_REG_OFFSET	0xD0UL
#define F1_VIRTUAL_DIP_REG_OFFSET       0xD4UL

/** */
int fpga_mgmt_process_cmd(int slot_id,
	const union afi_cmd *cmd, union afi_cmd *rsp, uint32_t *len);
void fpga_mgmt_cmd_init_metrics(union afi_cmd *cmd, uint32_t *len,
	uint32_t flags);
void fpga_mgmt_cmd_init_load(union afi_cmd *rsp, uint32_t *len,
	union fpga_mgmt_load_local_image_options *opt);
void fpga_mgmt_cmd_init_clear(union afi_cmd *cmd, uint32_t *len);

int
fpga_mgmt_cmd_handle_metrics(const union afi_cmd *rsp, uint32_t len,
	struct afi_cmd_metrics_rsp **metrics);

int fpga_mgmt_mbox_attach(int slot_id);
int fpga_mgmt_mbox_detach(int slot_id);
int fpga_mgmt_detach_all(void);

#define fail_slot_id(slot_id, label, ret) do {               \
	if (slot_id < 0 || slot_id >= FPGA_SLOT_MAX) {           \
		log_error("slot_id is out of range: %d", slot_id);   \
		ret = -EINVAL;                                       \
		goto label;                                          \
	}	                                                     \
} while (0)
