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

#include <fpga_common.h>
#include <afi_cmd_api.h>
#include <hal/fpga_hal_mbox.h>
#include <fpga_mgmt.h>
#include <fpga_pci.h>
#include <utils/lcd.h>

#include <string.h>
#include <errno.h>

#include "fpga_mgmt_internal.h"

struct fgpa_mgmt_state_s fpga_mgmt_state = {
	.plat_attached = false,
	.slot_id = 0,
	.timeout = FPAG_MGMT_TIMEOUT_DFLT,
	.delay_msec = FPAG_MGMT_DELAY_MSEC_DFLT
};

int fpga_mgmt_init(void) {
	return fpga_pci_init();
}

void fpag_mgmt_set_cmd_timeout(uint32_t value)
{
	fpga_mgmt_state.timeout = value;
}

void fpag_mgmt_set_cmd_delay_msec(uint32_t value)
{
	fpga_mgmt_state.delay_msec = value;
}

int fpga_mgmt_describe_local_image(int slot_id,
	struct fpga_mgmt_image_info *info)
{
	int ret;
	uint32_t len;
	union afi_cmd cmd;
	union afi_cmd rsp;

	/* map afi_cmd_api status onto public api status */
	static enum fpga_status status_map[] = {
		[ACMS_LOADED] = FPGA_STATUS_LOADED,
		[ACMS_CLEARED] = FPGA_STATUS_CLEARED,
		[ACMS_BUSY] = FPGA_STATUS_BUSY,
		[ACMS_NOT_PROGRAMMED] = FPGA_STATUS_NOT_PROGRAMMED,
	};

	if (!info) {
		return -EINVAL;
	}

	memset(&cmd, 0, sizeof(union afi_cmd));
	memset(&rsp, 0, sizeof(union afi_cmd));

	/* initialize the command structure */
	fpga_mgmt_cmd_init_metrics(&cmd, &len, 
		/*bool get_hw_metrics*/ false,
		/*bool clear_hw_metrics*/ false);

	/* send the command and wait for the response */
	ret = fpga_mgmt_process_cmd(slot_id, &cmd, &rsp, &len);
	fail_on(ret, out, "fpga_mgmt_process_cmd failed");

	/* extract the relevant data from the response */
	struct afi_cmd_metrics_rsp *metrics;
	ret = fpga_mgmt_cmd_handle_metrics(&rsp, len, &metrics);
	fail_on(ret, out, "fpga_mgmt_cmd_handle_metrics failed");

	/* translate the response structure to the API structure */

	if (metrics->status < 0 || metrics->status >= (signed) sizeof_array(status_map)) {
		info->status = FPGA_STATUS_BUSY;
	} else {
		info->status = status_map[metrics->status];
	}

	info->slot_id = slot_id;

	char *afi_id = (!metrics->ids.afi_id[0]) ? "none" : metrics->ids.afi_id;
	strncpy(info->afi_id, afi_id, sizeof(info->afi_id));

	struct fpga_hal_mbox_versions ver;
	ret = fpga_hal_mbox_get_versions(&ver);
	fail_on(ret, out, "fpga_hal_mbox_get_versions failed");
	info->sh_version = ver.sh_version;

	ret = fpga_pci_get_slot_spec(slot_id, 0, 0, &info->spec);
	fail_on(ret, out, "fpga_pci_get_slot_spec failed");

	/* copy the metrics into the out param */
	info->metrics = metrics->fmc;

out:
	return ret;
}

/**
 * Gets the status of an FPGA. Status values are definted in enum fpga_status.
 * If you need the AFI id at the same time, use fpga_mgmt_describe_local_image.
 *
 * @param[in]  slot_id  the logical slot index
 * @param[out] status   populated with status value
 * @returns 0 on success, non-zero on error
 */
int fpga_mgmt_get_status(int slot_id, int *status)
{
	int ret;
	struct fpga_mgmt_image_info info;

	if (!status) {
		return -EINVAL;
	}

	memset(&info, 0, sizeof(struct fpga_mgmt_image_info));

	ret = fpga_mgmt_describe_local_image(slot_id, &info);
	fail_on(ret, out, "fpga_mgmt_describe_local_image failed");

	*status = info.status;
out:
	return ret;
}

const char *fpga_mgmt_get_status_name(int status) {
	static const char *status_names[] = {
		[FPGA_STATUS_LOADED] = "loaded",
		[FPGA_STATUS_CLEARED] = "cleared",
		[FPGA_STATUS_BUSY] = "busy",
		[FPGA_STATUS_NOT_PROGRAMMED] = "not programmed",
		[FPGA_STATUS_MAX] = "unknown/invalid"
	};

	if (status < 0 || status >= FPGA_STATUS_MAX) {
		return status_names[FPGA_STATUS_MAX];
	} else {
		return status_names[status];
	}
}

int fpga_mgmt_clear_local_image(int slot_id) {
	int ret;
	uint32_t len;
	union afi_cmd cmd;
	union afi_cmd rsp;

	memset(&cmd, 0, sizeof(union afi_cmd));
	memset(&rsp, 0, sizeof(union afi_cmd));

	/* initialize the command structure */
	fpga_mgmt_cmd_init_clear(&cmd, &len);

	/* send the command and wait for the response */
	ret = fpga_mgmt_process_cmd(slot_id, &cmd, &rsp, &len);
	fail_on(ret, out, "fpga_mgmt_process_cmd failed");

	/* the clear command does not have an interesting response payload */
out:
	return ret;
}

int fpga_mgmt_load_local_image(int slot_id, char *afi_id) {
	int ret;
	uint32_t len;
	union afi_cmd cmd;
	union afi_cmd rsp;

	memset(&cmd, 0, sizeof(union afi_cmd));
	memset(&rsp, 0, sizeof(union afi_cmd));

	/* initialize the command structure */
	fpga_mgmt_cmd_init_load(&cmd, &len, afi_id);

	/* send the command and wait for the response */
	ret = fpga_mgmt_process_cmd(slot_id, &cmd, &rsp, &len);
	fail_on(ret, out, "fpga_mgmt_process_cmd failed");

	/* the load command does not have an interesting response payload */
out:
	return ret;
}

int fpga_mgmt_get_vLED_status(int slot_id, uint16_t *status) {
	(void)slot_id;
	(void)status;

	/* not implemented */
	return 1;

	/* fpga_hal_reg_read(...) */
}

int fpga_mgmt_set_vDIP(int slot_id, uint16_t value) {
	(void) slot_id;
	(void) value;

	/* not implemented */
	return 1;

	/* fpga_hal_reg_write(...) */
}

int fpga_mgmt_get_vDIP_status(int slot_id, uint16_t *value) {
	(void) slot_id;
	(void) value;

	/* not implemented */
	return 1;

	/* fpga_hal_reg_read(...) */
}

int fpga_mgmt_get_virtual_jtag_state(int slot_id, bool *enabled) {
	(void) slot_id;
	(void) enabled;

	/* not implemented */
	return 1;
}

int fpga_mgmt_set_virtual_jtag(int slot_id, bool enabled) {
	(void) slot_id;
	(void) enabled;

	/* not implemented */
	return 1;
}
