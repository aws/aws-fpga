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

#include <string.h>
#include <errno.h>

#include <fpga_mgmt.h>
#include <afi_cmd_api.h>
#include <fpga_hal_mbox.h>
#include <utils/lcd.h>

#include "fpga_mgmt_internal.h"

/** Synchronous API (load/clear) default timeout and delay msecs */
#define FPGA_MGMT_SYNC_TIMEOUT		300	
#define FPGA_MGMT_SYNC_DELAY_MSEC	200 

struct fgpa_mgmt_state_s fpga_mgmt_state = {
	.timeout = FPGA_MGMT_TIMEOUT_DFLT,
	.delay_msec = FPGA_MGMT_DELAY_MSEC_DFLT,
};

int fpga_mgmt_init(void)
{
	for (unsigned int i = 0; i < sizeof_array(fpga_mgmt_state.slots); ++i) {
		fpga_mgmt_state.slots[i].handle = PCI_BAR_HANDLE_INIT;
	}
	return fpga_pci_init();
}

int fpga_mgmt_close(void)
{
	return FPGA_ERR_OK;
}

void fpga_mgmt_set_cmd_timeout(uint32_t value)
{
	fpga_mgmt_state.timeout = value;
}

void fpga_mgmt_set_cmd_delay_msec(uint32_t value)
{
	fpga_mgmt_state.delay_msec = value;
}

static 
int fpga_mgmt_get_sh_version(int slot_id, uint32_t *sh_version)
{
	pci_bar_handle_t handle = PCI_BAR_HANDLE_INIT;
	int ret = -EINVAL;

	fail_on(!sh_version, err, "sh_version is NULL");
	fail_slot_id(slot_id, err, ret);

	ret = fpga_mgmt_mbox_attach(slot_id);
	fail_on(ret, err, "fpga_mgmt_mbox_attach failed");

	handle = fpga_mgmt_state.slots[slot_id].handle;

	struct fpga_hal_mbox_versions ver;
	ret = fpga_hal_mbox_get_versions(handle, &ver);
	fail_on(ret, err, "fpga_hal_mbox_get_versions failed");

	*sh_version = ver.sh_version;
err:
	if (handle != PCI_BAR_HANDLE_INIT) {
		fpga_mgmt_mbox_detach(slot_id);
	}
	
	return ret;
}

int fpga_mgmt_describe_local_image(int slot_id,
	struct fpga_mgmt_image_info *info, uint32_t flags)
{
	int ret;
	uint32_t len;
	union afi_cmd cmd;
	union afi_cmd rsp;

	fail_slot_id(slot_id, out, ret);

	if (!info) {
		return -EINVAL;
	}

	memset(&cmd, 0, sizeof(union afi_cmd));
	memset(&rsp, 0, sizeof(union afi_cmd));

	/* initialize the command structure */
	fpga_mgmt_cmd_init_metrics(&cmd, &len, flags);

	/* send the command and wait for the response */
	ret = fpga_mgmt_process_cmd(slot_id, &cmd, &rsp, &len);
	fail_on(ret, out, "fpga_mgmt_process_cmd failed");

	/* extract the relevant data from the response */
	struct afi_cmd_metrics_rsp *metrics;
	ret = fpga_mgmt_cmd_handle_metrics(&rsp, len, &metrics);
	fail_on(ret, out, "fpga_mgmt_cmd_handle_metrics failed");

	/* translate the response structure to the API structure */
	info->status = metrics->status;
	info->status_q = metrics->status_q;
	info->slot_id = slot_id;

	char *afi_id = (!metrics->ids.afi_id[0]) ? "none" : metrics->ids.afi_id;
	info->ids = metrics->ids;
	strncpy(info->ids.afi_id, afi_id, sizeof(info->ids.afi_id));

	uint32_t sh_version;
	ret = fpga_mgmt_get_sh_version(slot_id, &sh_version);
	fail_on(ret, out, "fpga_mgmt_get_sh_version failed");
	info->sh_version = sh_version;

	ret = fpga_pci_get_slot_spec(slot_id, &info->spec);
	fail_on(ret, out, "fpga_pci_get_slot_spec failed");

	/* copy the metrics into the out param */
	info->metrics = metrics->fmc;

out:
	return ret;
}

int fpga_mgmt_get_status(int slot_id, int *status, int *status_q)
{
	int ret;
	struct fpga_mgmt_image_info info;

	fail_slot_id(slot_id, out, ret);

	if (!status) {
		return -EINVAL;
	}

	memset(&info, 0, sizeof(struct fpga_mgmt_image_info));

	ret = fpga_mgmt_describe_local_image(slot_id, &info, 0);
	fail_on(ret, out, "fpga_mgmt_describe_local_image failed");

	*status = info.status;
	*status_q = info.status_q;
out:
	return ret;
}

const char *fpga_mgmt_get_status_name(int status)
{
	return FPGA_STATUS2STR(status);
}

const char *fpga_mgmt_strerror(int err) 
{
	if (err < 0) {
		return strerror(-err);
	}
	return FPGA_ERR2STR(err);
}

int fpga_mgmt_clear_local_image(int slot_id) 
{
	int ret;
	uint32_t len;
	union afi_cmd cmd;
	union afi_cmd rsp;

	fail_slot_id(slot_id, out, ret);

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

int fpga_mgmt_clear_local_image_sync(int slot_id, 
		uint32_t timeout, uint32_t delay_msec,
		struct fpga_mgmt_image_info *info) 
{
	struct fpga_mgmt_image_info tmp_info;
	struct fpga_pci_resource_map app_map;
	uint32_t prev_sh_version = 0;
	uint32_t sh_version = 0;
	uint32_t retries = 0;
	bool done = false;
	int status;
	int ret;

	/** Allow timeout adjustments that are greater than the defaults */
	uint32_t timeout_tmp = (timeout > FPGA_MGMT_SYNC_TIMEOUT) ?
		timeout : FPGA_MGMT_SYNC_TIMEOUT;
	uint32_t delay_msec_tmp = (delay_msec > FPGA_MGMT_SYNC_DELAY_MSEC) ?
		delay_msec : FPGA_MGMT_SYNC_DELAY_MSEC;

	memset(&tmp_info, 0, sizeof(tmp_info));

	/** 
	 * Get the current SH version and PCI resource map for the app_pf 
	 * that will be used after the clear has completed.
	 */
	ret = fpga_mgmt_get_sh_version(slot_id, &prev_sh_version);
	fail_on(ret != 0, out, "fpga_mgmt_get_sh_version failed");

	ret = fpga_pci_get_resource_map(slot_id, FPGA_APP_PF, &app_map);
	fail_on(ret != 0, out, "fpga_pci_get_resource_map failed");

	/** Clear the FPGA image (async completion) */
	ret = fpga_mgmt_clear_local_image(slot_id);
	fail_on(ret, out, "fpga_mgmt_clear_local_image failed");

	/** Wait until the status is "cleared" or timeout */
	while (!done) {
		ret = fpga_mgmt_describe_local_image(slot_id, &tmp_info, 0); /** flags==0 */

		status = (ret == 0) ? tmp_info.status : FPGA_STATUS_END;
		if (status == FPGA_STATUS_CLEARED) {
			done = true;
		} else if (status == FPGA_STATUS_BUSY) {
			fail_on(ret = (retries >= timeout_tmp) ? -ETIMEDOUT : 0, out, 
					"fpga_mgmt_describe_local_image timed out, status=%s(%d), retries=%u",
					FPGA_STATUS2STR(status), status, retries);
			retries++;
			msleep(delay_msec_tmp);
		} else {
			/** 
			 * Catch error status cases here.
			 *  -the caller can then display the error status and cause upon return.
			 */
			ret = tmp_info.status_q;
			goto out;
		}
	}

	/**
	 * Do not perform a remove/rescan of the APP PF if the SH version and PCI IDs
	 * have not changed.
	 */
	struct afi_device_ids *afi_device_ids = &tmp_info.ids.afi_device_ids;
	ret = fpga_mgmt_get_sh_version(slot_id, &sh_version);
	fail_on(ret != 0, out, "fpga_mgmt_get_sh_version failed");

	if ((sh_version != prev_sh_version) ||
		!((afi_device_ids->vendor_id == app_map.vendor_id) &&
			(afi_device_ids->device_id == app_map.device_id) &&
			(afi_device_ids->svid == app_map.subsystem_vendor_id) &&
			(afi_device_ids->ssid == app_map.subsystem_device_id))) {
		/** 
		 * Perform a PCI device remove and recan in order to expose the default AFI 
		 * Vendor and Device Id.
		 */
		log_info("remove+rescan required, sh_version=0x%08x, prev_sh_version=0x%08x, "
				"expected_ids={0x%04x, 0x%04x, 0x%04x, 0x%04x}, "
				"sysfs_ids={0x%04x, 0x%04x, 0x%04x, 0x%04x}",
				sh_version, prev_sh_version,
				afi_device_ids->vendor_id, afi_device_ids->device_id, 
				afi_device_ids->svid, afi_device_ids->ssid,
				app_map.vendor_id, app_map.device_id, 
				app_map.subsystem_vendor_id, app_map.subsystem_device_id);

		ret = fpga_pci_rescan_slot_app_pfs(slot_id);
		fail_on(ret, out, "fpga_pci_rescan_slot_app_pfs failed");
	}

	if (info) {
		*info = tmp_info;
	}
out:
	return ret;
}

int fpga_mgmt_load_local_image(int slot_id, char *afi_id)
{
	return fpga_mgmt_load_local_image_flags(slot_id, afi_id, 0);
}

int fpga_mgmt_init_load_local_image_options(union fpga_mgmt_load_local_image_options *opt){
	memset(opt, 0, sizeof(union fpga_mgmt_load_local_image_options));
	return 0;
}

int fpga_mgmt_load_local_image_flags(int slot_id, char *afi_id, uint32_t flags)
{
	union fpga_mgmt_load_local_image_options opt;

	fpga_mgmt_init_load_local_image_options(&opt);
	opt.slot_id = slot_id;
	opt.afi_id = afi_id;
	opt.flags = flags;

	return fpga_mgmt_load_local_image_with_options(&opt);
}

int fpga_mgmt_load_local_image_with_options(union fpga_mgmt_load_local_image_options *opt){
	int ret;
	uint32_t len;
	union afi_cmd cmd;
	union afi_cmd rsp;

	fail_slot_id(opt->slot_id, out, ret);

	memset(&cmd, 0, sizeof(union afi_cmd));
	memset(&rsp, 0, sizeof(union afi_cmd));

	/* initialize the command structure */
	fpga_mgmt_cmd_init_load(&cmd, &len, opt);

	/* send the command and wait for the response */
	ret = fpga_mgmt_process_cmd(opt->slot_id, &cmd, &rsp, &len);
	fail_on(ret, out, "fpga_mgmt_process_cmd failed");

	/* the load command does not have an interesting response payload */
out:
	return ret;
}

int fpga_mgmt_load_local_image_sync(int slot_id, char *afi_id,
		uint32_t timeout, uint32_t delay_msec,
		struct fpga_mgmt_image_info *info) 
{
	return fpga_mgmt_load_local_image_sync_flags(slot_id, afi_id, 0,
		timeout, delay_msec, info);
}

int fpga_mgmt_load_local_image_sync_flags(int slot_id, char *afi_id, uint32_t flags,
		uint32_t timeout, uint32_t delay_msec,
		struct fpga_mgmt_image_info *info) 
{
	union fpga_mgmt_load_local_image_options opt;

	fpga_mgmt_init_load_local_image_options(&opt);
	opt.slot_id = slot_id;
	opt.afi_id = afi_id;
	opt.flags = flags;

	return fpga_mgmt_load_local_image_sync_with_options(&opt, timeout, delay_msec, info);

}
int fpga_mgmt_load_local_image_sync_with_options(union fpga_mgmt_load_local_image_options *opt,
		uint32_t timeout, uint32_t delay_msec,
		struct fpga_mgmt_image_info *info) 
{
	struct fpga_mgmt_image_info tmp_info;
	struct fpga_pci_resource_map app_map;
	uint32_t prev_sh_version = 0;
	uint32_t sh_version = 0;
	uint32_t retries = 0;
	bool done = false;
	int status;
	int ret;

	/** Allow timeout adjustments that are greater than the defaults */
	uint32_t timeout_tmp = (timeout > FPGA_MGMT_SYNC_TIMEOUT) ?
		timeout : FPGA_MGMT_SYNC_TIMEOUT;
	uint32_t delay_msec_tmp = (delay_msec > FPGA_MGMT_SYNC_DELAY_MSEC) ?
		delay_msec : FPGA_MGMT_SYNC_DELAY_MSEC;

	memset(&tmp_info, 0, sizeof(tmp_info));
	
	/** 
	 * Get the current SH version and PCI resource map for the app_pf 
	 * that will be used after the load has completed.
	 */
	ret = fpga_mgmt_get_sh_version(opt->slot_id, &prev_sh_version);
	fail_on(ret != 0, out, "fpga_mgmt_get_sh_version failed");

	ret = fpga_pci_get_resource_map(opt->slot_id, FPGA_APP_PF, &app_map);
	fail_on(ret != 0, out, "fpga_pci_get_resource_map failed");

	/** Load the FPGA image (async completion) */
	ret = fpga_mgmt_load_local_image_with_options(opt);
	fail_on(ret, out, "fpga_mgmt_load_local_image failed");

	/** Wait until the status is "loaded" or timeout */
	while (!done) {
		ret = fpga_mgmt_describe_local_image(opt->slot_id, &tmp_info, 0); /** flags==0 */

		status = (ret == 0) ? tmp_info.status : FPGA_STATUS_END;
		if (status == FPGA_STATUS_LOADED) {
			/** Sanity check the afi_id */
			ret = (strncmp(opt->afi_id, tmp_info.ids.afi_id, sizeof(tmp_info.ids.afi_id))) ? 
				FPGA_ERR_FAIL : 0; 
			fail_on(ret, out, "AFI ID mismatch: requested afi_id=%s, loaded afi_id=%s",
					opt->afi_id, tmp_info.ids.afi_id);
			done = true;
		} else if (status == FPGA_STATUS_BUSY) {
			fail_on(ret = (retries >= timeout_tmp) ? -ETIMEDOUT : 0, out, 
					"fpga_mgmt_describe_local_image timed out, status=%s(%d), retries=%u",
					FPGA_STATUS2STR(status), status, retries);
			retries++;
			msleep(delay_msec_tmp);
		} else {
			/** 
			 * Catch error status cases here.
			 *  -the caller can then display the error status and cause upon return.
			 */
			ret = tmp_info.status_q;
			goto out;
		}
	}

	/**
	 * Do not perform a remove/rescan of the APP PF if the SH version and PCI IDs
	 * have not changed.
	 */
	struct afi_device_ids *afi_device_ids = &tmp_info.ids.afi_device_ids;
	ret = fpga_mgmt_get_sh_version(opt->slot_id, &sh_version);
	fail_on(ret != 0, out, "fpga_mgmt_get_sh_version failed");

	if ((sh_version != prev_sh_version) ||
		!((afi_device_ids->vendor_id == app_map.vendor_id) &&
			(afi_device_ids->device_id == app_map.device_id) &&
			(afi_device_ids->svid == app_map.subsystem_vendor_id) &&
			(afi_device_ids->ssid == app_map.subsystem_device_id))) {
		/** 
		 * Perform a PCI device remove and recan in order to expose the unique AFI 
		 * Vendor and Device Id.
		 */
		log_info("remove+rescan required, sh_version=0x%08x, prev_sh_version=0x%08x, "
				"expected_ids={0x%04x, 0x%04x, 0x%04x, 0x%04x}, "
				"sysfs_ids={0x%04x, 0x%04x, 0x%04x, 0x%04x}",
				sh_version, prev_sh_version,
				afi_device_ids->vendor_id, afi_device_ids->device_id, 
				afi_device_ids->svid, afi_device_ids->ssid,
				app_map.vendor_id, app_map.device_id, 
				app_map.subsystem_vendor_id, app_map.subsystem_device_id);

		ret = fpga_pci_rescan_slot_app_pfs(opt->slot_id);
		fail_on(ret, out, "fpga_pci_rescan_slot_app_pfs failed");
	}

	if (info) {
		*info = tmp_info;
	}
out:
	return ret;
}

int fpga_mgmt_get_vLED_status(int slot_id, uint16_t *status) 
{
	pci_bar_handle_t led_pci_bar;
	uint32_t read_data;
	int ret;

	ret = fpga_pci_attach(slot_id, FPGA_MGMT_PF, MGMT_PF_BAR0, 0, &led_pci_bar);
	fail_on(ret, out, "fpga_pci_attach failed");
	
	ret = fpga_pci_peek(led_pci_bar, F1_VIRTUAL_LED_REG_OFFSET, &read_data);
	fail_on(ret, out, "fpga_pci_peek failed");

	/* All this code assumes little endian, it would need rework for supporting non x86/arm platforms */
	*status = (uint16_t)(read_data & 0x0000FFFF);

	ret = fpga_pci_detach(led_pci_bar);
	fail_on(ret, out, "fpga_pci_detach failed");
out:
	return ret;	
}

int fpga_mgmt_set_vDIP(int slot_id, uint16_t value) 
{
	pci_bar_handle_t dip_pci_bar;
	uint32_t write_data;
	int ret;

	ret = fpga_pci_attach(slot_id, FPGA_MGMT_PF, MGMT_PF_BAR0, 0, &dip_pci_bar);
	fail_on(ret, out, "fpga_pci_attach failed");

	write_data = (uint32_t) value;

	ret = fpga_pci_poke(dip_pci_bar, F1_VIRTUAL_DIP_REG_OFFSET, write_data);
	fail_on(ret, out, "fpga_pci_poke failed");

	ret = fpga_pci_detach(dip_pci_bar);
	fail_on(ret, out, "fpga_pci_detach failed");
out:
	return ret;
}

int fpga_mgmt_get_vDIP_status(int slot_id, uint16_t *value) 
{
	pci_bar_handle_t dip_pci_bar;
	uint32_t read_data;
	int ret;

	ret = fpga_pci_attach(slot_id, FPGA_MGMT_PF, MGMT_PF_BAR0, 0, &dip_pci_bar);
	fail_on(ret, out, "fpga_pci_attach failed");

	ret = fpga_pci_peek(dip_pci_bar, F1_VIRTUAL_DIP_REG_OFFSET, &read_data);
	fail_on(ret, out, "fpga_pci_peek failed");

	/* All this code assumes little endian, it would need rework for supporting non x86/arm platforms */
	*value = (uint16_t)read_data; 

	ret = fpga_pci_detach(dip_pci_bar);
	fail_on(ret, out, "fpga_pci_detach failed");
out:
	return ret;
}
