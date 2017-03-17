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
	.timeout = FPAG_MGMT_TIMEOUT_DFLT,
	.delay_msec = FPAG_MGMT_DELAY_MSEC_DFLT
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

	fail_slot_id(slot_id, out, ret);

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
	info->status = metrics->status;
	info->slot_id = slot_id;

	char *afi_id = (!metrics->ids.afi_id[0]) ? "none" : metrics->ids.afi_id;
	info->ids = metrics->ids;
	strncpy(info->ids.afi_id, afi_id, sizeof(info->ids.afi_id));

	struct fpga_hal_mbox_versions ver;
	ret = fpga_hal_mbox_get_versions(&ver);
	fail_on(ret, out, "fpga_hal_mbox_get_versions failed");
	info->sh_version = ver.sh_version;

	ret = fpga_pci_get_slot_spec(slot_id, &info->spec);
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

	fail_slot_id(slot_id, out, ret);

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
	return FPGA_STATUS2STR(status);
}

int fpga_mgmt_clear_local_image(int slot_id) {
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

int fpga_mgmt_load_local_image(int slot_id, char *afi_id) {
	int ret;
	uint32_t len;
	union afi_cmd cmd;
	union afi_cmd rsp;

	fail_slot_id(slot_id, out, ret);

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
	int ret;
	pci_bar_handle_t	led_pci_bar;
	uint32_t	read_data;

	ret=fpga_pci_attach(slot_id, FPGA_MGMT_PF, MGMT_PF_BAR0, 0, &led_pci_bar);
	if (ret) 
		return -1;
	
	ret = fpga_pci_peek(led_pci_bar,F1_VIRTUAL_LED_REG_OFFSET,&read_data);
       /* All this code assumes little endian, it would need rework for supporting non x86/arm platforms */
        *(status) = (uint16_t)( read_data & 0x0000FFFF);


	fpga_pci_detatch(led_pci_bar);
	return ret;	
}

int fpga_mgmt_set_vDIP(int slot_id, uint16_t value) {
        int ret;
        pci_bar_handle_t        dip_pci_bar;
        uint32_t        write_data;

        ret=fpga_pci_attach(slot_id, FPGA_MGMT_PF, MGMT_PF_BAR0, 0, &dip_pci_bar);
        if (ret)
                return -1;


	write_data = (uint32_t) value;

        ret = fpga_pci_poke(dip_pci_bar,F1_VIRTUAL_DIP_REG_OFFSET,write_data);


        fpga_pci_detatch(dip_pci_bar);
        return ret;
}

int fpga_mgmt_get_vDIP_status(int slot_id, uint16_t *value) {

        int ret;
        pci_bar_handle_t        dip_pci_bar;
        uint32_t        read_data;

        ret=fpga_pci_attach(slot_id, FPGA_MGMT_PF, MGMT_PF_BAR0, 0, &dip_pci_bar);
        if (ret)
                return -1;

        ret = fpga_pci_peek(dip_pci_bar,F1_VIRTUAL_DIP_REG_OFFSET,&read_data);
       /* All this code assumes little endian, it would need rework for supporting non x86/arm platforms */
	 *(value) = (uint16_t)read_data; 

        fpga_pci_detatch(dip_pci_bar);
        return ret;

}
