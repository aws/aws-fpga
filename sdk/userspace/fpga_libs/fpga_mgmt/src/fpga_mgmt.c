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


#include <fpga_libs/fpga_mgmt.h>
#include <fpga_libs/fpga_pci.h>

int fpga_mgmt_init(void) {
	return fpga_pci_init();
}


int fpga_mgmt_describe_local_image(int slot_id, struct fpga_mgmt_image_info *info) {
	/* not implemented */
	return 1;
}

/**
 * Gets the status of an FPGA. Status values are definted in enum fpga_status.
 * If you need the AFI id at the same time, use fpga_mgmt_describe_local_image.
 *
 * @param[in]  slot_id  the logical slot index
 * @param[out] status   populated with status value
 * @returns 0 on success, non-zero on error
 */
int fpga_mgmt_get_status(int slot_id, int *status) {
	/* not implemented */
	return 1;
}

const char *fpga_mgmt_get_status_name(int status) {
	/* not implemented */
	return 1;
}

int fpga_mgmt_clear_local_image(int slot_id) {
	/* not implemented */
	return 1;
}

int fpga_mgmt_load_local_image(int slot_id, char *afi_id) {
	/* not implemented */
	return 1;
}

int fpga_mgmt_get_vLED_status(int slot_id, int *status) {
	/* not implemented */
	return 1;
}

int fpga_mgmt_set_vDIP(int slot_id, uint16_t value) {
	/* not implemented */
	return 1;
}

int fpga_mgmt_get_vDIP_status(int slot_id, uint16_t *value) {
	/* not implemented */
	return 1;
}

int fpga_mgmt_get_virtual_jtag_state(int slot_id, bool *enabled) {
	/* not implemented */
	return 1;
}

int fpga_mgmt_set_virtual_jtag(int slot_id, bool enabled) {
	/* not implemented */
	return 1;
}
