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

#pragma once

#include <stdbool.h>
#include <fpga_common.h>
#include <fpga_pci.h>

/**
 * Initialize the fpga_mgmt library.
 * Calls fpga_pci_init.
 * @returns
 * 0 on success
 * -1 on failure
 */
int fpga_mgmt_init(void);

int fpga_mgmt_close(void);

/**
 * Sets the command timeout value in multiples of the delay_msec value.
 *
 * @param[in] value timeout, n * delay_msec
 */
void fpag_mgmt_set_cmd_timeout(uint32_t value);

/**
 *
 */
void fpag_mgmt_set_cmd_delay_msec(uint32_t value);

/* fpga-describe-local-image */

/**
 * This structure provides all of the information for
 * fpga_mgmt_describe_local_image.
 */
struct fpga_mgmt_image_info {
	int status;
	int slot_id;
	struct fpga_meta_ids  ids;
	struct fpga_slot_spec spec;
	uint32_t sh_version;
	struct fpga_metrics_common metrics;
};

/**
 * Gets a collection of information about a slot. It populates a
 * struct fpga_mgmt_image_info.
 *
 * @param[in]  slot_id  the logical slot index
 * @param[out] info     struct to populate with the slot description
 * @returns 0 on success, non-zero on error
 */
int fpga_mgmt_describe_local_image(int slot_id, struct fpga_mgmt_image_info *info);

/**
 * Gets the status of an FPGA. Status values are definted in enum fpga_status.
 * If you need the AFI id at the same time, use fpga_mgmt_describe_local_image.
 *
 * @param[in]  slot_id  the logical slot index
 * @param[out] status   populated with status value
 * @returns 0 on success, non-zero on error
 */
int fpga_mgmt_get_status(int slot_id, int *status);

/**
 * Maps status codes provided by fpga_mgmt_get_status to a human readable
 * string.
 *
 * @param[in]  status   status code to map
 * @returns string containing the human readable form of the status code
 */
const char *fpga_mgmt_get_status_name(int status);

/* fpga-clear-local-image */
/**
 * Clears the specified FPGA image slot, including FPGA internal and external
 * memories that are used by the slot.
 *
 * @param[in]  slot_id  the logical slot index
 * @returns 0 on success, non-zero on error
 */
int fpga_mgmt_clear_local_image(int slot_id);

/* fpga-load-local-image */
/**
 * Loads the specified FPGA image to the specified slot number.
 *
 * @param[in]  slot_id  the logical slot index
 * @param[in]  afi_id   The Amazon FGPA Image id to be loaded
 * @returns 0 on success, non-zero on error
 */
int fpga_mgmt_load_local_image(int slot_id, char *afi_id);

/**
 * getting the status of the 16 virtual LED
 */
int fpga_mgmt_get_vLED_status(int slot_id, uint16_t *status);

/**
 * set the value for the 16 virtual DIP switchs
 */
int fpga_mgmt_set_vDIP(int slot_id, uint16_t value);

/**
 * get the value for the 16 virtual DIP switchs
 */
int fpga_mgmt_get_vDIP_status(int slot_id, uint16_t *);

/**
 * state: enabled, disabled, error if not supported
 */
int fpga_mgmt_get_virtual_jtag_state(int slot_id, bool *enabled);

/**
 * enable/disable
 */
int fpga_mgmt_set_virtual_jtag(int slot_id);
