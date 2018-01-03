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

#include <hal/fpga_common.h>
#include <fpga_pci.h>

#ifdef __cplusplus
extern "C" {
#endif

/**
 * Initialize the fpga_mgmt library.
 * Calls fpga_pci_init.
 *
 * @returns 0 on success, non-zero on error
 */
int fpga_mgmt_init(void);

/**
 * Closes the fpga_mgmt library and its dependencies and releases any acquired
 * resources.
 *
 * @returns 0 on success, non-zero on error
 */
int fpga_mgmt_close(void);

/**
 * Get an error code string.
 *
 * @param[in] err  The error code to decode
 * @returns a string corresponding to the provided error code.
 */
const char *fpga_mgmt_strerror(int err);

/**
 * Sets the command timeout value in multiples of the delay_msec value.
 *
 * @param[in] value  timeout, n * delay_msec
 */
void fpga_mgmt_set_cmd_timeout(uint32_t value);

/**
 * Sets the value of the delay_msec. The value is used as the basic unit of time
 * used to calculate timeouts for communicating with the mailbox pf.
 *
 * @param[in] value  number of ms used as base time unit
 */
void fpga_mgmt_set_cmd_delay_msec(uint32_t value);

/**
 * This structure provides all of the information for
 * fpga_mgmt_describe_local_image.
 */
struct fpga_mgmt_image_info {
	/** FPGA status: see FPGA_STATUS_XYZ in fpga_common.h */
	int status;
	/** FPGA status qualifier: see FPGA_ERR_XYZ in fpga_common.h */
	int status_q;
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
 * @param[in]  flags    set flags for for metrics retrieval options
 * @returns 0 on success, non-zero on error
 */
int fpga_mgmt_describe_local_image(int slot_id,
	struct fpga_mgmt_image_info *info, uint32_t flags);

/**
 * Gets the status of an FPGA. 
 *
 * Status values are defined in fpga_common.h, see FPGA_STATUS_XYZ.
 * Status qualifier values are defined in fpga_common.h, see FPGA_ERR_XYZ.
 * If you need the AFI id at the same time, use fpga_mgmt_describe_local_image.
 *
 * @param[in]  slot_id    the logical slot index
 * @param[out] status     populated with status value
 * @param[out] status_q   populated with status qualifier value
 * @returns 0 on success, non-zero on error
 */
int fpga_mgmt_get_status(int slot_id, int *status, int *status_q);

/**
 * Maps status codes provided by fpga_mgmt_get_status to a human readable
 * string.
 *
 * @param[in]  status   status code to map
 * @returns string containing the human readable form of the status code
 */
const char *fpga_mgmt_get_status_name(int status);

/**
 * Asynchronously clears the specified FPGA image slot, including FPGA 
 * internal and external memories that are used by the slot.
 *
 * @param[in]  slot_id  the logical slot index
 * @returns 0 on success, non-zero on error
 */
int fpga_mgmt_clear_local_image(int slot_id);

/**
 * Synchronously clears the specified FPGA image slot, including FPGA 
 * internal and external memories that are used by the slot.
 * A user-specified timeout may be specified as: 
 *		timeout (retries) * delay_msec (polling period)
 *
 * @param[in]  slot_id	the logical slot index
 * @param[in]  timeout	the timeout retries
 * @param[in]  delay_msec the delay msec between timeout retries
 * @param[in/out]  info	struct to populate with the slot description (or NULL)
 * @returns 0 on success, non-zero on error
 */
int fpga_mgmt_clear_local_image_sync(int slot_id, 
		uint32_t timeout, uint32_t delay_msec,
		struct fpga_mgmt_image_info *info);


/**
 * Wrapper for fpga_mgmt_load_local_image_flags, with flags set to 0 as a default
 */
int fpga_mgmt_load_local_image(int slot_id, char *afi_id);

/**
 * Wrapper for fpga_mgmt_load_local_image_with_options, passing the slot_id, afi_id,
 * and flags in the opt structure, with other options set to defaults via
 * fpga_mgmt_init_load_local_image_options
*/
int fpga_mgmt_load_local_image_flags(int slot_id, char *afi_id, uint32_t flags);

/*
 * @param[in]  slot_id  the logical slot index
 * @param[in]  afi_id   The Amazon FGPA Image id to be loaded
 * @param[in]  flags   flags to select various options from Common FPGA
 *                     command flags
 * @param[in]  clock_mains	Requested values of the main clock, per group.
				Other clocks in the group will be set to low
				frequencies.
*/
union fpga_mgmt_load_local_image_options {
	uint8_t reserved[1024];
	struct {
		int slot_id;
		char* afi_id;
		uint32_t flags;
		uint32_t clock_mains[FPGA_MMCM_GROUP_MAX];
	};
};

int fpga_mgmt_init_load_local_image_options(union fpga_mgmt_load_local_image_options *opt);

/**
 * Asynchronously loads the specified FPGA image to the specified slot number.
 *
 * @param[in]  opt	See fpga_mgmt_load_local_image_options
 * @returns 0 on success, non-zero on error
 */
int fpga_mgmt_load_local_image_with_options(union fpga_mgmt_load_local_image_options *opt);

/**
 * Wrapper for fpga_mgmt_load_local_image_sync_flags, with flags set to 0 as a
 * default.
*/
int fpga_mgmt_load_local_image_sync(int slot_id, char *afi_id,
		uint32_t timeout, uint32_t delay_msec,
		struct fpga_mgmt_image_info *info);

/**
 * Wrapper for fpga_mgmt_load_local_image_sync_with_options, passing the slot_id, afi_id,
 * and flags in the opt structure, with other options set to defaults via
 * fpga_mgmt_init_load_local_image_options
*/
int fpga_mgmt_load_local_image_sync_flags(int slot_id, char *afi_id, uint32_t flags,
		uint32_t timeout, uint32_t delay_msec,
		struct fpga_mgmt_image_info *info);

/**
 * Synchronously loads the specified FPGA image slot to the specified slot 
 * number.
 * A user-specified timeout may be specified as: 
 *		timeout (retries) * delay_msec (polling period)
 *
 * @param[in]  opt	See fpga_mgmt_load_local_image_options
 * @param[in]  timeout	the timeout retries
 * @param[in]  delay_msec the delay msec between timeout retries
 * @param[in/out]  info	struct to populate with the slot description (or NULL)
 * @returns 0 on success, non-zero on error
 */
int fpga_mgmt_load_local_image_sync_with_options(union fpga_mgmt_load_local_image_options *opt,
		uint32_t timeout, uint32_t delay_msec,
		struct fpga_mgmt_image_info *info);

/**
 * Gets the status of the 16 virtual LEDs. Their statuses are returned as a
 * 16-bit value with each bit corresponding to the on/off state of the LEDs.
 *
 * @param[in]   slot_id  the logical slot index
 * @param[out]  status   16 bits describing the LED states
 * @returns 0 on success, non-zero on error
 */
int fpga_mgmt_get_vLED_status(int slot_id, uint16_t *status);

/**
 * Sets the status of the 16 virtual dip switches. Their statuses are set as a
 * 16-bit value with each bit corresponding to the on/off state of the switches.
 *
 * @param[in]  slot_id  the logical slot index
 * @param[in]  value    16 bits describing the switch states
 * @returns 0 on success, non-zero on error
 */
int fpga_mgmt_set_vDIP(int slot_id, uint16_t value);

/**
 * Gets the status of the 16 virtual dip switches. Their statuses are returned
 * as a 16-bit value with each bit corresponding to the on/off state of the
 * switches.
 *
 * @param[in]   slot_id  the logical slot index
 * @param[out]  value    16 bits describing the switch states
 * @returns 0 on success, non-zero on error
 */
int fpga_mgmt_get_vDIP_status(int slot_id, uint16_t *value);

#ifdef __cplusplus
}
#endif
