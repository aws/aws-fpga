/*
 * Copyright 2015-2016 Amazon.com, Inc. or its affiliates. All Rights Reserved.
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

/** @file
 * EC2_CMD_F1
 */

#pragma once

#include <afi_cmd_api.h>

#define CLI_VERSION  "v5.00"
 
/** First flag bit, @see afi_cmd_hdr#len_flags */
#define AFI_CMD_HDR_FLAGS_SHIFT 24

/** Mask to get the length portion, @see afi_cmd_hdr#len_flags */
#define AFI_CMD_HDR_LEN_MASK    ((1 << AFI_CMD_HDR_FLAGS_SHIFT) - 1)

/** Max retriees for draining presumed stale AFI commands */
#define AFI_MAX_ID_RETRIES		1

/**
 * AFI cmd extension
 */
enum {
	AFI_EXT_DESCRIBE_SLOTS = AFI_CMD_END,
	AFI_START_VJTAG,
	AFI_GET_LED,
	AFI_GET_DIP,
	AFI_SET_DIP,
	AFI_EXT_END
};

/** F1 Mailbox PF defines */
#define F1_MBOX_VENDOR_ID		0x1d0f
#define F1_MBOX_DEVICE_ID		0x1041
#define F1_MBOX_RESOURCE_NUM	0

/** F1 Application PF defines */
#define F1_APP_PF_START			0
#define F1_APP_PF_END			15

/** 
 * Generally, we allow a sanitized first level error to be displayed
 * for the user.  We do not want low-level mailbox related errors
 * to be displayed (since we are abstracting the mailbox interface).
 * The fail_on_quiet define allows the multi-level trace debug info
 * to still be displayed for development if needed, by re-defining
 * fail_on_quiet as fail_on.
 */
#define fail_on_quiet fail_on_user
// #define fail_on_quiet(CONDITION, LABEL, ...)	\
// 	do {					\
// 		if (CONDITION) {	\
// 			goto LABEL;		\
// 		}					\
// 	} while (0)

/** 
 * This should be used for the sanitized first level errors to be
 * displayed for the user.
 */
#define fail_on_user(CONDITION, LABEL, ...)	\
	do {							\
		if (CONDITION) {			\
			printf(__VA_ARGS__);	\
			printf("\n");			\
			goto LABEL;				\
		}							\
	} while (0)

/** 
 * This should be used for sanitized first level internal errors
 * to be displayed to the user.
 * We're only providing the line number and not the routine name
 * because we're abstracting the mailbox interface and all that
 * goes along with it.
 */
#define CLI_INTERNAL_ERR_STR "Error: Internal error "
#define fail_on_internal(CONDITION, LABEL, ...)	\
	do {										\
		if (CONDITION) {						\
			printf(__VA_ARGS__);				\
			printf("(line %u)\n", __LINE__);	\
			goto LABEL;							\
		}										\
	} while (0)

/** Common string for sudo/root access */
#define CLI_ROOT_ACCESS_ERR_STR \
	"Error: Please prefix the command with 'sudo' or login as root"

/**
 * Default timeout:
 *   CLI_TIMEOUT_DFLT * CLI_DELAY_MSEC_DFLT
 */
#define CLI_TIMEOUT_DFLT   	25
#define CLI_DELAY_MSEC_DFLT	200	

/**
 * ec2_fpga_cmd:
 */
struct ec2_fpga_cmd {
	uint32_t slot_dev_index;
	struct fpga_slot_spec mbox_slot_devs[FPGA_SLOT_MAX]; /* todo: do we need this still? */
	uint32_t opcode;
	uint32_t afi_slot;
	char	 afi_id[AFI_ID_STR_MAX];
	uint32_t mbox_timeout;
	uint32_t mbox_delay_msec;
	bool	 plat_attached;
	bool	 show_headers;
	bool	 get_hw_metrics;
	bool	 clear_hw_metrics;
	bool	 rescan;
	bool     show_mbox_device;
	uint16_t v_dip_switch;
	char*    tcp_port;
};

extern struct ec2_fpga_cmd f1;

/**
 * Parse command line arguments.
 *
 * @param[in]   argc    Argument count.
 * @param[in]   argv    Argument string vector.
 */
int 
parse_args(int argc, char *argv[]);

/**
 * Initialize the AFI slot devices from the PCI/sysfs layer. 
 *
 * @returns
 *  0   on success 
 * -1   on failure
 */
int cli_pci_init(void);

/**
 * De-initialize the PCI/sysfs layer.
 */
void cli_pci_free(void);

/**
 * Retrieve the application PF map for the given mbox slot.
 *
 * @param[in]   slot		the fpga slot
 * @param[in]   app_pf_num	the application PF number to check 
 * @param[out]  map			the application PF resource map to return 
 *
 * @returns
 *  0	on success 
 * -1	on failure
 */
int cli_get_app_pf_map(uint32_t slot, uint32_t app_pf_num, 
		struct fpga_pci_resource_map *map);

/**
 * Remove the application PF for the given mbox slot.
 *
 * @param[in]   slot		the fpga slot
 * @param[in]   app_pf_num	the application PF number to check 
 *
 * @returns
 *  0	on success 
 * -1	on failure
 */
int
cli_remove_app_pf(uint32_t slot, uint32_t app_pf_num);

/**
 * PCI rescan.
 *
 * @returns
 *  0	on success 
 * -1	on failure
 */
int
cli_pci_rescan(void);
