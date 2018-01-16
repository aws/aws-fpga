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

#define CLI_VERSION  "v6.00"
 
/**
 * CLI cmds
 */
enum {
	CLI_CMD_LOAD,
	CLI_CMD_CLEAR,
	CLI_CMD_DESCRIBE,
	CLI_CMD_DESCRIBE_SLOTS,
	CLI_CMD_START_VJTAG,
	CLI_CMD_GET_LED,
	CLI_CMD_GET_DIP,
	CLI_CMD_SET_DIP,
	CLI_CMD_END
};

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

/** Common string for sudo/root access */
#define CLI_ROOT_ACCESS_ERR_STR \
	"Error: Please prefix the command with 'sudo' or login as root"

/**
 * Default synchronous API timeout:
 * e.g. load + describe multi-AFI command sequences.
 *  timeout * delay_msec 
 */
#define CLI_SYNC_TIMEOUT_DFLT		300	
#define CLI_SYNC_DELAY_MSEC_DFLT	200	

/**
 * Request timeout: timeout * delay_msec
 */
#define CLI_REQUEST_TIMEOUT_DFLT   	50
#define CLI_REQUEST_DELAY_MSEC_DFLT	200	

/**
 * ec2_fpga_cmd:
 */
struct ec2_fpga_cmd {
	/** See CLI_CMD_XYZ */
	uint32_t opcode;
	/** The AFI slot */
	uint32_t afi_slot;
	/** Requested clock frequencies for each clock group */
	uint32_t clock_a0_freq;
	uint32_t clock_b0_freq;
	uint32_t clock_c0_freq;
	/** The AFI ID */
	char	 afi_id[AFI_ID_STR_MAX];
	/** 
	 * Synchronous API timeout (e.g. load + describe AFI command sequence): 
	 *  timeout * delay_msec 
	 */
	uint32_t sync_timeout;
	uint32_t sync_delay_msec;
	/** Request timeout for AFI commands: timeout * delay_msec */
	uint32_t request_timeout;
	uint32_t request_delay_msec;
	/** Indicates if the parser itself fully completed the command */
	bool	 parser_completed;	
	/** Asynchronous operations */
	bool	 async;
	/** Show headers option */
	bool	 show_headers;
	/** Metrics options */
	bool	 get_hw_metrics;
	bool	 clear_hw_metrics;
	/** Rescan option */
	bool	 rescan;
	/** Show mailbox device option */
	bool     show_mbox_device;
	/** Reload the shell even if not required for AFI */
	bool     force_shell_reload;
	/** Virtual DIP switch */
	uint16_t v_dip_switch;
	/** Virtual JTAG TCP port */
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
