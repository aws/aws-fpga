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
 * EC2 F1 CLI parsing and associated help text.
 */

#include <assert.h>
#include <limits.h>
#include <sys/types.h>
#include <stdlib.h>
#include <string.h>
#include <sys/errno.h>
#include <stdio.h>
#include <getopt.h>

#include <lcd.h>

#include <fpga_common.h>

#include "fpga_local_cmd.h"

#define MSEC_PER_SEC 1000

/**
 * Usage defines for use with print_usage.
 */
static const char *opcode_str_usage[] = {
	"  SYNOPSIS",
	"     fpga-local-cmd [GENERAL OPTIONS] [-h]",
	"  DESCRIPTION",
	"     This program is normally executed via the wrapper scripts.",
	"     See fpga-load-local-image, fpga-clear-local-image,",
	"     fpga-describe-local-image, fpga-describe-local-image-slots.",
	"  GENERAL OPTIONS",
	"     LoadFpgaImage, ClearFpgaImage, DescribeFpgaImage,",
	"     DescribeFpgaImageSlots",
};

static const char *describe_afi_slots_usage[] = {
    "  SYNOPSIS",
	"      fpga-describe-local-image-slots [GENERAL OPTIONS] [-h]",
	"      Example: fpga-describe-local-image-slots",
	"  DESCRIPTION",
	"      Returns the FPGA image slot numbers and device mappings to use for",
	"      the fpga-load-local-image, fpga-clear-local-image, and",
	"      fpga-describe-local-image commands.",
	"  GENERAL OPTIONS",
	"      -?, --help",
    "          Display this help.",
	"      -H, --headers",
	"          Display column headers.",
	"      -V, --version",
	"          Display version number of this program.",
	"      --request-timeout TIMEOUT",
	"          Specify a request timeout TIMEOUT (in seconds).",
};

static const char *describe_afi_usage[] = {
	"  SYNOPSIS",
	"      fpga-describe-local-image [GENERAL OPTIONS] [-h]",
	"      Example: fpga-describe-local-image -S 0",
	"  DESCRIPTION",
	"      Returns the status of the FPGA image for a specified FPGA image",
	"      slot number. The fpga-image-slot parameter is a logical index that",
	"      represents a given FPGA within an instance.",
	"      Use fpga-describe-local-image-slots to return the available FPGA",
	"      image slots for the instance.",
	"  GENERAL OPTIONS",
	"      -S, --fpga-image-slot",
	"          The logical slot number for the FPGA image.",
	"          Constraints: Positive integer from 0 to the total slots minus 1.",
	"      -R  --rescan",
	"          Rescan the AFIDEVICE to update the per-AFI PCI VendorId and",
	"          DeviceId that may be dynamically modified due to a",
	"          fpga-load-local-image or fpga-clear-local-image command.",
	"          NOTE1: this option removes the AFIDEVICE from the sysfs PCI", 
	"          subsystem and then rescans the PCI subsystem in order for",
	"          the modified AFI PCI IDs to be refreshed.",
	"          NOTE2: it is the developer's responsibility to remove any", 
	"          driver priviously installed on the older PCIe VendorId",
	"          and DeviceId before fpga-clear-local-image,",
	"          fpga-load-local-image, or re-scan.",
	"      -?, --help",
	"          Display this help.",
	"      -H, --headers",
	"          Display column headers.",
	"      -V, --version",
	"          Display version number of this program.",
	"      --request-timeout TIMEOUT",
	"          Specify a request timeout TIMEOUT (in seconds).",
};

static const char *load_afi_usage[] = {
	"  SYNOPSIS",
	"      fpga-load-local-image [GENERAL OPTIONS] [-h]",
	"      Example: fpga-load-local-image -S 0 -I <fpga-image-id>",
	"  DESCRIPTION",
	"      Loads the specified FPGA image to the specified slot number, and",
	"      returns the status of the command.  The fpga-image-slot parameter",
	"      is a logical index that represents a given FPGA within an instance.",
	"      Use fpga-describe-local-image to return the FPGA image status, and",
	"      fpga-describe-local-image-slots to return the available FPGA image",
	"      slots for the instance.",
	"  GENERAL OPTIONS",
	"      -S, --fpga-image-slot",
	"          The logical slot number for the FPGA image",
	"          Constraints: Positive integer from 0 to the total slots minus 1.",
	"      -I, --fpga-image-id",
	"          The ID of the FPGA image. agfi-<number>",
	"      -?, --help",
	"          Display this help.",
	"      -H, --headers",
	"          Display column headers.",
	"      -V, --version",
	"          Display version number of this program.",
	"      --request-timeout TIMEOUT",
	"          Specify a request timeout TIMEOUT (in seconds).",
};

static const char *clear_afi_usage[] = {
	"  SYNOPSIS",
	"      fpga-clear-local-image [GENERAL OPTIONS] [-h]",
	"      Example: fpga-clear-local-image -S 0",
	"  DESCRIPTION",
	"      Clears the specified FPGA image slot, including FPGA internal and",
	"      external memories that are used by the slot. The fpga-image-slot",
	"      parameter is a logical index that represents a given FPGA within",
	"      an instance.",
	"      Use fpga-describe-local-image to return the FPGA image status, and",
	"      fpga-describe-local-image-slots to return the available FPGA image",
	"      slots for the instance.",
	"  GENERAL OPTIONS",
	"      -S, --fpga-image-slot",
	"          The logical slot number for the FPGA image.",
	"          Constraints: Positive integer from 0 to the total slots minus 1.",
	"      -?, --help",
	"          Display this help.",
	"      -H, --headers",
	"          Display column headers.",
	"      -V, --version",
	"          Display version number of this program.",
	"      --request-timeout TIMEOUT",
	"          Specify a request timeout TIMEOUT (in seconds).",
};

/**
 * Generic usage printing engine. 
 *
 * @param[in]	prog_name		program name
 * @param[in]   usage			usage array of strings
 * @param[in]   num_entries		number of entries in the usage array of strings
 */
static void 
print_usage(const char *prog_name, const char *usage[], size_t num_entries)
{   
	(void)prog_name;

	size_t i;
	for (i = 0; i < num_entries; i++) {
		printf("%s\n", usage[i]);
	}
}

/**
 * Print the version number of this program. 
 */
static void 
print_version(void)
{   
	printf("AFI Management Tools Version: %s\n", CLI_VERSION);
	printf("AFI CMD API Version: v%u\n", AFI_CMD_API_VERSION);
}

/**
 * Configure the request timeout
 *
 * @param[in]   timeout		timeout in seconds
 *
 * @returns
 *  0   on success 
 * -1   on failure
 */
static int
config_request_timeout(uint32_t timeout)
{
	size_t timeout_tmp = 
			CLI_TIMEOUT_DFLT * CLI_DELAY_MSEC_DFLT / MSEC_PER_SEC;
	size_t timeout_max = 
			((size_t)(uint32_t)-1) * CLI_DELAY_MSEC_DFLT / MSEC_PER_SEC;

	/** Check min and max values */
	fail_on_user((timeout < timeout_tmp) || (timeout > timeout_max), err, 
			"Error: The timeout must be between %zu and %zu seconds",
			timeout_tmp, timeout_max);

	timeout_tmp = ((size_t)timeout) * MSEC_PER_SEC / CLI_DELAY_MSEC_DFLT;
	if (timeout_tmp > (uint32_t)-1) {
		/** Sanity check: Max out at ((1 << 32) - 1) * CLI_DELAY_MSEC_DFLT */
		timeout_tmp = (uint32_t)-1;
	}

	f1.mbox_timeout = timeout_tmp;

	log_debug("Setting timeout to %u secs, mbox_timeout=%u, mbox_delay_msec=%u", 
			timeout, f1.mbox_timeout, f1.mbox_delay_msec);
	return 0;
err:
	return -1;
}

/**
 * Parse load-fpga-image command line arguments.
 *
 * @param[in]   argc    Argument count.
 * @param[in]   argv    Argument string vector.
 */
static int 
parse_args_load_afi(int argc, char *argv[])
{
	int opt = 0;

	static struct option long_options[] = {
		{"fpga-image-slot",		required_argument,	0,	'S'	},
		{"fpga-image-id",		required_argument,	0,	'I'	},
		{"request-timeout",		required_argument,	0,	'r'	},
		{"headers",				no_argument,		0,	'H'	},
		{"help",				no_argument,		0,	'?'	},
		{"version",				no_argument,		0,	'V'	},
		{0,						0,					0,	0	},
	};

	int long_index = 0;
	while ((opt = getopt_long(argc, argv, "S:I:r:H?hV",
			long_options, &long_index)) != -1) {
		switch (opt) {
		case 'S': {
			string_to_uint(&f1.afi_slot, optarg);
			fail_on_user(f1.afi_slot >= FPGA_SLOT_MAX, err, "fpga-image-slot must be less than %u", 
					FPGA_SLOT_MAX);
			break;
		}
		case 'I': {
		    fail_on_user(strnlen(optarg, AFI_ID_STR_MAX) == AFI_ID_STR_MAX, err,
					"fpga-image-id must be less than %u bytes", AFI_ID_STR_MAX);

			strncpy(f1.afi_id, optarg, sizeof(f1.afi_id)); 
			f1.afi_id[sizeof(f1.afi_id) - 1] = 0; 
			break;
		}
		case 'r': {
			uint32_t value32;
			string_to_uint(&value32, optarg);
			int ret = config_request_timeout(value32);
			fail_on_quiet(ret != 0, err, "Could not configure the request-timeout");
			break;
		}
		case 'H': {
			f1.show_headers = true;
			break;
		}
		case 'V': {
			print_version();
			goto out_ver;
		}
		default: {
			goto err;   
		}
		}
	}
	
	if ((f1.afi_slot == (uint32_t) -1) ||
		(f1.afi_id[0] == 0)) {
		goto err;
	}

	return 0;
err:
	print_usage(argv[0], load_afi_usage, sizeof_array(load_afi_usage));
out_ver:
	return -1;
}

/**
 * Parse clear-fpga-image command line arguments.
 *
 * @param[in]   argc    Argument count.
 * @param[in]   argv    Argument string vector.
 */
static int 
parse_args_clear_afi(int argc, char *argv[])
{
	int opt = 0;

	static struct option long_options[] = {
		{"fpga-image-slot",		required_argument,	0,	'S'	},
		{"request-timeout",		required_argument,	0,	'r'	},
		{"headers",				no_argument,		0,	'H'	},
		{"help",				no_argument,		0,	'?'	},
		{"version",				no_argument,		0,	'V'	},
		{0,						0,					0,	0	},
	};

	int long_index = 0;
	while ((opt = getopt_long(argc, argv, "S:r:H?hV",
			long_options, &long_index)) != -1) {
		switch (opt) {
		case 'S': {
			string_to_uint(&f1.afi_slot, optarg);
			fail_on_user(f1.afi_slot >= FPGA_SLOT_MAX, err, "fpga-image-slot must be less than %u", 
					FPGA_SLOT_MAX);
			break;
		}
		case 'r': {
			uint32_t value32;
			string_to_uint(&value32, optarg);
			int ret = config_request_timeout(value32);
			fail_on_quiet(ret != 0, err, "Could not configure the request-timeout");
			break;
		}
		case 'H': {
			f1.show_headers = true;
			break;
		}
		case 'V': {
			print_version();
			goto out_ver;
		}
		default: {
			goto err;   
		}
		}
	}
	
	if (f1.afi_slot == (uint32_t) -1) { 
		goto err;
	}

	return 0;
err:
	print_usage(argv[0], clear_afi_usage, sizeof_array(clear_afi_usage));
out_ver:
	return -1;
}

/**
 * Parse describe-fpga-image command line arguments.
 *
 * @param[in]   argc    Argument count.
 * @param[in]   argv    Argument string vector.
 */
static int 
parse_args_describe_afi(int argc, char *argv[])
{
	int opt = 0;

	static struct option long_options[] = {
		{"fpga-image-slot",		required_argument,	0,	'S'	},
		{"request-timeout",		required_argument,	0,	'r'	},
		{"rescan",				no_argument,		0,	'R'	},
		{"headers",				no_argument,		0,	'H'	},
		{"help",				no_argument,		0,	'?'	},
		{"version",				no_argument,		0,	'V'	},
		{0,						0,					0,	0	},
	};

	int long_index = 0;
	while ((opt = getopt_long(argc, argv, "S:r:RH?hV",
			long_options, &long_index)) != -1) {
		switch (opt) {
		case 'S': {
			string_to_uint(&f1.afi_slot, optarg);
			fail_on_user(f1.afi_slot >= FPGA_SLOT_MAX, err, 
					"fpga-image-slot must be less than %u", FPGA_SLOT_MAX);
			break;
		}
		case 'r': {
			uint32_t value32;
			string_to_uint(&value32, optarg);
			int ret = config_request_timeout(value32);
			fail_on_quiet(ret != 0, err, "Could not configure the request-timeout");
			break;
		}
		case 'R': {
			f1.rescan = true;
			break;
		}
		case 'H': {
			f1.show_headers = true;
			break;
		}
		case 'V': {
			print_version();
			goto out_ver;
		}
		default: {
			goto err;   
		}
		}
	}
	
	if (f1.afi_slot == (uint32_t) -1) { 
		goto err;
	}

	return 0;
err:
	print_usage(argv[0], describe_afi_usage, sizeof_array(describe_afi_usage));
out_ver:
	return -1;
}

/**
 * Parse describe-fpga-image-slots command line arguments.
 *
 * @param[in]   argc    Argument count.
 * @param[in]   argv    Argument string vector.
 */
static int 
parse_args_describe_afi_slots(int argc, char *argv[])
{
	int opt = 0;

	static struct option long_options[] = {
		{"request-timeout",		required_argument,	0,	'r'	},
		{"headers",				no_argument,		0,	'H'	},
		{"help",				no_argument,		0,	'?'	},
		{"version",				no_argument,		0,	'V'	},
		{0,						0,					0,	0	},
	};

	int long_index = 0;
	while ((opt = getopt_long(argc, argv, "r:H?hV",
			long_options, &long_index)) != -1) {
		switch (opt) {
		case 'r': {
			uint32_t value32;
			string_to_uint(&value32, optarg);
			int ret = config_request_timeout(value32);
			fail_on_quiet(ret != 0, err, "Could not configure the request-timeout");
			break;
		}
		case 'H': {
			f1.show_headers = true;
			break;
		}
		case 'V': {
			print_version();
			goto out_ver;
		}
		default: {
			goto err;   
		}
		}
	}
	
	return 0;
err:
	print_usage(argv[0], describe_afi_slots_usage, 
			sizeof_array(describe_afi_slots_usage));
out_ver:
	return -1;
}

typedef int (*parse_args_func_t)(int argc, char *argv[]);

struct parse_args_str2func {
	char				*str;
	uint32_t			 opcode;
	parse_args_func_t	 func;
};

/**
 * Parse command line arguments.
 *
 * @param[in]   argc    Argument count.
 * @param[in]   argv    Argument string vector.
 */
int 
parse_args(int argc, char *argv[])
{
	fail_on_quiet(argc < 2, err, "Error: opcode string must be specified");
	fail_on_user(!argv[0] || !argv[1], err, 
			"Error: program name or opcode string is NULL");

	static struct parse_args_str2func str2func[] = {
		{"LoadFpgaImage",			AFI_CMD_LOAD,			parse_args_load_afi},
		{"ClearFpgaImage",			AFI_CMD_CLEAR,			parse_args_clear_afi},
		{"DescribeFpgaImageSlots",	AFI_EXT_DESCRIBE_SLOTS,	parse_args_describe_afi_slots},
		{"DescribeFpgaImage",		AFI_CMD_METRICS,		parse_args_describe_afi},
	};

	char *opcode_str = argv[1];
	size_t i;
	int ret = -1;
	for (i = 0; i < sizeof_array(str2func); i++) {
		struct parse_args_str2func *entry = &str2func[i];

		if (!strncmp(entry->str, opcode_str, strlen(entry->str))) {
			f1.opcode = entry->opcode;
			ret = entry->func(argc, argv);
			break;
		}
	}

	if (f1.opcode == (uint32_t)-1) {
		goto err;
	}

	return ret;
err:
	print_usage(argv[0], opcode_str_usage, sizeof_array(opcode_str_usage));
	return -1;
}
