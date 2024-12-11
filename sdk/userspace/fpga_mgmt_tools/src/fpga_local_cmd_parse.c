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
 * EC2 F1 and F2 CLI parsing and associated help text.
 */

#include <assert.h>
#include <limits.h>
#include <sys/types.h>
#include <stdlib.h>
#include <string.h>
#include <sys/errno.h>
#include <stdio.h>
#include <getopt.h>

#include <fpga_mgmt.h>
#include <fpga_pci.h>
#include <utils/lcd.h>

#include "fpga_local_cmd.h"
#include "virtual_jtag.h"

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
	"     fpga-start-virtual-jtag, fpga-get-virtual-led",
	"     fpga-get-virtual-dip-switch, fpga-set-virtual-dip-switch",
	"  GENERAL OPTIONS",
	"     LoadFpgaImage, ClearFpgaImage, DescribeFpgaImage,",
	"     DescribeFpgaImageSlots, StartVirtualJtag, GetVirtualLED,",
	"     GetVirtualDIP, SetVirtualDIP",
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
	"      -h, --help",
    "          Display this help.",
	"      -H, --headers",
	"          Display column headers.",
	"      -V, --version",
	"          Display version number of this program.",
	"      --request-timeout TIMEOUT",
	"          Specify a request timeout TIMEOUT (in seconds).",
	"      -M, --show-mbox",
	"          Show the mbox physical function in the list of devices."
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
	"      -M, --metrics",
	"          Return FPGA image hardware metrics.",
	"          Examples: FPGA PCI and DDR metrics.",
	"      -C, --clear-metrics",
	"          Return FPGA image hardware metrics (clear on read).",
	"          Examples: FPGA PCI and DDR metrics.",
	"      -L, --clear-cache",
	"          Return FPGA image hardware metrics (clear afi cache on read).",
	"          Examples: agfi-<number>",
	"      -R, --rescan",
	"          Rescan the AFIDEVICE to update the per-AFI PCI VendorId and",
	"          DeviceId that may be dynamically modified due to a",
	"          fpga-load-local-image or fpga-clear-local-image command.",
	"          NOTE1: this option removes the AFIDEVICE from the sysfs PCI",
	"          subsystem and then rescans the PCI subsystem in order for",
	"          the modified AFI PCI IDs to be refreshed.",
	"          NOTE2: it is the developer's responsibility to remove any",
	"          driver previously installed on the older PCIe VendorId",
	"          and DeviceId before fpga-clear-local-image,",
	"          fpga-load-local-image, or re-scan.",
	"      -h, --help",
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
	"      NOTE: By default, this command automatically rescans the AFIDEVICE",
	"      to update the per-AFI PCI VendorId and DeviceId that may be",
	"      dynamically modified during each FPGA image load.",
	"      The rescan operation removes the AFIDEVICE from the sysfs PCI",
	"      subsystem and then rescans the PCI subsystem in order for",
	"      the modified AFI PCI IDs to be refreshed.",
	"      It is the developer's responsibility to remove any",
	"      driver previously installed on the older PCIe VendorId",
	"      and DeviceId before the FPGA image is loaded.",
	"  GENERAL OPTIONS",
	"      -S, --fpga-image-slot",
	"          The logical slot number for the FPGA image",
	"          Constraints: Positive integer from 0 to the total slots minus 1.",
	"      -I, --fpga-image-id",
	"          The ID of the FPGA image. agfi-<number>",
	"      -A, --async",
	"          The default mode of operation is synchronous FPGA image load",
	"          with automatic rescan.  The --async option may be specfied",
	"          for asynchronous FPGA image load completion, which may be",
	"          polled for completion using fpga-describe-local-image.",
	"      -h, --help",
	"          Display this help.",
	"      -H, --headers",
	"          Display column headers.",
	"      -V, --version",
	"          Display version number of this program.",
	"      --request-timeout TIMEOUT",
	"          Specify a request timeout TIMEOUT (in seconds).",
	"      --sync-timeout TIMEOUT",
	"          Specify a timeout TIMEOUT (in seconds) for the sequence",
	"          of operations that are performed in the synchronous (blocking)",
	"          mode.",
	"      -F, --force-shell-reload",
	"          Reload the FPGA shell on AFI load, even if the next AFI",
	"          doesn't require it.",
	"      -P, --prefetch-image",
	"          Prefetch the indicated AFI and store it in the cache for faster loading.",
	"          Fastest load times can be achieved by using cached AFIs and enabling data retention (-D).",
	"          See Reducing AFI load times documentation.",
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
	"      NOTE: By default, this command automatically rescans the AFIDEVICE",
	"      to update the default AFI PCI VendorId and DeviceId that are",
	"      dynamically modified during each FPGA image clear.",
	"      The rescan operation removes the AFIDEVICE from the sysfs PCI",
	"      subsystem and then rescans the PCI subsystem in order for",
	"      the modified AFI PCI IDs to be refreshed.",
	"      It is the developer's responsibility to remove any",
	"      driver previously installed on the older PCIe VendorId",
	"      and DeviceId before the FPGA image is cleared.",
	"  GENERAL OPTIONS",
	"      -S, --fpga-image-slot",
	"          The logical slot number for the FPGA image.",
	"          Constraints: Positive integer from 0 to the total slots minus 1.",
	"      -A, --async",
	"          The default mode of operation is synchronous FPGA image clear",
	"          with automatic rescan.  The --async option may be specfied",
	"          for asynchronous FPGA image clear completion, which may be",
	"          polled for completion using fpga-describe-local-image.",
	"      -h, --help",
	"          Display this help.",
	"      -H, --headers",
	"          Display column headers.",
	"      -V, --version",
	"          Display version number of this program.",
	"      --request-timeout TIMEOUT",
	"          Specify a request timeout TIMEOUT (in seconds).",
	"      --sync-timeout TIMEOUT",
	"          Specify a timeout TIMEOUT (in seconds) for the sequence",
	"          of operations that are performed in the synchronous (blocking)",
	"          mode",
};

static const char *start_virtual_jtag_usage[] = {
	"  SYNOPSIS",
	"      fpga-start-virtual-jtag [GENERAL OPTIONS] [-h]",
	"      Example: fpga-start-virtual-jtag -S 0 [-P <tcp-port>]",
	"  DESCRIPTION",
	"      Start Virtual JTAG spplication server, running Xilinx's Virtual",
	"      Cable (XVC) service,  which listens incoming command over TCP",
	"      port that is set by -P option (Default TCP port is 10201).",
	"      The fpga-image-slot parameter is a logical index that represents",
	"      a given FPGA within an instance.",
	"      This command will work only if AFI is in READY state:",
	"      Use fpga-describe-local-image to return the FPGA image status, and",
	"      fpga-describe-local-image-slots to return the AFI state.",
	"      The AFI should have included Xilinx's VIO/LIA debug cores",
	"      and AWS CL Debug Bridge inside the CustomLogic (CL)",
	"      Concurrent debug of multiple FPGA slots is possible as long as",
	"      different <tcp-port> values are used for each slot.",
	"      Linux firewall and/or EC2 Network Security Group rules may",
	"      need to change for enabling inbound access to the TCP port.",
	"  GENERAL OPTIONS",
	"      -S, --fpga-image-slot",
	"          The logical slot number for the FPGA image",
	"          Constraints: Positive integer from 0 to the total slots minus 1.",
	"      -P, --tcp-port",
	"          The TCP port number to use for virtual jtag server, default",
	"          TCP port is 10201.  Remember to use different TCP port for",
	"          different slot if debugging multiple slots concurrently",
	"      -h, --help",
	"          Display this help.",
	"      -H, --headers",
	"          Display column headers.",
	"      -V, --version",
	"          Display version number of this program.",
};

static const char *get_virtual_led_usage[] = {
	"  SYNOPSIS",
	"      fpga-get-virtual-led [GENERAL OPTIONS] [-h]",
	"      Example: fpga-get-virtual-led -S 0",
	"  DESCRIPTION",
	"      Returns the current status of the virtual LED exposed by the AFI, a",
	"      series of 0 (zeros) and 1 (ones), first digit from the righti maps",
	"      to cl_sh_vled[0]. For example, a return value 0000000001000000",
	"      indicates that cl_sh_vled[6] is set(on)",
	"  GENERAL OPTIONS",
	"      -S, --fpga-image-slot",
	"          The logical slot number for the FPGA image",
	"          Constraints: Positive integer from 0 to the total slots minus 1.",
	"      -h, --help",
	"          Display this help.",
	"      -H, --headers",
	"          Display column headers.",
	"      -V, --version",
	"          Display version number of this program.",
};

static const char *get_virtual_dip_usage[] = {
	"  SYNOPSIS",
	"      fpga-get-virtual-dip-switch [GENERAL OPTIONS] [-h]",
	"      Example: fpga-get-virtual-dip-switch -S 0",
	"  DESCRIPTION",
	"      Returns the current status of the virtual DIP Switches by",
	"      driven to the AFI. A series of 0 (Zeros) and 1 (ones)",
	"      First digit from the right maps to sh_cl_vdip[0]",
	"      For example, a return value 0000000001000000",
	"      indicates that sh_cl_vdip[6] is set(on)",
	"  GENERAL OPTIONS",
	"      -S, --fpga-image-slot",
	"          The logical slot number for the FPGA image",
	"          Constraints: Positive integer from 0 to the total slots minus 1.",
	"      -h, --help",
	"          Display this help.",
	"      -H, --headers",
	"          Display column headers.",
	"      -V, --version",
	"          Display version number of this program.",
};

static const char *set_virtual_dip_usage[] = {
	"  SYNOPSIS",
	"      fpga-set-virtual-dip-switch [GENERAL OPTIONS] [-h]",
	"      Example: fpga-set-virtual-dip-switch -S 0 -D 0101000011000000",
	"  DESCRIPTION",
	"      Drive the AFI in a given slot with the specified virtual DIP Switches",
	"      A 16 digit value is require: a series of 0 (zeros) and 1 (ones)",
	"      First digit from the right maps to sh_cl_vdip[0]",
	"      For example, a value 0101000011000000",
	"      indicates that sh_cl_vdip[6], [7], [12], and [14] is set/on",
	"  GENERAL OPTIONS",
	"      -S, --fpga-image-slot",
	"          The logical slot number for the FPGA image",
	"          Constraints: Positive integer from 0 to the total slots minus 1.",
	"      -D, --virtual-dip",
	"          A 16 digit bitmap representation of the desired setting for Virtual DIP Switches",
	"          This argument is mandatory and must be 16 digits made of any combinations of",
	"          zeros or ones.",
	"      -h, --help",
	"          Display this help.",
	"      -H, --headers",
	"          Display column headers.",
	"      -V, --version",
	"          Display version number of this program.",
};

static const char *describe_clkgen_usage[] = {
	"  SYNOPSIS",
	"      fpga-describe-clkgen",
	"      Example: fpga-describe-clkgen -S 0",
	"  DESCRIPTION",
	"      Returns the currently loaded frequencies for each clock in each MMCM"
	"  GENERAL OPTIONS",
	"      -S, --fpga-image-slot",
	"          The logical slot number for the FPGA image",
	"          Constraints: Positive integer from 0 to the total slots minus 1.",
	"      -h, --help",
	"          Display this help.",
	"      -V, --version",
	"          Display version number of this program.",
};

static const char *load_clkgen_recipe_usage[] = {
	"  SYNOPSIS",
	"      fpga-load-clkgen-recipe",
	"      Example: fpga-load-clkgen-recipe -S 0 -a 0 -b 1 -c 2 -m 3",
	"      Loads recipe A0 to MMCM_A, B1 to MMCM_B, C1 to MMCM_C and H3 to MMCM_HBM",
	"  DESCRIPTION",
	"      Loads a clock recipe into the specified MMCMs.",
	"      MMCMs that are not specified will be set to the default recipes.",
	"      Frquencies are listed in MHz. * - default recipe",
	"      A Recipe Number      clk_extra_a1    clk_extra_a2    clk_extra_a3",
	"      A0                   62.5            187.5           250",
	"      A1 *                 125             375             500",
	"      A2                   62.5            187.5           250",
	"      B Recipe Number      clk_extra_b0    clk_extra_b1",
	"      B0                   250             125",
	"      B1                   125             62.5",
	"      B2 *                 450             225",
	"      B3                   250             62.5",
	"      B4                   300             75",
	"      B5                   400             100",
	"      C Recipe Number      clk_extra_c0    clk_extra_c1",
	"      C0 *                 300             400",
	"      C1                   150             200",
	"      C2                   75              100",
	"      C3                   200             266.67",
	"      HBM Recipe Number    clk_hbm_axi",
	"      H0                   250",
	"      H1                   125",
	"      H2 *                 450",
	"      H3                   300",
	"      H4                   400",
	"      Returns the currently loaded clkgen clock configuration in MHz",
	"  GENERAL OPTIONS",
	"      -S, --fpga-image-slot",
	"          The logical slot number for the FPGA image",
	"          Constraints: Positive integer from 0 to the total slots minus 1.",
	"      -h, --help",
	"          Display this help.",
	"      -V, --version",
	"          Display version number of this program.",
	"      -a, --clock-a-recipe",
	"          Request the clock group A set with the specified recipe",
	"      -b, --clock-b-recipe",
	"          Request the clock group B set with the specified recipe",
	"      -c, --clock-c-recipe",
	"          Request the clock group C set with the specified recipe",
	"      -m, --clock-hbm-recipe",
	"          Request the clock group HBM set with the specified recipe",
};

static const char *load_clkgen_dynamic_usage[] = {
	"  SYNOPSIS",
	"      fpga-load-clkgen-dynamic",
	"      Example: fpga-load-clkgen-dynamic -S 0 -a 125 -b ",
	"  DESCRIPTION",
	"      Loads a frequency into the first clock of each specified MMCMs.",
	"      MMCMs not specified will be set to the default frequency.",
	"      clk_extra_a1 - Max Frequency 125 MHz, Default 125 MHz",
	"      clk_extra_b0 - Max Frequency 450 MHz, Default 450 MHz",
	"      clk_extra_c0 - Max Frequency 300 MHz, Default 300 MHz",
	"      clk_hbm_axi - Max Frequency 450 MHz, Default 450 MHz",
	"      Returns the currently loaded clkgen clock configuration",
	"  GENERAL OPTIONS",
	"      -S, --fpga-image-slot",
	"          The logical slot number for the FPGA image",
	"          Constraints: Positive integer from 0 to the total slots minus 1.",
	"      -h, --help",
	"          Display this help.",
	"      -V, --version",
	"          Display version number of this program.",
	"      -a, --clock-a1-freq",
	"          Request clk_extra_a1 frequency be set to this value in Mhz or less",
	"      -b, --clock-b0-freq",
	"          Request clk_extra_b0 frequency be set to this value in Mhz or less",
	"      -c, --clock-c0-freq",
	"          Request clk_extra_c0 frequency be set to this value in Mhz or less",
	"      -m, --clock-hbm-freq",
	"          Request clk_hbm_axi frequency be set to this value in Mhz or less",
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
}

/**
 * Check the given option and set the fpga.parser_completed flag.
 *
 * -parser_completed is set when the parser will complete the option
 *  (help or version output) and no further command processing is necessary,
 *  though a non-zero return value is still returned from parse_args.
 * -the parser_completed flag may then be used to skip the "Error" output
 *  that is generically used for parsing or other errors beyond the parsing
 *  stage.
 *
 * @param[in]	opt		the option to check
 */
static void
get_parser_completed(char opt)
{
	if ((opt == 'h') || (opt == 'V')) {
		fpga.parser_completed = true;
	}
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
			CLI_REQUEST_TIMEOUT_DFLT * CLI_REQUEST_DELAY_MSEC_DFLT / MSEC_PER_SEC;
	size_t timeout_max =
			((size_t)(uint32_t)-1) * CLI_REQUEST_DELAY_MSEC_DFLT / MSEC_PER_SEC;

	/** Check min and max values */
	fail_on_user((timeout < timeout_tmp) || (timeout > timeout_max), err,
			"Error: The timeout must be between %zu and %zu seconds",
			timeout_tmp, timeout_max);

	timeout_tmp = ((size_t)timeout) * MSEC_PER_SEC / CLI_REQUEST_DELAY_MSEC_DFLT;
	if (timeout_tmp > (uint32_t)-1) {
		/** Sanity check: Max out at ((1 << 32) - 1) * CLI_REQUEST_DELAY_MSEC_DFLT */
		timeout_tmp = (uint32_t)-1;
	}

	fpga.request_timeout = timeout_tmp;
	fpga.request_delay_msec = CLI_REQUEST_DELAY_MSEC_DFLT;

	log_debug("Setting timeout to %u secs, request_timeout=%u, request_delay_msec=%u",
			timeout, fpga.request_timeout, fpga.request_delay_msec);
	return 0;
err:
	return -EINVAL;
}

/**
 * Configure the synchronous operation timeout
 *
 * @param[in]   timeout		timeout in seconds
 *
 * @returns
 *  0   on success
 * -1   on failure
 */
static int
config_sync_timeout(uint32_t timeout)
{
	size_t timeout_tmp =
			CLI_SYNC_TIMEOUT_DFLT * CLI_SYNC_DELAY_MSEC_DFLT / MSEC_PER_SEC;
	size_t timeout_max =
			((size_t)(uint32_t)-1) * CLI_SYNC_DELAY_MSEC_DFLT / MSEC_PER_SEC;

	/** Check min and max values */
	fail_on_user((timeout < timeout_tmp) || (timeout > timeout_max), err,
			"Error: The timeout must be between %zu and %zu seconds",
			timeout_tmp, timeout_max);

	timeout_tmp = ((size_t)timeout) * MSEC_PER_SEC / CLI_SYNC_DELAY_MSEC_DFLT;
	if (timeout_tmp > (uint32_t)-1) {
		/** Sanity check: Max out at ((1 << 32) - 1) * CLI_SYNC_DELAY_MSEC_DFLT */
		timeout_tmp = (uint32_t)-1;
	}

	fpga.sync_timeout = timeout_tmp;
	fpga.sync_delay_msec = CLI_SYNC_DELAY_MSEC_DFLT;

	log_debug("Setting timeout to %u secs, sync_timeout=%u, sync_delay_msec=%u",
			timeout, fpga.sync_timeout, fpga.sync_delay_msec);
	return 0;
err:
	return -EINVAL;
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
		{"sync-timeout",		required_argument,	0,	's'	},
		{"async",				no_argument,		0,	'A'	},
		{"headers",				no_argument,		0,	'H'	},
		{"help",				no_argument,		0,	'h'	},
		{"version",				no_argument,		0,	'V'	},
		{"force-shell-reload",	no_argument,		0,	'F'	},
		{"prefetch-image",		no_argument,		0,	'P'	},
		{0,						0,					0,	0	},
	};

	int long_index = 0;
	while ((opt = getopt_long(argc, argv, "S:I:r:s:AH?hVFDP",
			long_options, &long_index)) != -1) {
		switch (opt) {
		case 'S': {
			string_to_uint(&fpga.afi_slot, optarg);
			fail_on_user(fpga.afi_slot >= FPGA_SLOT_MAX, err, "fpga-image-slot must be less than %u",
					FPGA_SLOT_MAX);
			break;
		}
		case 'I': {
		    fail_on_user(strnlen(optarg, AFI_ID_STR_MAX) == AFI_ID_STR_MAX, err,
					"fpga-image-id must be less than %u bytes", AFI_ID_STR_MAX);

			strncpy(fpga.afi_id, optarg, sizeof(fpga.afi_id));
			fpga.afi_id[sizeof(fpga.afi_id) - 1] = 0;
			break;
		}
		case 'r': {
			uint32_t value32;
			string_to_uint(&value32, optarg);
			int ret = config_request_timeout(value32);
			fail_on(ret != 0, err, "Could not configure the request-timeout");
			break;
		}
		case 's': {
			uint32_t value32;
			string_to_uint(&value32, optarg);
			int ret = config_sync_timeout(value32);
			fail_on(ret != 0, err, "Could not configure the sync-timeout");
			break;
		}
		case 'A': {
			fpga.async = true;
			break;
		}
		case 'H': {
			fpga.show_headers = true;
			break;
		}
		case 'F': {
			fpga.force_shell_reload = true;
			break;
		}
		case 'V': {
			print_version();
			get_parser_completed(opt);
			goto out_ver;
		}
		case 'P': {
			fpga.prefetch = true;
			fpga.async = true;
			break;
		}
		default: {
			get_parser_completed(opt);
			goto err;
		}
		}
	}

	if ((fpga.afi_slot == (uint32_t) -1) ||
		(fpga.afi_id[0] == 0)) {
		goto err;
	}

	return 0;
err:
	print_usage(argv[0], load_afi_usage, sizeof_array(load_afi_usage));
out_ver:
	return -EINVAL;
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
		{"sync-timeout",		required_argument,	0,	's'	},
		{"async",				no_argument,		0,	'A'	},
		{"headers",				no_argument,		0,	'H'	},
		{"help",				no_argument,		0,	'h'	},
		{"version",				no_argument,		0,	'V'	},
		{0,						0,					0,	0	},
	};

	int long_index = 0;
	while ((opt = getopt_long(argc, argv, "S:r:s:AH?hV",
			long_options, &long_index)) != -1) {
		switch (opt) {
		case 'S': {
			string_to_uint(&fpga.afi_slot, optarg);
			fail_on_user(fpga.afi_slot >= FPGA_SLOT_MAX, err, "fpga-image-slot must be less than %u",
					FPGA_SLOT_MAX);
			break;
		}
		case 'r': {
			uint32_t value32;
			string_to_uint(&value32, optarg);
			int ret = config_request_timeout(value32);
			fail_on(ret != 0, err, "Could not configure the request-timeout");
			break;
		}
		case 's': {
			uint32_t value32;
			string_to_uint(&value32, optarg);
			int ret = config_sync_timeout(value32);
			fail_on(ret != 0, err, "Could not configure the sync-timeout");
			break;
		}
		case 'A': {
			fpga.async = true;
			break;
		}
		case 'H': {
			fpga.show_headers = true;
			break;
		}
		case 'V': {
			print_version();
			get_parser_completed(opt);
			goto out_ver;
		}
		default: {
			get_parser_completed(opt);
			goto err;
		}
		}
	}

	if (fpga.afi_slot == (uint32_t) -1) {
		goto err;
	}

	return 0;
err:
	print_usage(argv[0], clear_afi_usage, sizeof_array(clear_afi_usage));
out_ver:
	return -EINVAL;
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
		{"metrics",				no_argument,		0,	'M' },
		{"clear-metrics",		no_argument,		0,	'C' },
		{"clear-cache",			no_argument,		0,	'L' },
		{"request-timeout",		required_argument,	0,	'r'	},
		{"rescan",				no_argument,		0,	'R'	},
		{"headers",				no_argument,		0,	'H'	},
		{"help",				no_argument,		0,	'h'	},
		{"version",				no_argument,		0,	'V'	},
		{0,						0,					0,	0	},
	};

	int long_index = 0;
	while ((opt = getopt_long(argc, argv, "S:MCLr:RH?hV",
			long_options, &long_index)) != -1) {
		switch (opt) {
		case 'S': {
			string_to_uint(&fpga.afi_slot, optarg);
			fail_on_user(fpga.afi_slot >= FPGA_SLOT_MAX, err,
					"fpga-image-slot must be less than %u", FPGA_SLOT_MAX);
			break;
		}
		case 'M': {
			fpga.get_hw_metrics = true;
			break;
		}
		case 'C': {
			fpga.get_hw_metrics = true;
			fpga.clear_hw_metrics = true;
			break;
		}
		case 'L': {
			fpga.get_hw_metrics = true;
			fpga.clear_afi_cache = true;
			break;
		}
		case 'r': {
			uint32_t value32;
			string_to_uint(&value32, optarg);
			int ret = config_request_timeout(value32);
			fail_on(ret != 0, err, "Could not configure the request-timeout");
			break;
		}
		case 'R': {
			fpga.rescan = true;
			break;
		}
		case 'H': {
			fpga.show_headers = true;
			break;
		}
		case 'V': {
			print_version();
			get_parser_completed(opt);
			goto out_ver;
		}
		default: {
			get_parser_completed(opt);
			goto err;
		}
		}
	}

	if (fpga.afi_slot == (uint32_t) -1) {
		goto err;
	}

	return 0;
err:
        print_usage(argv[0], describe_afi_usage, sizeof_array(describe_afi_usage));
out_ver:
	return -EINVAL;
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
		{"help",				no_argument,		0,	'h'	},
		{"version",				no_argument,		0,	'V'	},
		{"show-mbox",           no_argument,        0,  'M' },
		{0,						0,					0,	0	},
	};

	int long_index = 0;
	while ((opt = getopt_long(argc, argv, "r:H?hVM",
			long_options, &long_index)) != -1) {
		switch (opt) {
		case 'r': {
			uint32_t value32;
			string_to_uint(&value32, optarg);
			int ret = config_request_timeout(value32);
			fail_on(ret != 0, err, "Could not configure the request-timeout");
			break;
		}
		case 'H': {
			fpga.show_headers = true;
			break;
		}
		case 'V': {
			print_version();
			get_parser_completed(opt);
			goto out_ver;
		}
		case 'M': {
			fpga.show_mbox_device = true;
			break;
		}
		default: {
			get_parser_completed(opt);
			goto err;
		}
		}
	}

	return 0;
err:
	print_usage(argv[0], describe_afi_slots_usage,
			sizeof_array(describe_afi_slots_usage));
out_ver:
	return -EINVAL;
}


static  char default_tcp_port[5] = "10201";
/**
 * Parse fpga-start-virtual-jtag command line arguments.
 *
 * @param[in]   argc    Argument count.
 * @param[in]   argv    Argument string vector.
 */
static int
parse_args_start_virtual_jtag(int argc, char *argv[])
{
	int opt = 0;
	uint32_t temp_int = 0;
	char*	tcp_port;

	static struct option long_options[] = {
		{"fpga-image-slot",		required_argument,	0,	'S'	},
		{"tcp-port",			required_argument,	0,	'P'	},
		{"headers",				no_argument,		0,	'H'	},
		{"help",				no_argument,		0,	'h'	},
		{"version",				no_argument,		0,	'V'	},
		{0,						0,					0,	0	},
	};

	int long_index = 0;
	fpga.tcp_port=(char*) default_tcp_port;

	while ((opt = getopt_long(argc, argv, "S:P:RH?hV",
			long_options, &long_index)) != -1) {
		switch (opt) {
		case 'S': {
			string_to_uint(&fpga.afi_slot, optarg);
			fail_on_user(fpga.afi_slot >= FPGA_SLOT_MAX, err,
					"fpga-image-slot must be less than %u", FPGA_SLOT_MAX);
			break;
		}
		case 'P': { // FIXME
			tcp_port = optarg;
			string_to_uint(&temp_int, tcp_port);
			fail_on_user(temp_int >= (64*1024-1), err,
                                        "tcp-port must be less than %u", 64*1024-1);
			fail_on_user(temp_int <= (1024), err,
                                        "tcp-port must be larger than %u",1024);
			fpga.tcp_port = optarg;
			break;
		}
		case 'H': {
			fpga.show_headers = true;
			break;
		}
		case 'V': {
			print_version();
			get_parser_completed(opt);
			goto out_ver;
		}
		default: {
			get_parser_completed(opt);
			goto err;
		}
		}
	}

	if (fpga.afi_slot == (uint32_t) -1) {
		printf("Error: Invalid Slot Id !");
		goto err;
	}

	return 0;

err:
        print_usage(argv[0], start_virtual_jtag_usage, sizeof_array(start_virtual_jtag_usage));
out_ver:
	return -EINVAL;
}

/**
 * Parse fpga-get-virtual-led command line arguments.
 *
 * @param[in]   argc    Argument count.
 * @param[in]   argv    Argument string vector.
 */
static int
parse_args_get_virtual_led(int argc, char *argv[])
{
	int opt;

	static struct option long_options[] = {
		{"fpga-image-slot",		required_argument,	0,	'S'	},
		{"headers",				no_argument,		0,	'H'	},
		{"help",				no_argument,		0,	'h'	},
		{"version",				no_argument,		0,	'V'	},
		{0,						0,					0,	0	},
	};

	int long_index = 0;
	while ((opt = getopt_long(argc, argv, "S:RH?hV",
			long_options, &long_index)) != -1) {
		switch (opt) {
		case 'S': {
			string_to_uint(&fpga.afi_slot, optarg);
			fail_on_user(fpga.afi_slot >= FPGA_SLOT_MAX, err,
					"fpga-image-slot must be less than %u", FPGA_SLOT_MAX);
			break;
		}

		case 'H': {
			fpga.show_headers = true;
			break;
		}
		case 'V': {
			print_version();
			get_parser_completed(opt);
			goto out_ver;
		}
		default: {
			get_parser_completed(opt);
			goto err;
		}
		}
	}

	if (fpga.afi_slot == (uint32_t) -1) {
		printf("Error: Invalid Slot Id !");
		goto err;
	}
	return 0;
err:
        print_usage(argv[0], get_virtual_led_usage, sizeof_array(get_virtual_led_usage));
out_ver:
	return -EINVAL;
}

/**
 * Parse fpga-get-virtual-dip-switch command line arguments.
 *
 * @param[in]   argc    Argument count.
 * @param[in]   argv    Argument string vector.
 */
static int
parse_args_get_virtual_dip(int argc, char *argv[])
{
	int opt;

	static struct option long_options[] = {
		{"fpga-image-slot",		required_argument,	0,	'S'	},
		{"headers",				no_argument,		0,	'H'	},
		{"help",				no_argument,		0,	'h'	},
		{"version",				no_argument,		0,	'V'	},
		{0,						0,					0,	0	},
	};

	int long_index = 0;
	while ((opt = getopt_long(argc, argv, "S:RH?hV",
			long_options, &long_index)) != -1) {
		switch (opt) {
		case 'S': {
			string_to_uint(&fpga.afi_slot, optarg);
			fail_on_user(fpga.afi_slot >= FPGA_SLOT_MAX, err,
					"fpga-image-slot must be less than %u", FPGA_SLOT_MAX);
			break;
		}

		case 'H': {
			fpga.show_headers = true;
			break;
		}
		case 'V': {
			print_version();
			get_parser_completed(opt);
			goto out_ver;
		}
		default: {
			get_parser_completed(opt);
			goto err;
		}
		}
	}

	if (fpga.afi_slot == (uint32_t) -1) {
		printf("Error: Invalid Slot Id !");
		goto err;
	}

	return 0;
err:
        print_usage(argv[0], get_virtual_dip_usage, sizeof_array(get_virtual_dip_usage));
out_ver:
	return -EINVAL;
}

/**
 * Parse fpga-set-virtual-dip-switch command line arguments.
 *
 * @param[in]   argc    Argument count.
 * @param[in]   argv    Argument string vector.
 */
static int
parse_args_set_virtual_dip(int argc, char *argv[])
{
	int opt;
	uint16_t status=0;
	int i;
	int vdip_arg_found=0;

	static struct option long_options[] = {
		{"fpga-image-slot",		required_argument,	0,	'S'	},
		{"virtual-dip",			required_argument,	0,	'D'	},
		{"headers",				no_argument,		0,	'H'	},
		{"help",				no_argument,		0,	'h'	},
		{"version",				no_argument,		0,	'V'	},
		{0,						0,					0,	0	},
	};

	int long_index = 0;
	while ((opt = getopt_long(argc, argv, "S:D:RH?hV",
			long_options, &long_index)) != -1) {
		switch (opt) {
		case 'S': {
			string_to_uint(&fpga.afi_slot, optarg);
			fail_on_user(fpga.afi_slot >= FPGA_SLOT_MAX, err,
					"fpga-image-slot must be less than %u", FPGA_SLOT_MAX);
			break;
		}
		case 'D': {
			fail_on_user(strlen(optarg) != 16, err,
					"virtual-dip must be 16 digits of zero or one");
			for (i=0;i<16;i++) {
				if (optarg[i] == '1')
					status = status | 0x1;
				else if (optarg[i] == '0')
					status = status;
				else
					fail_on_user(1, err,
					"illegal digit for virtual-dip %c", optarg[i]);
				if (i!=15)
					status = status << 1;
			}
			vdip_arg_found=1;
			fpga.v_dip_switch=status;
			break;
		}

		case 'H': {
			fpga.show_headers = true;
			break;
		}
		case 'V': {
			print_version();
			get_parser_completed(opt);
			goto out_ver;
		}

		default: {
			get_parser_completed(opt);
			goto err;
		}
		}
	}

	if (fpga.afi_slot == (uint32_t) -1) {
		printf("Error: Invalid Slot Id !");
		goto err;
	}
	if (!vdip_arg_found) {
		printf("Error: Missing DIP Switch values !");
		goto err;
	}

	return 0;
err:
        print_usage(argv[0], set_virtual_dip_usage, sizeof_array(set_virtual_dip_usage));
out_ver:
	return -EINVAL;
}

/**
 * Parse describe_clkgen command line arguments.
 *
 * @param[in]   argc    Argument count.
 * @param[in]   argv    Argument string vector.
 */
static int
parse_args_describe_clkgen(int argc, char *argv[])
{
	int opt = 0;

	static struct option long_options[] = {
		{"fpga-image-slot",		required_argument,	0,	'S'	},
		{"help",				no_argument,		0,	'h'	},
		{"version",				no_argument,		0,	'V'	},
		{0,						0,					0,	0	},
	};

	int long_index = 0;
	while ((opt = getopt_long(argc, argv, "S:hV?",
			long_options, &long_index)) != -1) {
		switch (opt) {
		case 'S': {
			string_to_uint(&fpga.afi_slot, optarg);
			fail_on_user(fpga.afi_slot >= FPGA_SLOT_MAX, err,
					"fpga-image-slot must be less than %u", FPGA_SLOT_MAX);
			break;
		}
		case 'V': {
			print_version();
			get_parser_completed(opt);
			goto out_ver;
		}
		default: {
			get_parser_completed(opt);
			goto err;
		}
		}
	}

	if (fpga.afi_slot == (uint32_t) -1) {
		goto err;
	}

	return 0;
err:
        print_usage(argv[0], describe_clkgen_usage, sizeof_array(describe_clkgen_usage));
out_ver:
	return -EINVAL;
}

/**
 * Parse load_clkgen command line arguments.
 *
 * @param[in]   argc    Argument count.
 * @param[in]   argv    Argument string vector.
 */
static int
parse_args_load_clkgen_recipe(int argc, char *argv[])
{
	int opt = 0;

	static struct option long_options[] = {
		{"fpga-image-slot",		required_argument,	0,	'S'	},
		{"help",				no_argument,		0,	'h'	},
		{"version",				no_argument,		0,	'V'	},
		{"clock-a-recipe",      required_argument,  0,  'a' },
		{"clock-b-recipe",      required_argument,  0,  'b' },
		{"clock-c-recipe",      required_argument,  0,  'c' },
		{"clock-hbm-recipe",    required_argument,  0,  'm' },
		{0,						0,					0,	0	},
	};

	int long_index = 0;
	while ((opt = getopt_long(argc, argv, "S:hV?a:b:c:m:",
			long_options, &long_index)) != -1) {
		switch (opt) {
		case 'S': {
			string_to_uint(&fpga.afi_slot, optarg);
			fail_on_user(fpga.afi_slot >= FPGA_SLOT_MAX, err,
					"fpga-image-slot must be less than %u", FPGA_SLOT_MAX);
			break;
		}
		case 'a': {
			string_to_uint(&fpga.clock_a_recipe, optarg);
			break;
		}
		case 'b': {
			string_to_uint(&fpga.clock_b_recipe, optarg);
			break;
		}
		case 'c': {
			string_to_uint(&fpga.clock_c_recipe, optarg);
			break;
		}
		case 'm': {
			string_to_uint(&fpga.clock_hbm_recipe, optarg);
			break;
		}
		case 'V': {
			print_version();
			get_parser_completed(opt);
			goto out_ver;
		}
		default: {
			get_parser_completed(opt);
			goto err;
		}
		}
	}

	if (fpga.afi_slot == (uint32_t) -1) {
		goto err;
	}

	return 0;
err:
        print_usage(argv[0], load_clkgen_recipe_usage, sizeof_array(load_clkgen_recipe_usage));
out_ver:
	return -EINVAL;
}

static int
parse_args_load_clkgen_dynamic(int argc, char *argv[])
{
	int opt = 0;

	static struct option long_options[] = {
		{"fpga-image-slot",		required_argument,	0,	'S'	},
		{"help",				no_argument,		0,	'h'	},
		{"version",				no_argument,		0,	'V'	},
		{"clock-a0-freq",       required_argument,  0,  'a' },
		{"clock-b0-freq",       required_argument,  0,  'b' },
		{"clock-c0-freq",       required_argument,  0,  'c' },
		{"clock-hbm-freq",      required_argument,  0,  'm' },
		{0,						0,					0,	0	},
	};

	int long_index = 0;
	while ((opt = getopt_long(argc, argv, "S:hV?a:b:c:m:",
			long_options, &long_index)) != -1) {
		switch (opt) {
		case 'S': {
			string_to_uint(&fpga.afi_slot, optarg);
			fail_on_user(fpga.afi_slot >= FPGA_SLOT_MAX, err,
					"fpga-image-slot must be less than %u", FPGA_SLOT_MAX);
			break;
		}
		case 'a': {
			string_to_uint(&fpga.clock_a_freq, optarg);
			break;
		}
		case 'b': {
			string_to_uint(&fpga.clock_b_freq, optarg);
			break;
		}
		case 'c': {
			string_to_uint(&fpga.clock_c_freq, optarg);
			break;
		}
		case 'm': {
			string_to_uint(&fpga.clock_hbm_freq, optarg);
			break;
		}
		case 'V': {
			print_version();
			get_parser_completed(opt);
			goto out_ver;
		}
		default: {
			get_parser_completed(opt);
			goto err;
		}
		}
	}

	if (fpga.afi_slot == (uint32_t) -1) {
		goto err;
	}

	return 0;
err:
        print_usage(argv[0], load_clkgen_dynamic_usage, sizeof_array(load_clkgen_dynamic_usage));
out_ver:
	return -EINVAL;
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
	fail_on(argc < 2, err, "Error: opcode string must be specified");
	fail_on_user(!argv[0] || !argv[1], err,
			"Error: program name or opcode string is NULL");

	static struct parse_args_str2func str2func[] = {
		{"LoadFpgaImage",			CLI_CMD_LOAD,					parse_args_load_afi},
		{"ClearFpgaImage",			CLI_CMD_CLEAR,					parse_args_clear_afi},
		{"DescribeFpgaImageSlots",	CLI_CMD_DESCRIBE_SLOTS,			parse_args_describe_afi_slots},
		{"DescribeFpgaImage",		CLI_CMD_DESCRIBE,				parse_args_describe_afi},
		{"StartVirtualJtag",		CLI_CMD_START_VJTAG,			parse_args_start_virtual_jtag},
		{"GetVirtualLED",			CLI_CMD_GET_LED,				parse_args_get_virtual_led},
		{"GetVirtualDIP",			CLI_CMD_GET_DIP,				parse_args_get_virtual_dip},
		{"SetVirtualDIP",			CLI_CMD_SET_DIP,				parse_args_set_virtual_dip},
		{"DescribeClkGen",			CLI_CMD_DESCRIBE_CLKGEN,		parse_args_describe_clkgen},
		{"LoadClkGenRecipe",		CLI_CMD_LOAD_CLKGEN_RECIPE,		parse_args_load_clkgen_recipe},
		{"LoadClkGenDynamic",		CLI_CMD_LOAD_CLKGEN_DYNAMIC,	parse_args_load_clkgen_dynamic},
	};

	char *opcode_str = argv[1];
	size_t i;
	int ret = -EINVAL;
	for (i = 0; i < sizeof_array(str2func); i++) {
		struct parse_args_str2func *entry = &str2func[i];

		if (!strncmp(entry->str, opcode_str, strlen(entry->str))) {
			fpga.opcode = entry->opcode;
			ret = entry->func(argc, argv);
			break;
		}
	}

	if (fpga.opcode == (uint32_t)-1) {
		goto err;
	}

	return ret;
err:
	print_usage(argv[0], opcode_str_usage, sizeof_array(opcode_str_usage));
	return -EINVAL;
}
