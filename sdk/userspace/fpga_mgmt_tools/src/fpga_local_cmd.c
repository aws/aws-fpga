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
 * Main EC2 F1 CLI processing.
 */

#include <assert.h>
#include <limits.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <stdlib.h>
#include <string.h>
#include <sys/errno.h>
#include <stdio.h>
#include <getopt.h>

#include <fpga_mgmt.h>
#include <utils/lcd.h>

#include "fpga_local_cmd.h"
#include "virtual_jtag.h"

#define TYPE_FMT	"%-10s"

/**
 * Globals 
 */
struct ec2_fpga_cmd f1;

/** 
 * Use dmesg as the default logger, stdout is available for debug.
 */
#if 1
const struct logger *logger = &logger_kmsg;
#else
const struct logger *logger = &logger_stdout;
#endif

/**
 * Display the application PFs for the given AFI slot.
 *
 * @param[in]   afi_slot	the fpga slot
 *
 * @returns
 *  0	on success, non-zero on failure
 */
static int 
cli_show_slot_app_pfs(int slot_id, struct fpga_slot_spec *spec)
{
	fail_on(slot_id >= FPGA_SLOT_MAX, err, "slot_id(%d) >= %d", 
		slot_id, FPGA_SLOT_MAX);

	if (f1.show_headers) {
		printf("Type  FpgaImageSlot  VendorId    DeviceId    DBDF\n");         
	}

	/** Retrieve and display associated application PFs (if any) */
	bool found_app_pf = false;
	int i;
	for (i = 0; i < FPGA_PF_MAX; i++) {
		struct fpga_pci_resource_map *app_map = &spec->map[i];

		if (i == FPGA_MGMT_PF && !f1.show_mbox_device) {
			/* skip the mbox pf */
			continue;
		}

		printf(TYPE_FMT "  %2u       0x%04x      0x%04x      " PCI_DEV_FMT "\n",
				"AFIDEVICE", slot_id, app_map->vendor_id, app_map->device_id, 
				app_map->domain, app_map->bus, app_map->dev, app_map->func);
		found_app_pf = true;
	}
	if (!found_app_pf) {
		printf(TYPE_FMT "    unknown    unknown    unknown\n", "AFIDEVICE"); 
	}

	return 0;
err:
	return FPGA_ERR_FAIL;
}

/**
 * Display the FPGA image information.
 *
 * @param[in]   info the fpga info 
 *
 * @returns
 *  0	on success, non-zero on failure
 */
static int 
cli_show_image_info(struct fpga_mgmt_image_info *info)
{
	assert(info);

	struct fpga_slot_spec slot_spec;
	int ret = FPGA_ERR_FAIL;
	uint32_t i;
	uint64_t frequency;

	if (f1.show_headers) {
		printf("Type  FpgaImageSlot  FpgaImageId             StatusName    StatusCode   ErrorName    ErrorCode   ShVersion\n");
	}

	char *afi_id = (!info->ids.afi_id[0]) ? "none" : info->ids.afi_id;
	printf(TYPE_FMT "  %2u       %-22s", "AFI", f1.afi_slot, afi_id);

	printf("  %-8s         %2d        %-8s        %2d       0x%08x\n", 
			FPGA_STATUS2STR(info->status), info->status, 
			FPGA_ERR2STR(info->status_q), info->status_q, 
			info->sh_version);

	if (f1.rescan) {
		/** Rescan the application PFs for this slot */
		ret = fpga_pci_rescan_slot_app_pfs(f1.afi_slot);
		fail_on(ret != 0, err, "cli_rescan_slot_app_pfs failed");
	}

	/** Display the application PFs for this slot */
	ret = fpga_pci_get_slot_spec(f1.afi_slot, &slot_spec);
	fail_on(ret != 0, err, "fpga_pci_get_slot_spec failed");
	ret = cli_show_slot_app_pfs(f1.afi_slot, &slot_spec);
	fail_on(ret != 0, err, "cli_show_slot_app_pfs failed");

	if (f1.get_hw_metrics) {
		if (f1.show_headers) {
			printf("Metrics\n");
		}

		struct fpga_metrics_common *fmc = &info->metrics;
		printf("sdacl-slave-timeout=%u\n", 
				(fmc->int_status & FPGA_INT_STATUS_SDACL_SLAVE_TIMEOUT) ?  1 : 0);

		printf("virtual-jtag-slave-timeout=%u\n", 
				(fmc->int_status & FPGA_INT_STATUS_VIRTUAL_JTAG_SLAVE_TIMEOUT) ?  1 : 0);

		printf("ocl-slave-timeout=%u\n", 
				(fmc->int_status & FPGA_INT_STATUS_OCL_SLAVE_TIMEOUT) ?
				1 : 0); 

		printf("bar1-slave-timeout=%u\n", 
				(fmc->int_status & FPGA_INT_STATUS_BAR1_SLAVE_TIMEOUT) ?
				1 : 0); 

		printf("dma-pcis-timeout=%u\n", 
				(fmc->int_status & FPGA_INT_STATUS_DMA_PCI_SLAVE_TIMEOUT) ?
				1 : 0); 

		printf("pcim-range-error=%u\n", 
				(fmc->int_status & FPGA_INT_STATUS_PCI_MASTER_RANGE_ERROR) ? 
				1 : 0); 

		printf("pcim-axi-protocol-error=%u\n", 
				(fmc->int_status & FPGA_INT_STATUS_PCI_MASTER_AXI_PROTOCOL_ERROR) ?
				1 : 0); 

		printf("pcim-axi-protocol-4K-cross-error=%u\n", 
				(fmc->pcim_axi_protocol_error_status & FPGA_PAP_4K_CROSS_ERROR) ?
				1 : 0); 

		printf("pcim-axi-protocol-bus-master-enable-error=%u\n", 
				(fmc->pcim_axi_protocol_error_status & FPGA_PAP_BM_EN_ERROR) ?
				1 : 0); 

		printf("pcim-axi-protocol-request-size-error=%u\n", 
				(fmc->pcim_axi_protocol_error_status & FPGA_PAP_REQ_SIZE_ERROR) ?
				1 : 0); 

		printf("pcim-axi-protocol-write-incomplete-error=%u\n", 
				(fmc->pcim_axi_protocol_error_status & FPGA_PAP_WR_INCOMPLETE_ERROR) ?
				1 : 0); 

		printf("pcim-axi-protocol-first-byte-enable-error=%u\n", 
				(fmc->pcim_axi_protocol_error_status & FPGA_PAP_FIRST_BYTE_EN_ERROR) ?
				1 : 0); 

		printf("pcim-axi-protocol-last-byte-enable-error=%u\n", 
				(fmc->pcim_axi_protocol_error_status & FPGA_PAP_LAST_BYTE_EN_ERROR) ?
				1 : 0); 

		printf("pcim-axi-protocol-bready-error=%u\n", 
				(fmc->pcim_axi_protocol_error_status & FPGA_PAP_BREADY_TIMEOUT_ERROR) ?
				1 : 0); 

		printf("pcim-axi-protocol-rready-error=%u\n", 
				(fmc->pcim_axi_protocol_error_status & FPGA_PAP_RREADY_TIMEOUT_ERROR) ?
				1 : 0); 

		printf("pcim-axi-protocol-wchannel-error=%u\n", 
				(fmc->pcim_axi_protocol_error_status & FPGA_PAP_WCHANNEL_TIMEOUT_ERROR) ?
				1 : 0); 

		printf("sdacl-slave-timeout-addr=0x%" PRIx32 "\n", fmc->sdacl_slave_timeout_addr); 
		printf("sdacl-slave-timeout-count=%u\n", fmc->sdacl_slave_timeout_count); 

		printf("virtual-jtag-slave-timeout-addr=0x%" PRIx32 "\n", fmc->virtual_jtag_slave_timeout_addr); 
		printf("virtual-jtag-slave-timeout-count=%u\n", fmc->virtual_jtag_slave_timeout_count); 

		printf("ocl-slave-timeout-addr=0x%" PRIx64 "\n", fmc->ocl_slave_timeout_addr); 
		printf("ocl-slave-timeout-count=%u\n", fmc->ocl_slave_timeout_count); 

		printf("bar1-slave-timeout-addr=0x%" PRIx64 "\n", fmc->bar1_slave_timeout_addr); 
		printf("bar1-slave-timeout-count=%u\n", fmc->bar1_slave_timeout_count); 

		printf("dma-pcis-timeout-addr=0x%" PRIx64 "\n", fmc->dma_pcis_timeout_addr); 
		printf("dma-pcis-timeout-count=%u\n", fmc->dma_pcis_timeout_count); 

		printf("pcim-range-error-addr=0x%" PRIx64 "\n", fmc->pcim_range_error_addr); 
		printf("pcim-range-error-count=%u\n", fmc->pcim_range_error_count); 

		printf("pcim-axi-protocol-error-addr=0x%" PRIx64 "\n", fmc->pcim_axi_protocol_error_addr); 
		printf("pcim-axi-protocol-error-count=%u\n", fmc->pcim_axi_protocol_error_count); 

		printf("pcim-write-count=%" PRIu64 "\n", fmc->pcim_write_count); 
		printf("pcim-read-count=%" PRIu64 "\n", fmc->pcim_read_count); 

		for (i = 0; i < sizeof_array(fmc->ddr_ifs); i++) {
			struct fpga_ddr_if_metrics_common *ddr_if = &fmc->ddr_ifs[i];

			printf("DDR%u\n", i);
			printf("   write-count=%" PRIu64 "\n", ddr_if->write_count); 
			printf("   read-count=%" PRIu64 "\n", ddr_if->read_count); 
		}

		printf("Clock Group A Frequency (Mhz)\n");
		for (i = 0; i < CLOCK_COUNT_A; i++) {
			frequency = fmc->clocks[0].frequency[i] / 1000000;
			printf("%" PRIu64 "  ", frequency); 
		}
		printf("\nClock Group B Frequency (Mhz)\n");
		for (i = 0; i < CLOCK_COUNT_B; i++) {
			frequency = fmc->clocks[1].frequency[i] / 1000000;
			printf("%" PRIu64 "  ", frequency); 
		}
		printf("\nClock Group C Frequency (Mhz)\n");
		for (i = 0; i < CLOCK_COUNT_C; i++) {
			frequency = fmc->clocks[2].frequency[i] / 1000000;
			printf("%" PRIu64 "  ", frequency); 
		}
		printf("\n");

		printf("Power consumption (Vccint):\n");
		printf("   Last measured: %" PRIu64 " watts\n",fmc->power);
		printf("   Average: %" PRIu64 " watts\n",fmc->power_mean);
		printf("   Max measured: %" PRIu64 " watts\n",fmc->power_max);
	}

	return 0;
err:
	return ret;
}

/**
 * Attach for CLI processing.
 *
 * @returns
 *  0	on success, non-zero on failure
 */
static int
cli_attach(void)
{
	int ret = FPGA_ERR_FAIL;

	if (f1.opcode == CLI_CMD_DESCRIBE_SLOTS) {
		/** 
		 * ec2-afi-describe-slots does not use the Mbox logic, local
		 * information only 
		 */
		goto out;
	}

	ret = fpga_mgmt_init();
	fail_on(ret != 0, err, "fpga_mgmt_init failed");

	fpga_mgmt_set_cmd_timeout(f1.request_timeout);
	fpga_mgmt_set_cmd_delay_msec(f1.request_delay_msec);

out:
	return 0;
err:
	return ret;
}

/**
 * Detach CLI processing.
 *
 * @returns
 *  0	on success, non-zero on failure
 */
static int
cli_detach(void)
{
	fpga_mgmt_close();
	return 0;
}

/**
 * Generate the load local image command.
 *
 * @returns
 *  0	on success, non-zero on failure
 */
static int command_load(void)
{
	int ret;
	union fpga_mgmt_load_local_image_options opt;

	uint32_t flags = (f1.force_shell_reload) ? FPGA_CMD_FORCE_SHELL_RELOAD : 0;

 	fpga_mgmt_init_load_local_image_options(&opt);
        opt.slot_id = f1.afi_slot;
        opt.afi_id = f1.afi_id;
        opt.flags = flags;
	opt.clock_mains[0] = f1.clock_a0_freq;
	opt.clock_mains[1] = f1.clock_b0_freq;
	opt.clock_mains[2] = f1.clock_c0_freq;


	if (f1.async) {
		ret = fpga_mgmt_load_local_image_with_options(&opt);
		fail_on(ret != 0, err, "fpga_mgmt_load_local_image failed");
	} else {
		struct fpga_mgmt_image_info info;
		memset(&info, 0, sizeof(struct fpga_mgmt_image_info));

		ret = fpga_mgmt_load_local_image_sync_with_options(&opt,
				f1.sync_timeout, f1.sync_delay_msec, &info);
		fail_on(ret != 0, err, "fpga_mgmt_load_local_image_sync failed");

		ret = cli_show_image_info(&info);
		fail_on(ret != 0, err, "cli_show_image_info failed");
	}
err:
	return ret;
}

/**
 * Generate the clear local image command.
 *
 * @returns
 *  0	on success, non-zero on failure
 */
static int 
command_clear(void)
{
	int ret;

	if (f1.async) {
		ret = fpga_mgmt_clear_local_image(f1.afi_slot);
		fail_on(ret != 0, err, "fpga_mgmt_clear_local_image failed");
	} else {
		struct fpga_mgmt_image_info info;
		memset(&info, 0, sizeof(struct fpga_mgmt_image_info));

		ret = fpga_mgmt_clear_local_image_sync(f1.afi_slot, 
				f1.sync_timeout, f1.sync_delay_msec, &info);
		fail_on(ret != 0, err, "fpga_mgmt_clear_local_image_sync failed");

		ret = cli_show_image_info(&info);
		fail_on(ret != 0, err, "cli_show_image_info failed");
	}
err:
	return ret;
}

/**
 * Generate the describe local image command and handle the response.
 *
 * @returns
 *  0	on success, non-zero on failure
 */
static int
command_describe(void)
{
	int ret;
	uint32_t flags;
	struct fpga_mgmt_image_info info;

	memset(&info, 0, sizeof(struct fpga_mgmt_image_info));

	flags = 0;
	flags |= (f1.get_hw_metrics) ? FPGA_CMD_GET_HW_METRICS : 0;
	flags |= (f1.clear_hw_metrics) ? FPGA_CMD_CLEAR_HW_METRICS : 0;

	ret = fpga_mgmt_describe_local_image(f1.afi_slot, &info, flags);
	fail_on(ret != 0, err, "fpga_mgmt_describe_local_image failed");

	ret = cli_show_image_info(&info);
	fail_on(ret != 0, err, "cli_show_image_info failed");

	return 0;
err:
	return ret;
}

/**
 * Handle the describe local image slots "response".
 *  -this response uses local (not mbox) information only.
 *
 * @returns
 *  0	on success, non-zero on failure
 */
static int
command_describe_slots(void)
{
	int i, ret;
	struct fpga_slot_spec spec_array[FPGA_SLOT_MAX];

	memset(spec_array, 0, sizeof(spec_array));

	ret = fpga_pci_get_all_slot_specs(spec_array, sizeof_array(spec_array));

	for (i = 0; i < (int) sizeof_array(spec_array); ++i) {
		if (spec_array[i].map[FPGA_APP_PF].vendor_id == 0)
			continue;

		/** Display the application PFs for this slot */
		ret = cli_show_slot_app_pfs(i, &spec_array[i]);
		fail_on(ret != 0, err, "cli_show_slot_app_pfs failed");

	}
	return 0;
err:
	return ret;
}

/**
 * Generate the start virtual jtag command.
 *
 * @returns
 *  0	on success, non-zero on failure
 */
static int 
command_start_virtual_jtag(void)
{
	printf("Starting Virtual JTAG XVC Server for FPGA slot id %u, listening to TCP port %s.\n",
			f1.afi_slot, f1.tcp_port);
	printf("Press CTRL-C to stop the service.\n");

	return xvcserver_start(f1.afi_slot, f1.tcp_port);
}

/**
 * Display the virtual status from the get virtual led or dip command.
 *
 * @param[in]   status  the virtual led or dip status to display. 
 *
 * @returns
 *  0	on success, non-zero on failure
 */
static int
cli_show_virtual_led_dip_status(uint16_t status)
{
	int i;
	for(i = 0; i < 16; i++) {
		if (status & 0x8000) {
			printf("1");
		} else {
			printf("0");
		}
		status = status << 1;
		if ((i % 4 == 3) && (i != 15)) {
			printf("-");
		}
	}
	printf("\n");
	return 0;
}

/**
 * Generate the get virtual led command.
 *
 * @returns
 *  0	on success, non-zero on failure
 */
static int 
command_get_virtual_led(void)
{
	uint16_t status;
	int	ret;

	if (ret = fpga_mgmt_get_vLED_status(f1.afi_slot, &status)) {
		printf("Error trying to get virtual LED state\n");
		return ret;
	}

	printf("FPGA slot id %u have the following Virtual LED:\n", f1.afi_slot);
	return cli_show_virtual_led_dip_status(status);
}

/**
 * Generate the get virtual dip command.
 *
 * @returns
 *  0	on success, non-zero on failure
 */
static int 
command_get_virtual_dip(void)
{
	uint16_t status;
	int ret;

	if (ret = fpga_mgmt_get_vDIP_status(f1.afi_slot, &status)) {
		printf("Error: can not get virtual DIP Switch state\n");
		return ret;
	}

	printf("FPGA slot id %u has the following Virtual DIP Switches:\n", f1.afi_slot);
	return cli_show_virtual_led_dip_status(status);
}

/**
 * Generate the set virtual dip command.
 *
 * @returns
 *  0	on success, non-zero on failure
 */
static int 
command_set_virtual_dip(void)
{
	int ret;
	if (ret = fpga_mgmt_set_vDIP(f1.afi_slot, f1.v_dip_switch)) {
		printf("Error trying to set virtual DIP Switch \n");
	}
	return ret;
}

typedef int (*command_func_t)(void);

static const command_func_t command_table[CLI_CMD_END] = {
	[CLI_CMD_LOAD] = command_load,
	[CLI_CMD_CLEAR] = command_clear,
	[CLI_CMD_DESCRIBE] = command_describe,
	[CLI_CMD_DESCRIBE_SLOTS] = command_describe_slots,
	[CLI_CMD_START_VJTAG] = command_start_virtual_jtag,
	[CLI_CMD_GET_LED] = command_get_virtual_led,
	[CLI_CMD_GET_DIP] = command_get_virtual_dip,
	[CLI_CMD_SET_DIP] = command_set_virtual_dip,
};

/**
 * Main CLI cmd/rsp processing engine. 
 *
 * @returns
 *  0	on success, non-zero on failure
 */
static int
cli_main(void)
{
	fail_on(f1.opcode >= CLI_CMD_END, err, "Invalid opcode %u", f1.opcode);
	fail_on_user(command_table[f1.opcode] == NULL, err, "Action not defined for "
	             "opcode %u", f1.opcode);

	return command_table[f1.opcode]();
err:
	return FPGA_ERR_FAIL;
}

/**
 * Setup the f1 structure with initial values.
 *
 * @returns
 *  0	on success, non-zero on failure
 */
static int 
cli_init_f1(void)
{
	memset(&f1, 0, sizeof(f1));
	f1.opcode = -1;
	f1.afi_slot = -1;
	f1.request_timeout = CLI_REQUEST_TIMEOUT_DFLT;
	f1.request_delay_msec = CLI_REQUEST_DELAY_MSEC_DFLT;
	f1.sync_timeout = CLI_SYNC_TIMEOUT_DFLT;
	f1.sync_delay_msec = CLI_SYNC_DELAY_MSEC_DFLT;
	f1.show_mbox_device = false;

	srand((unsigned)time(NULL));

	return 0;
}

/**
 * CLI create method.
 *
 * @returns
 *  0	on success, non-zero on failure
 */
static int 
cli_create(void)
{
	return cli_init_f1();
}

/**
 * CLI destroy method.
 *
 * @returns
 *  0	on success, non-zero on failure
 */
static int 
cli_destroy(void)
{
	return cli_init_f1();
}

/**
 * CLI main
 *
 * @param[in]	argc	argument count  
 * @param[in]   argv	argument vector
 *
 * @returns
 *  0	on success, non-zero on failure
 */
int 
main(int argc, char *argv[])
{
	int ret = cli_create();
	fail_on(ret != 0, err, "cli_create failed");

	ret = log_init("fpga-local-cmd");
	fail_on(ret != 0, err, "log_init failed");

	ret = log_attach(logger, NULL, 0);
	fail_on_user(ret != 0, err, "%s", CLI_ROOT_ACCESS_ERR_STR);
		
	ret = parse_args(argc, argv);
	fail_on(ret != 0, err, "parse_args failed");

	ret = cli_attach();
	fail_on(ret != 0, err, "cli_attach failed");

	ret = cli_main();
	fail_on(ret != 0, err, "cli_main failed");
err:
	/** 
	 * f1.parser_completed may be set by parse_args when it internally 
	 * completes the command without error due to help or version output.
	 * In this case a non-zero error is returned by parse_args and we do not
	 * want to print the "Error" below.
	 */
	if (ret && !f1.parser_completed) {
		printf("Error: (%d) %s\n", ret, fpga_mgmt_strerror(ret));
	}
	cli_detach();
	cli_destroy();
	return ret;
}
