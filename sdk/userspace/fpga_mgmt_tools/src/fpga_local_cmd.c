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
 * Main EC2 F1 and F2 CLI processing.
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

#include <unistd.h>

#include <fpga_mgmt.h>
#include <fpga_clkgen.h>
#include <utils/lcd.h>

#include "fpga_local_cmd.h"
#include "virtual_jtag.h"

#define TYPE_FMT	"%-10s"

/**
 * Globals
 */
struct ec2_fpga_cmd fpga;

/**
 * Use dmesg as the default logger, stdout is available for debug.
 */
#if defined(FPGA_ALLOW_NON_ROOT)
const struct logger *logger = &logger_stdout;
#else
const struct logger *logger = &logger_kmsg;
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

	if (fpga.show_headers) {
		printf("Type  FpgaImageSlot  VendorId    DeviceId    DBDF\n");
	}

	/** Retrieve and display associated application PFs (if any) */
	bool found_app_pf = false;
	int i;
	for (i = 0; i < FPGA_PF_MAX; i++) {
		struct fpga_pci_resource_map *app_map = &spec->map[i];

		if (i == FPGA_MGMT_PF && !fpga.show_mbox_device) {
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
 * Helper function for printing metric information.
 */
static void
print_common_interupt_status(uint32_t int_status) {
	printf("virtual-jtag-slave-timeout=%u\n", (int_status & FPGA_INT_STATUS_CHIPSCOPE_TIMEOUT) ?  1 : 0);
	printf("ocl-slave-timeout=%u\n", (int_status & FPGA_INT_STATUS_PCI_SLAVE_OCL_TIMEOUT) ? 1 : 0);
	printf("sda-slave-timeout=%u\n", (int_status & FPGA_INT_STATUS_PCI_SLAVE_SDA_TIMEOUT) ? 1 : 0);
	printf("dma-pcis-timeout=%u\n", (int_status & FPGA_INT_STATUS_PCI_SLAVE_TIMEOUT) ? 1 : 0);
	printf("pcim-range-error=%u\n", (int_status & FPGA_INT_STATUS_PCI_RANGE_ERROR) ? 1 : 0);
	printf("pcim-axi-protocol-error=%u\n", (int_status & FPGA_INT_STATUS_PCI_AXI_PROTOCOL_ERROR) ? 1 : 0);
	printf("dma-range-error=%u\n", (int_status & FPGA_INT_STATUS_DMA_RANGE_ERROR) ? 1 : 0);
}

static void
print_pcim_axi_protocol_errors(uint32_t error_status) {
	printf("pcim-axi-protocol-4K-cross-error=%u\n", (error_status & FPGA_PAP_4K_CROSS_ERROR) ? 1 : 0);
	printf("pcim-axi-protocol-bus-master-enable-error=%u\n", (error_status & FPGA_PAP_BM_EN_ERROR) ? 1 : 0);
	printf("pcim-axi-protocol-request-size-error=%u\n", (error_status & FPGA_PAP_REQ_SIZE_ERROR) ? 1 : 0);
	printf("pcim-axi-protocol-write-incomplete-error=%u\n", (error_status & FPGA_PAP_WR_INCOMPLETE_ERROR) ? 1 : 0);
	printf("pcim-axi-protocol-first-byte-enable-error=%u\n", (error_status & FPGA_PAP_FIRST_BYTE_EN_ERROR) ? 1 : 0);
	printf("pcim-axi-protocol-last-byte-enable-error=%u\n", (error_status & FPGA_PAP_LAST_BYTE_EN_ERROR) ? 1 : 0);
	printf("pcim-axi-protocol-bready-error=%u\n", (error_status & FPGA_PAP_BREADY_TIMEOUT_ERROR) ? 1 : 0);
	printf("pcim-axi-protocol-rready-error=%u\n", (error_status & FPGA_PAP_RREADY_TIMEOUT_ERROR) ? 1 : 0);
	printf("pcim-axi-protocol-wchannel-error=%u\n", (error_status & FPGA_PAP_WCHANNEL_TIMEOUT_ERROR) ? 1 : 0);
}

static void
print_clocks(struct fpga_clocks_common clocks[FPGA_MMCM_GROUP_MAX]) {
	uint64_t i;
	uint64_t frequency;
	printf("Clock Group A Frequency (Mhz)\n");
	for (i = 0; i < CLOCK_COUNT_A; i++) {
		frequency = clocks[0].frequency[i] / 1000000;
		printf("%" PRIu64 "  ", frequency);
	}
	printf("\nClock Group B Frequency (Mhz)\n");
	for (i = 0; i < CLOCK_COUNT_B; i++) {
		frequency = clocks[1].frequency[i] / 1000000;
		printf("%" PRIu64 "  ", frequency);
	}
	printf("\nClock Group C Frequency (Mhz)\n");
	for (i = 0; i < CLOCK_COUNT_C; i++) {
		frequency = clocks[2].frequency[i] / 1000000;
		printf("%" PRIu64 "  ", frequency);
	}
	printf("\n");
}

/**
 * Display the FPGA metric information.
 *
 * @param[in]   fmc the FPGA metrics data to be printed
 */
static void
print_f1_metrics(struct f1_metrics_common *fmc) {
	uint32_t i;

	printf("sdacl-slave-timeout=%u\n", (fmc->int_status & FPGA_INT_STATUS_SDACL_SLAVE_TIMEOUT) ?  1 : 0);
	print_common_interupt_status(fmc->int_status);

	print_pcim_axi_protocol_errors(fmc->pcim_axi_protocol_error_status);

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

	print_clocks(fmc->clocks);

	printf("Power consumption (Vccint):\n");
	printf("   Last measured: %" PRIu64 " watts\n",fmc->power);
	printf("   Average: %" PRIu64 " watts\n",fmc->power_mean);
	printf("   Max measured: %" PRIu64 " watts\n",fmc->power_max);
	printf("Cached agfis:\n");
	for (i = 0; i < sizeof_array(fmc->cached_agfis); i++) {
		if (fmc->cached_agfis[i] == 0) {
			break;
		}
		printf("   agfi-0%016" PRIx64 "\n", fmc->cached_agfis[i]);
	}
}

static void
print_f2_metrics(struct f2_metrics_common *fmc) {
	uint32_t i;

	print_common_interupt_status(fmc->int_status);

	print_pcim_axi_protocol_errors(fmc->pcim_axi_protocol_error_status);

	printf("pcim-range-error-addr=0x%" PRIx64 "\n", fmc->pcim_range_error_addr);
	printf("pcim-range-error-count=%u\n", fmc->pcim_range_error_count);

	printf("pcim-axi-protocol-error-addr=0x%" PRIx64 "\n", fmc->pcim_axi_protocol_error_addr);
	printf("pcim-axi-protocol-error-count=%u\n", fmc->pcim_axi_protocol_error_count);

	printf("pcim-write-count=%" PRIu64 "\n", fmc->pcim_write_count);
	printf("pcim-read-count=%" PRIu64 "\n", fmc->pcim_read_count);

	printf("dma-pcis-timeout-addr=0x%" PRIx64 "\n", fmc->dma_pcis_timeout_addr);
	printf("dma-pcis-timeout-count=%u\n", fmc->dma_pcis_timeout_count);

	printf("ocl-slave-timeout-addr=0x%" PRIx32 "\n", fmc->ocl_slave_timeout_addr);
	printf("ocl-slave-timeout-count=%u\n", fmc->ocl_slave_timeout_count);

	printf("sda-slave-timeout-addr=0x%" PRIx64 "\n", fmc->sda_slave_timeout_addr);
	printf("sda-slave-timeout-count=%u\n", fmc->sda_slave_timeout_count);

	printf("virtual-jtag-slave-timeout-addr=0x%" PRIx32 "\n", fmc->virtual_jtag_slave_timeout_addr);
	printf("virtual-jtag-slave-timeout-count=%u\n", fmc->virtual_jtag_slave_timeout_count);

	printf("virtual-jtag-slave-write-count=%u\n", fmc->virtual_jtag_write_count);
	printf("virtual-jtag-slave-read-count=%u\n", fmc->virtual_jtag_read_count);

	for (i = 0; i < sizeof_array(fmc->ddr_ifs); i++) {
		struct fpga_ddr_if_metrics_common *ddr_if = &fmc->ddr_ifs[i];

		printf("DDR%u\n", i);
		printf("   write-count=%" PRIu64 "\n", ddr_if->write_count);
		printf("   read-count=%" PRIu64 "\n", ddr_if->read_count);
	}

	printf("Power consumption (Vccint):\n");
	printf("   Last measured: %" PRIu64 " watts\n",fmc->power);
	printf("   Average: %" PRIu64 " watts\n",fmc->power_mean);
	printf("   Max measured: %" PRIu64 " watts\n",fmc->power_max);
	printf("Cached agfis:\n");
	for (i = 0; i < sizeof_array(fmc->cached_agfis); i++) {
		if (fmc->cached_agfis[i] == 0) {
			break;
		}
		printf("   agfi-0%016" PRIx64 "\n", fmc->cached_agfis[i]);
	}
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

	if (fpga.show_headers) {
		printf("Type  FpgaImageSlot  FpgaImageId             StatusName    StatusCode   ErrorName    ErrorCode   ShVersion\n");
	}

	char *afi_id = (!info->ids.afi_id[0]) ? "none" : info->ids.afi_id;
	printf(TYPE_FMT "  %2u       %-22s", "AFI", fpga.afi_slot, afi_id);

	printf("  %-8s         %2d        %-8s        %2d       0x%08x\n",
			FPGA_STATUS2STR(info->status), info->status,
			FPGA_ERR2STR(info->status_q), info->status_q,
			info->sh_version);

	if (fpga.rescan) {
		/** Rescan the application PFs for this slot */
		ret = fpga_pci_rescan_slot_app_pfs(fpga.afi_slot);
		fail_on(ret != 0, err, "cli_rescan_slot_app_pfs failed");
	}

	/** Display the application PFs for this slot */
	ret = fpga_pci_get_slot_spec(fpga.afi_slot, &slot_spec);
	fail_on(ret != 0, err, "fpga_pci_get_slot_spec failed");
	ret = cli_show_slot_app_pfs(fpga.afi_slot, &slot_spec);
	fail_on(ret != 0, err, "cli_show_slot_app_pfs failed");

	if (fpga.get_hw_metrics) {
		if (fpga.show_headers) {
			printf("Metrics\n");
		}

		if (slot_spec.map[FPGA_MGMT_PF].device_id == F1_MBOX_DEVICE_ID) {
			print_f1_metrics(&info->metrics.f1_metrics);
		} else {
			print_f2_metrics(&info->metrics.f2_metrics);
		}
	}

	return 0;
err:
	return ret;
}

/**
 * Display the FPGA clkgen information.
 *
 * @param[in]   info the fpga info
 *
 * @returns
 *  0	on success, non-zero on failure
 */
static int
cli_show_clkgen_info(struct fpga_clkgen_info *info)
{
	assert(info);

	printf("Clock Group A Frequency (Mhz)\n");
	printf("| clk_extra_a1 | clk_extra_a2 | clk_extra_a3 |\n");
	printf("|--------------|--------------|--------------|\n");
	printf("|   %8.2f   |   %8.2f   |   %8.2f   |\n\n",
		info->clock_group_a.clocks[0],
		info->clock_group_a.clocks[1],
		info->clock_group_a.clocks[2]);

	printf("Clock Group B Frequency (Mhz)\n");
	printf("| clk_extra_b0 | clk_extra_b1 |\n");
	printf("|--------------|--------------|\n");
	printf("|   %8.2f   |   %8.2f   |\n\n",
		info->clock_group_b.clocks[0],
		info->clock_group_b.clocks[1]);

	printf("Clock Group C Frequency (Mhz)\n");
	printf("| clk_extra_c0 | clk_extra_c1 |\n");
	printf("|--------------|--------------|\n");
	printf("|   %8.2f   |   %8.2f   |\n\n",
		info->clock_group_c.clocks[0],
		info->clock_group_c.clocks[1]);

	printf("Clock Group HBM Frequency (Mhz)\n");
	printf("| clk_hbm_axi |\n");
	printf("|-------------|\n");
	printf("|   %7.2f   |\n\n",
		info->clock_group_hbm.clocks[0]);

	return 0;
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

	if (fpga.opcode == CLI_CMD_DESCRIBE_SLOTS) {
		/**
		 * ec2-afi-describe-slots does not use the Mbox logic, local
		 * information only
		 */
		goto out;
	}

	ret = fpga_mgmt_init();
	fail_on(ret != 0, err, "fpga_mgmt_init failed");

	fpga_mgmt_set_cmd_timeout(fpga.request_timeout);
	fpga_mgmt_set_cmd_delay_msec(fpga.request_delay_msec);

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

	uint32_t flags = 0;
	flags |= (fpga.force_shell_reload ) ? FPGA_CMD_FORCE_SHELL_RELOAD  : 0;
	flags |= (fpga.prefetch) ? FPGA_CMD_PREFETCH : 0;

 	fpga_mgmt_init_load_local_image_options(&opt);
        opt.slot_id = fpga.afi_slot;
        opt.afi_id = fpga.afi_id;
        opt.flags = flags;

	if (fpga.async) {
		ret = fpga_mgmt_load_local_image_with_options(&opt);
		fail_on(ret != 0, err, "fpga_mgmt_load_local_image failed");
	} else {
		struct fpga_mgmt_image_info info;
		memset(&info, 0, sizeof(struct fpga_mgmt_image_info));

		ret = fpga_mgmt_load_local_image_sync_with_options(&opt,
				fpga.sync_timeout, fpga.sync_delay_msec, &info);
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

	if (fpga.async) {
		ret = fpga_mgmt_clear_local_image(fpga.afi_slot);
		fail_on(ret != 0, err, "fpga_mgmt_clear_local_image failed");
	} else {
		struct fpga_mgmt_image_info info;
		memset(&info, 0, sizeof(struct fpga_mgmt_image_info));

		ret = fpga_mgmt_clear_local_image_sync(fpga.afi_slot,
				fpga.sync_timeout, fpga.sync_delay_msec, &info);
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
	flags |= (fpga.get_hw_metrics) ? FPGA_CMD_GET_HW_METRICS : 0;
	flags |= (fpga.clear_hw_metrics) ? FPGA_CMD_CLEAR_HW_METRICS : 0;
	flags |= (fpga.clear_afi_cache) ? FPGA_CMD_CLEAR_AFI_CACHE : 0;

	ret = fpga_mgmt_describe_local_image(fpga.afi_slot, &info, flags);
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
			fpga.afi_slot, fpga.tcp_port);
	printf("Press CTRL-C to stop the service.\n");

	return xvcserver_start(fpga.afi_slot, fpga.tcp_port);
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

	if (ret = fpga_mgmt_get_vLED_status(fpga.afi_slot, &status)) {
		printf("Error trying to get virtual LED state\n");
		return ret;
	}

	printf("FPGA slot id %u have the following Virtual LED:\n", fpga.afi_slot);
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

	if (ret = fpga_mgmt_get_vDIP_status(fpga.afi_slot, &status)) {
		printf("Error: can not get virtual DIP Switch state\n");
		return ret;
	}

	printf("FPGA slot id %u has the following Virtual DIP Switches:\n", fpga.afi_slot);
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
	if (ret = fpga_mgmt_set_vDIP(fpga.afi_slot, fpga.v_dip_switch)) {
		printf("Error trying to set virtual DIP Switch \n");
	}
	return ret;
}

/**
 * Generate the describe clkgen command and handle the response.
 *
 * @returns
 *  0	on success, non-zero on failure
 */
static int
command_describe_clkgen(void)
{
	int ret = 0;
	struct fpga_clkgen_info info;
	memset(&info, 0, sizeof(struct fpga_clkgen_info));

	ret = aws_clkgen_get_dynamic(fpga.afi_slot, &info);
	fail_on(ret != 0, err, "aws_clkgen_get_dynamic failed");

	ret = cli_show_clkgen_info(&info);
	fail_on(ret != 0, err, "cli_show_clkgen_info failed");

	return 0;
err:
	return ret;
}

/**
 * Generate the load clkgen recipe command and handle the response.
 *
 * @returns
 *  0	on success, non-zero on failure
 */
static int
command_load_clkgen_recipe(void)
{
	int ret = 0;

	ret = aws_clkgen_set_recipe(fpga.afi_slot, fpga.clock_a_recipe, fpga.clock_b_recipe, fpga.clock_c_recipe, fpga.clock_hbm_recipe, fpga.reset);
	fail_on(ret != 0, err, "aws_clkgen_set_recipe failed");

	ret = command_describe_clkgen();
	fail_on(ret != 0, err, "cli_show_clkgen_info failed");

	return 0;
err:
	return ret;
}

static int
command_load_clkgen_dynamic(void)
{
	int ret = 0;

	ret = aws_clkgen_set_dynamic(fpga.afi_slot, fpga.clock_a_freq, fpga.clock_b_freq, fpga.clock_c_freq, fpga.clock_hbm_freq, fpga.reset);
	fail_on(ret != 0, err, "aws_clkgen_set_dynamic_freq failed");

	ret = command_describe_clkgen();
	fail_on(ret != 0, err, "cli_show_clkgen_info failed");

	return 0;
err:
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
	[CLI_CMD_DESCRIBE_CLKGEN] = command_describe_clkgen,
	[CLI_CMD_LOAD_CLKGEN_RECIPE] = command_load_clkgen_recipe,
	[CLI_CMD_LOAD_CLKGEN_DYNAMIC] = command_load_clkgen_dynamic,
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
	fail_on(fpga.opcode >= CLI_CMD_END, err, "Invalid opcode %u", fpga.opcode);
	fail_on_user(command_table[fpga.opcode] == NULL, err, "Action not defined for "
	             "opcode %u", fpga.opcode);

	return command_table[fpga.opcode]();
err:
	return FPGA_ERR_FAIL;
}

/**
 * Setup the fpga structure with initial values.
 *
 * @returns
 *  0	on success, non-zero on failure
 */
static int
cli_init_fpga(void)
{
	memset(&fpga, 0, sizeof(fpga));
	fpga.opcode = -1;
	fpga.afi_slot = -1;
	fpga.request_timeout = CLI_REQUEST_TIMEOUT_DFLT;
	fpga.request_delay_msec = CLI_REQUEST_DELAY_MSEC_DFLT;
	fpga.sync_timeout = CLI_SYNC_TIMEOUT_DFLT;
	fpga.sync_delay_msec = CLI_SYNC_DELAY_MSEC_DFLT;
	fpga.show_mbox_device = false;
	fpga.clock_a_freq = 125;
	fpga.clock_a_recipe = 1;
	fpga.clock_b_freq = 450;
	fpga.clock_b_recipe = 2;
	fpga.clock_c_freq = 300;
	fpga.clock_c_recipe = 0;
	fpga.clock_hbm_freq = 450;
	fpga.clock_hbm_recipe = 2;

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
	return cli_init_fpga();
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
	return cli_init_fpga();
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

	ret = log_init("fpga-local-cmd(%u)", getpid());
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
	 * fpga.parser_completed may be set by parse_args when it internally
	 * completes the command without error due to help or version output.
	 * In this case a non-zero error is returned by parse_args and we do not
	 * want to print the "Error" below.
	 */
	if (ret && !fpga.parser_completed) {
		printf("Error: (%d) %s\n", ret, fpga_mgmt_strerror(ret));
		const char *long_help = fpga_mgmt_strerror_long(ret);
		if (long_help) {
			printf("%s", long_help);
		}
	}
	cli_detach();
	cli_destroy();
	return ret;
}
