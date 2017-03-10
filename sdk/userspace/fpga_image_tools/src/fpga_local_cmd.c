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

#include <utils/lcd.h>

#include <fpga_pci.h>
#include <fpga_mgmt.h>

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
 *  0	on success 
 * -1	on failure
 */
static int 
cli_show_slot_app_pfs(int slot_id, struct fpga_slot_spec *spec)
{
	fail_on_quiet(slot_id >= FPGA_SLOT_MAX, err, CLI_INTERNAL_ERR_STR);

	if (f1.show_headers) {
		printf("Type  FpgaImageSlot  VendorId    DeviceId    DBDF\n");         
	}

	/** Retrieve and display associated application PFs (if any) */
	bool found_app_pf = false;
	int i;
	for (i = 0; i < FPGA_MAX_PF; i++) {
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
 * Attach for CLI processing.
 *
 * @returns
 *  0	on success 
 * -1	on failure
 */
static int
cli_attach(void)
{
	int ret;

	if (f1.opcode == AFI_EXT_DESCRIBE_SLOTS) {
		/** 
		 * ec2-afi-describe-slots does not use the Mbox logic, local
		 * information only 
		 */
		goto out;
	}

	ret = fpga_mgmt_init();
	fail_on_internal(ret != 0, err, CLI_INTERNAL_ERR_STR);

out:
	return 0;
err:
	return FPGA_ERR_FAIL;
}

/**
 * Detach CLI processing.
 *
 * @returns
 *  0	on success 
 * -1	on failure
 */
static int
cli_detach(void)
{
	fpga_mgmt_close();
	return 0;
}

static int command_get_virtual_led(void)
{
uint16_t	status;
int		ret;
int		i;
        if (ret = fpga_mgmt_get_vLED_status(f1.afi_slot,&status)) {
                printf("Error trying to get virtual LED state\n");
                return ret;
        }

        printf("FPGA slot id %u have the following Virtual LED:\n",f1.afi_slot);
        for(i=0;i<16;i++) {
                if (status & 0x8000)
                        printf("1");
                else
                        printf("0");
                status = status << 1;
                if ((i%4 == 3) && (i!=15))
                        printf("-");
	}
	printf("\n");
	return 0;
}

static int command_get_virtual_dip(void)
{
uint16_t        status;
int             ret;
int             i;
        if (ret = fpga_mgmt_get_vDIP_status(f1.afi_slot,&status)) {
                printf("Error: can not get virtual DIP Switch state\n");
                return ret;
        }

        printf("FPGA slot id %u has the following Virtual DIP Switches:\n",f1.afi_slot);
        for(i=0;i<16;i++) {
                if (status & 0x8000)
                        printf("1");
                else
                        printf("0");
                status = status << 1;
		if ((i%4 == 3) && (i!=15))
			printf("-");
        }
        printf("\n");
	return 0;
}

static int command_set_virtual_dip(void)
{
int             ret;
	if (ret = fpga_mgmt_set_vDIP(f1.afi_slot,f1.v_dip_switch)) {
		printf("Error trying to set virtual DIP Switch \n");
	}
	return ret;
}

static int command_start_virtual_jtag(void)
{
        printf("Starting Virtual JTAG XVC Server for FPGA slot id %u, listening to TCP port %s.\n",f1.afi_slot,f1.tcp_port);
        printf("Press CTRL-C to stop the service.\n");

        return xvcserver_start(f1.afi_slot,f1.tcp_port);
}

static int command_load(void)
{
	int ret;
	ret = fpga_mgmt_load_local_image(f1.afi_slot, f1.afi_id);
	return ret;
}

/**
 * Generate the AFI_CMD_CLEAR.
 *
 * @param[in]		cmd		cmd buffer 
 * @param[in,out]	len		cmd len
 */
static int 
command_clear(void)
{
	return fpga_mgmt_clear_local_image(f1.afi_slot);
}

/**
 * Handle the AFI_CMD_METRICS response.
 *
 * @param[in]	cmd		cmd buffer 
 * @param[in]	rsp		rsp buffer 
 * @param[in]	len		rsp len
 *
 * @returns
 *  0	on success 
 * -1	on failure
 */
static int
command_metrics(void)
{
	int ret;
	uint32_t i, flags;
	struct fpga_mgmt_image_info info;
	struct fpga_slot_spec slot_spec;

	memset(&info, 0, sizeof(struct fpga_mgmt_image_info));

	flags = 0;
	flags |= (f1.get_hw_metrics) ? FPGA_CMD_GET_HW_METRICS : 0;
	flags |= (f1.clear_hw_metrics) ? FPGA_CMD_CLEAR_HW_METRICS : 0;

	ret = fpga_mgmt_describe_local_image(f1.afi_slot, &info, flags);
	fail_on(ret, err, "Unable to describe local image");

	if (f1.show_headers) {
		printf("Type  FpgaImageSlot  FpgaImageId             StatusName    StatusCode   ShVersion\n");         
	}

	char *afi_id = (!info.ids.afi_id[0]) ? "none" : info.ids.afi_id;
	printf(TYPE_FMT "  %2u       %-22s", "AFI", f1.afi_slot, afi_id);

	printf("  %-8s         %2u        0x%08x\n", 
			FPGA_STATUS2STR(info.status), info.status, info.sh_version); 

	if (f1.rescan) {
		/** Rescan the application PFs for this slot */
		ret = fpga_pci_rescan_slot_app_pfs();
		fail_on_quiet(ret != 0, err, "cli_rescan_slot_app_pfs failed");
	}

	/** Display the application PFs for this slot */
	ret = fpga_pci_get_slot_spec(f1.afi_slot, &slot_spec);
	fail_on_quiet(ret != 0, err, "fpga_pci_get_slot_spec failed");
	ret = cli_show_slot_app_pfs(f1.afi_slot, &slot_spec);
	fail_on_quiet(ret != 0, err, "cli_show_slot_app_pfs failed");

	if (f1.get_hw_metrics) {
		if (f1.show_headers) {
			printf("Metrics\n");
		}

		struct fpga_metrics_common *fmc = &info.metrics;
		printf("pci-slave-timeout=%u\n", 
				(fmc->int_status & FPGA_INT_STATUS_PCI_SLAVE_TIMEOUT) ?
				1 : 0); 

		printf("pci-slave-sda-timeout=%u\n", 
				(fmc->int_status & FPGA_INT_STATUS_PCI_SLAVE_SDA_TIMEOUT) ?
				1 : 0); 

		printf("pci-slave-ocl-timeout=%u\n", 
				(fmc->int_status & FPGA_INT_STATUS_PCI_SLAVE_OCL_TIMEOUT) ?
				1 : 0); 

		printf("pci-slave-edma-timeout=%u\n", 
				(fmc->int_status & FPGA_INT_STATUS_PCI_SLAVE_EDMA_TIMEOUT) ?
				1 : 0); 

		printf("pci-range-error=%u\n", 
				(fmc->int_status & FPGA_INT_STATUS_PCI_RANGE_ERROR) ? 
				1 : 0); 

		printf("pci-axi-protocol-error=%u\n", 
				(fmc->int_status & FPGA_INT_STATUS_PCI_AXI_PROTOCOL_ERROR) ?
				1 : 0); 

		printf("pci-axi-protocol-len-error=%u\n", 
				(fmc->pci_axi_protocol_error_status & FPGA_PAP_LEN_ERROR) ?
				1 : 0); 

		printf("pci-axi-protocol-4K-cross-error=%u\n", 
				(fmc->pci_axi_protocol_error_status & FPGA_PAP_4K_CROSS_ERROR) ?
				1 : 0); 

		printf("pci-axi-protocol-bus-master-enable-error=%u\n", 
				(fmc->pci_axi_protocol_error_status & FPGA_PAP_BM_EN_ERROR) ?
				1 : 0); 

		printf("pci-axi-protocol-request-size-error=%u\n", 
				(fmc->pci_axi_protocol_error_status & FPGA_PAP_REQ_SIZE_ERROR) ?
				1 : 0); 

		printf("pci-axi-protocol-write-incomplete-error=%u\n", 
				(fmc->pci_axi_protocol_error_status & FPGA_PAP_WR_INCOMPLETE_ERROR) ?
				1 : 0); 

		printf("pci-axi-protocol-first-byte-enable-error=%u\n", 
				(fmc->pci_axi_protocol_error_status & FPGA_PAP_FIRST_BYTE_EN_ERROR) ?
				1 : 0); 

		printf("pci-axi-protocol-last-byte-enable-error=%u\n", 
				(fmc->pci_axi_protocol_error_status & FPGA_PAP_LAST_BYTE_EN_ERROR) ?
				1 : 0); 

		printf("pci-axi-protocol-write-strobe-error=%u\n", 
				(fmc->pci_axi_protocol_error_status & FPGA_PAP_WSTRB_ERROR) ?
				1 : 0); 

		printf("pci-axi-protocol-bready-error=%u\n", 
				(fmc->pci_axi_protocol_error_status & FPGA_PAP_BREADY_TIMEOUT_ERROR) ?
				1 : 0); 

		printf("pci-axi-protocol-rready-error=%u\n", 
				(fmc->pci_axi_protocol_error_status & FPGA_PAP_RREADY_TIMEOUT_ERROR) ?
				1 : 0); 

		printf("pci-axi-protocol-wchannel-error=%u\n", 
				(fmc->pci_axi_protocol_error_status & FPGA_PAP_WCHANNEL_TIMEOUT_ERROR) ?
				1 : 0); 

		printf("ps-timeout-addr=0x%" PRIx64 "\n", fmc->ps_timeout_addr); 
		printf("ps-timeout-count=%u\n", fmc->ps_timeout_count); 

		printf("ps-sda-timeout-addr=0x%" PRIx64 "\n", fmc->ps_sda_timeout_addr); 
		printf("ps-sda-timeout-count=%u\n", fmc->ps_sda_timeout_count); 

		printf("ps-ocl-timeout-addr=0x%" PRIx64 "\n", fmc->ps_ocl_timeout_addr); 
		printf("ps-ocl-timeout-count=%u\n", fmc->ps_ocl_timeout_count); 

		printf("ps-edma-timeout-addr=0x%" PRIx64 "\n", fmc->ps_edma_timeout_addr); 
		printf("ps-edma-timeout-count=%u\n", fmc->ps_edma_timeout_count); 

		printf("pm-range-error-addr=0x%" PRIx64 "\n", fmc->pm_range_error_addr); 
		printf("pm-range-error-count=%u\n", fmc->pm_range_error_count); 

		printf("pm-axi-protocol-error-addr=0x%" PRIx64 "\n", fmc->pm_axi_protocol_error_addr); 
		printf("pm-axi-protocol-error-count=%u\n", fmc->pm_axi_protocol_error_count); 

		printf("pm-write-count=%" PRIu64 "\n", fmc->pm_write_count); 
		printf("pm-read-count=%" PRIu64 "\n", fmc->pm_read_count); 

		for (i = 0; i < sizeof_array(fmc->ddr_ifs); i++) {
			struct fpga_ddr_if_metrics_common *ddr_if = &fmc->ddr_ifs[i];

			printf("DDR%u\n", i);
			printf("   write-count=%" PRIu64 "\n", ddr_if->write_count); 
			printf("   read-count=%" PRIu64 "\n", ddr_if->read_count); 
		}
	}

	return 0;
err:
	return FPGA_ERR_FAIL;
}

/**
 * Handle the AFI_EXT_DESCRIBE_SLOTS "response".
 *  -this response uses local (not mbox) information only.
 *
 * @param[in]	cmd		cmd buffer 
 * @param[in]	rsp		rsp buffer 
 * @param[in]	len		rsp len
 *
 * @returns
 *  0	on success 
 * -1	on failure
 */
static int
command_describe_slots(void)
{
	int i, ret;
	struct fpga_slot_spec spec_array[FPGA_SLOT_MAX];

	memset(spec_array, 0, sizeof(spec_array));

	ret = fpga_pci_get_all_slot_specs(spec_array, sizeof_array(spec_array));

	for (i = 0; i < sizeof_array(spec_array); ++i) {
		if (spec_array[i].map[FPGA_APP_PF].vendor_id == 0)
			continue;

		/** Display the application PFs for this slot */
		ret = cli_show_slot_app_pfs(i, &spec_array[i]);
		fail_on_quiet(ret != 0, err, "cli_show_slot_app_pfs failed");

	}
	return 0;
err:
	return FPGA_ERR_FAIL;
}

typedef int (*command_func_t)(void);

static const command_func_t command_table[AFI_EXT_END] = {
	[AFI_CMD_LOAD] = command_load,
	[AFI_CMD_METRICS] = command_metrics,
	[AFI_CMD_CLEAR] = command_clear,
	[AFI_EXT_DESCRIBE_SLOTS] = command_describe_slots,
	[AFI_START_VJTAG] = command_start_virtual_jtag,
	[AFI_GET_LED] = command_get_virtual_led,
	[AFI_GET_DIP] = command_get_virtual_dip,
	[AFI_SET_DIP] = command_set_virtual_dip,
};

/**
 * Main CLI cmd/rsp processing engine. 
 *
 * @returns
 *  0	on success 
 * -1	on failure
 */
static int
cli_main(void)
{
	fail_on_quiet(f1.opcode >= AFI_EXT_END, err, "Invalid opcode %u", f1.opcode);
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
 *  0	on success 
 * !0	failure
 */
static int 
cli_init_f1(void)
{
	memset(&f1, 0, sizeof(f1));
	f1.opcode = -1;
	f1.afi_slot = -1;
	f1.mbox_timeout = CLI_TIMEOUT_DFLT;
	f1.mbox_delay_msec = CLI_DELAY_MSEC_DFLT;
	f1.show_mbox_device = false;

	srand((unsigned)time(NULL));

	return 0;
}

/**
 * CLI create method.
 *
 * @returns
 *  0	on success 
 * !0	failure
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
 *  0	on success 
 * !0	failure
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
 *  0	on success 
 * !0	failure
 */
int 
main(int argc, char *argv[])
{
	int ret = cli_create();
	fail_on_internal(ret != 0, err, CLI_INTERNAL_ERR_STR);

	ret = log_init("fpga-local-cmd");
	fail_on_internal(ret != 0, err, CLI_INTERNAL_ERR_STR);

	ret = log_attach(logger, NULL, 0);
	fail_on_user(ret != 0, err, "%s", CLI_ROOT_ACCESS_ERR_STR);
		
	ret = parse_args(argc, argv);
	fail_on_quiet(ret != 0, err, "parse args failed");

	ret = cli_attach();
	fail_on_quiet(ret != 0, err, "cli_attach failed");

	ret = cli_main();
	fail_on_quiet(ret != 0, err, "cli_main failed");
err:
	if (ret) {
		printf("Error: (%d) %s\n", ret, fpga_mgmt_strerror(ret));
	}
	cli_detach();
	cli_destroy();
	return ret;
}
