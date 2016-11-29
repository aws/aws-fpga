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

#include <lcd.h>

#include <fpga_common.h>
#include <afi_cmd_api.h>
#include <fpga_hal_plat.h>
#include <fpga_hal_mbox.h>

#include "fpga_local_cmd.h"

#define TYPE_FMT	"%-10s"

/**
 * Globals 
 */
struct ec2_fpga_cmd f1;

static union afi_cmd cmd;
static union afi_cmd rsp;

/** 
 * Use dmesg as the default logger, stdout is available for debug.
 */
#if 1
const struct logger *logger = &logger_kmsg;
#else
const struct logger *logger = &logger_stdout;
#endif

/**
 * Fill in the given FPGA slot specification.
 *
 * @param[in]   afi_slot	the fpga slot
 * @param[in]   spec		the slot spec to fill in 
 *
 * @returns
 *  0	on success 
 * -1	on failure
 */
static int
cli_fill_slot_spec(uint32_t afi_slot, struct fpga_slot_spec *spec)
{
	fail_on_user(afi_slot >= FPGA_SLOT_MAX, err, "Error: fpga-image-slot must be less than %u", 
			FPGA_SLOT_MAX);

	*spec = f1.mbox_slot_devs[afi_slot];
	
	return 0;
err:
	return -1;
}

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
cli_show_slot_app_pfs(uint32_t afi_slot)
{
	fail_on_quiet(afi_slot >= FPGA_SLOT_MAX, err, CLI_INTERNAL_ERR_STR);

	if (f1.show_headers) {
		printf("Type  FpgaImageSlot  VendorId    DeviceId    DBDF\n");         
	}

	/** Retrieve and display associated application PFs (if any) */
	bool found_app_pf = false;
	int i;
	for (i = F1_APP_PF_START; i <= F1_APP_PF_END; i++) {
		struct fpga_pci_resource_map app_map;

		/** 
		 * cli_get_app_pf_map will skip the Mbox PF (ret==1).
		 * We continue up through F1_APP_PF_END (e.g. 15) for future 
		 * compatibilty with any gaps in the PF numbering.
		 */
		int ret = cli_get_app_pf_map(afi_slot, i, &app_map);
		if (ret == 0) {
			printf(TYPE_FMT "  %2u       0x%04x      0x%04x      " PCI_DEV_FMT "\n",
					"AFIDEVICE", afi_slot, app_map.vendor_id, app_map.device_id, 
					app_map.domain, app_map.bus, app_map.dev, app_map.func);
			found_app_pf = true;
		} 
	}
	if (!found_app_pf) {
		printf(TYPE_FMT "    unknown    unknown    unknown\n", "AFIDEVICE"); 
	}

	return 0;
err:
	return -1;
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
	int ret = cli_pci_init();
	fail_on_quiet(ret != 0, err, 
			"Error: Could not initialize for slot discovery");

	if (f1.opcode == AFI_EXT_DESCRIBE_SLOTS) {
		/** 
		 * ec2-afi-describe-slots does not use the Mbox logic, local
		 * information only 
		 */
		goto out;
	}

	ret = fpga_plat_init();
	fail_on_internal(ret != 0, err, CLI_INTERNAL_ERR_STR);

	struct fpga_slot_spec spec;
	ret = cli_fill_slot_spec(f1.afi_slot, &spec);
	fail_on_quiet(ret != 0, err, "Error: Could not fill the slot spec");

	ret = fpga_plat_attach(&spec);
	fail_on_user(ret != 0, err, "%s", CLI_ROOT_ACCESS_ERR_STR);

	f1.plat_attached = true;

	struct fpga_hal_mbox mbox = {
		.slot = f1.afi_slot,
		.timeout = f1.mbox_timeout,
		.delay_msec = f1.mbox_delay_msec,
	};

	ret = fpga_hal_mbox_init(&mbox);
	fail_on_internal(ret != 0, err, CLI_INTERNAL_ERR_STR);

	ret = fpga_hal_mbox_attach(true); /**< clear_state=true */
	fail_on_internal(ret != 0, err, CLI_INTERNAL_ERR_STR);

out:
	return 0;
err:
	return -1;
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
	cli_pci_free();

	if (f1.plat_attached) {
		int ret = fpga_hal_mbox_detach(true); /**< clear_state=true */
		if (ret != 0) {
			log_error("%s (line %u)", CLI_INTERNAL_ERR_STR, __LINE__);
			/** Continue with plat detach */
		}

		ret = fpga_plat_detach();
		fail_on_internal(ret != 0, err, CLI_INTERNAL_ERR_STR);

		f1.plat_attached = false;
	}

	return 0;
err:
	return -1;
}

/**
 * AFI command get payload length utility.
 *
 * @param[in]  cmd		the command buffer
 *
 * @returns
 * len	the command payload length
 */
static uint32_t
afi_cmd_hdr_get_len(const union afi_cmd *cmd)
{
	return cmd ? (cmd->hdr.len_flags & AFI_CMD_HDR_LEN_MASK) : ~0u;
}

/**
 * AFI command get flags utility.
 *
 * @param[in]  cmd		the command buffer
 *
 * @returns
 * flags	the command flags
 */
static uint32_t
afi_cmd_hdr_get_flags(const union afi_cmd *cmd)
{
	return cmd ? (cmd->hdr.len_flags >> AFI_CMD_HDR_FLAGS_SHIFT) : ~0u;
}

/**
 * AFI command set payload length utility.
 *
 * @param[in]  cmd		the command buffer
 * @param[in]  len		the payload length to set
 *
 * @returns
 *  0	on success 
 * -1	on failure
 */
static int
afi_cmd_hdr_set_len(union afi_cmd *cmd, size_t len)
{
	/* Null pointer or overflow? */
	if (!cmd || (len & ~AFI_CMD_HDR_LEN_MASK)) {
		return -1;
	}

	cmd->hdr.len_flags &= ~AFI_CMD_HDR_LEN_MASK;
	cmd->hdr.len_flags |= (uint32_t)len;
	return 0;
}

/**
 * AFI command set flags utility.
 *
 * @param[in]  cmd		the command buffer
 * @param[in]  flags	the flags to set
 *
 * @returns
 *  0	on success 
 * -1	on failure
 */
static int
afi_cmd_hdr_set_flags(union afi_cmd *cmd, unsigned int flags)
{
	/* Null pointer or overflow? */
	if (!cmd || (flags & ~AFI_CMD_HDR_ALL_FLAGS)) {
		return -1;
	}

	cmd->hdr.len_flags &= AFI_CMD_HDR_LEN_MASK;
	cmd->hdr.len_flags |= flags << AFI_CMD_HDR_FLAGS_SHIFT;
	return 0;
}

/**
 * Table of AFI_CMD_ERROR opcode, error values.
 */
static const char *ace_tbl[ACE_END] = {
	[ACE_OK] = "ok",
	[ACE_BUSY] = "busy",
	[ACE_INVALID_AFI_ID] = "invalid-afi-id",
};

/**
 * Handle AFI error response 
 *
 * @param[in]  cmd		the command that was sent.
 * @param[in]  rsp		the response that was received.
 * @param[in]  len		the expected response payload len.
 *
 * @returns
 *  0	on success 
 * -1	on failure
 */
static int 
handle_afi_cmd_error_rsp(const union afi_cmd *cmd, 
		const union afi_cmd *rsp, uint32_t len)
{		
	(void)cmd;

	struct afi_cmd_err_rsp *err_rsp = (void *)rsp->body;

	uint32_t tmp_len = 
		sizeof(struct afi_cmd_hdr) + sizeof(struct afi_cmd_err_rsp);

	fail_on_quiet(len != tmp_len, err, "total_rsp_len(%u) != calculated_len(%u)", 
			len, tmp_len);

	if (f1.show_headers) {
		printf("Type  FpgaImageSlot    ErrorName    ErrorCode\n");         
	}

	printf(TYPE_FMT "    %u", "AFI", f1.afi_slot);

	char *err_name = "internal-error";
	if ((err_rsp->error < ACE_END) && ace_tbl[err_rsp->error]) {
		err_name = (void *)ace_tbl[err_rsp->error];
	}
	printf("    %s    %u\n", err_name, err_rsp->error); 

	return 0;
err:
	return -1;
}

/**
 * Validate the AFI response header, using the command header.
 *
 * @param[in]  cmd		the command that was sent.
 * @param[in]  rsp		the response that was received.
 * @param[in]  len		the expected response payload len.
 *
 * @returns
 *  0	on success 
 * -1	on failure
 */
static int 
afi_validate_header(const union afi_cmd *cmd, 
		const union afi_cmd *rsp, uint32_t len)
{
	uint32_t stored_flags = afi_cmd_hdr_get_flags(rsp);
	uint32_t is_response = stored_flags & AFI_CMD_HDR_IS_RSP;
	uint32_t payload_len = afi_cmd_hdr_get_len(rsp);

	fail_on_quiet(!cmd, err, "cmd == NULL");
	fail_on_quiet(!rsp, err, "rsp == NULL");

	/** Version */
	fail_on_quiet(cmd->hdr.version != rsp->hdr.version, err, 
			"cmd_ver(%u) != rsp_ver(%u)", 
			cmd->hdr.version, rsp->hdr.version);

	/** Opcode */
	fail_on_quiet(cmd->hdr.op != rsp->hdr.op, op_err, "cmd_op(%u) != rsp_op(%u)",
			cmd->hdr.op, rsp->hdr.op);

	/** Id */
	fail_on_quiet(cmd->hdr.id != rsp->hdr.id, id_err, "cmd_id(%u) != rsp_id(%u)",
			cmd->hdr.id, rsp->hdr.id);

	/** Received len too small */
	fail_on_quiet(len < sizeof(struct afi_cmd_hdr), err, 
			"Received length %u too small", len);

	/** Payload len too big */
	fail_on_quiet(payload_len + sizeof(struct afi_cmd_hdr) > AFI_CMD_DATA_LEN, 
			err, "Payload length %u too big", payload_len);

	/** Not a response */
	fail_on_quiet(!is_response, err, "Command is not a response");
	return 0;

id_err:
	return -EAGAIN;
op_err:
	if (rsp->hdr.op == AFI_CMD_ERROR) {
		return handle_afi_cmd_error_rsp(cmd, rsp, len);
	}
err:
	return -1;
}

/**
 * Get the next command id.
 *
 * @returns
 * id
 */
static uint32_t
afi_get_next_id(void)
{
	static uint32_t id = 0;

	if (id == 0) {
		id = rand();
	}

	return id++;
}

/**
 * Generate the AFI_CMD_LOAD.
 *
 * @param[in]		cmd		cmd buffer 
 * @param[in,out]	len		cmd len
 */
static void 
make_afi_cmd_load(union afi_cmd *cmd, uint32_t *len)
{
	assert(cmd);
	assert(len);
	struct afi_cmd_load_req *req = (void *)cmd->body;
	uint32_t payload_len = sizeof(struct afi_cmd_load_req);

	/** Fill in cmd header */
	cmd->hdr.version = AFI_CMD_API_VERSION;
	cmd->hdr.op = AFI_CMD_LOAD;
	cmd->hdr.id = afi_get_next_id();
	afi_cmd_hdr_set_len(cmd, payload_len);
	afi_cmd_hdr_set_flags(cmd, 0);
		
	/** Fill in cmd body */
	strncpy(req->ids.afi_id, f1.afi_id, sizeof(req->ids.afi_id)); 
    req->ids.afi_id[sizeof(req->ids.afi_id) - 1] = 0; 

	req->fpga_cmd_flags = 0;

	*len = sizeof(struct afi_cmd_hdr) + payload_len;
}

/**
 * Generate the AFI_CMD_METRICS.
 *
 * @param[in]		cmd		cmd buffer 
 * @param[in,out]	len		cmd len
 */
static void 
make_afi_cmd_metrics(union afi_cmd *cmd, uint32_t *len)
{
	assert(cmd);
	assert(len);

	struct afi_cmd_metrics_req *req = (void *)cmd->body;
	uint32_t payload_len = sizeof(struct afi_cmd_metrics_req);

	/** Fill in cmd header */
	cmd->hdr.version = AFI_CMD_API_VERSION;
	cmd->hdr.op = AFI_CMD_METRICS;
	cmd->hdr.id = afi_get_next_id();
	afi_cmd_hdr_set_len(cmd, payload_len);
	afi_cmd_hdr_set_flags(cmd, 0);

	/** Fill in cmd body */
	req->fpga_cmd_flags = 0;

	*len = sizeof(struct afi_cmd_hdr) + payload_len;
}

/**
 * Generate the AFI_CMD_CLEAR.
 *
 * @param[in]		cmd		cmd buffer 
 * @param[in,out]	len		cmd len
 */
static void 
make_afi_cmd_clear(union afi_cmd *cmd, uint32_t *len)
{
	assert(cmd);
	assert(len);

	struct afi_cmd_clear_req *req = (void *)cmd->body;
	uint32_t payload_len = sizeof(struct afi_cmd_clear_req);

	/** Fill in cmd header */
	cmd->hdr.version = AFI_CMD_API_VERSION;
	cmd->hdr.op = AFI_CMD_CLEAR;
	cmd->hdr.id = afi_get_next_id();
	afi_cmd_hdr_set_len(cmd, payload_len);
	afi_cmd_hdr_set_flags(cmd, 0);

	/** Fill in cmd body */
	req->fpga_cmd_flags = 0;

	*len = sizeof(struct afi_cmd_hdr) + payload_len;
}

/**
 * Table of AFI_CMD_METRICS opcode, status values.
 */
static const char *acms_tbl[ACMS_END] = {
	[ACMS_LOADED] = "loaded",
	[ACMS_CLEARED] = "cleared",
	[ACMS_BUSY] = "busy",
	[ACMS_NOT_PROGRAMMED] = "not-programmed",
};

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
handle_afi_cmd_metrics_rsp(const union afi_cmd *cmd,
		const union afi_cmd *rsp, uint32_t len)
{
	(void)cmd;
	/** We've already validated the header... */
	struct afi_cmd_metrics_rsp *metrics = (void *)rsp->body;

	uint32_t tmp_len = 
		sizeof(struct afi_cmd_hdr) + sizeof(struct afi_cmd_metrics_rsp);

	fail_on_quiet(len != tmp_len, err, "total_rsp_len(%u) != calculated_len(%u)", 
			len, tmp_len);

	if (f1.show_headers) {
		printf("Type  FpgaImageSlot  FpgaImageId             StatusName    StatusCode\n");         
	}

	char *afi_id = (!metrics->ids.afi_id[0]) ? "none" : metrics->ids.afi_id;
	printf(TYPE_FMT "  %2u       %-22s", "AFI", f1.afi_slot, afi_id);

	char *status_name = "internal-error";
	if ((metrics->status < ACMS_END) && acms_tbl[metrics->status]) {
		status_name = (void *)acms_tbl[metrics->status]; 
	}
	printf("  %-8s         %2u\n", status_name, metrics->status); 

	/** Display the application PFs for this slot */
	int ret = cli_show_slot_app_pfs(f1.afi_slot);
	fail_on_quiet(ret != 0, err, "cli_show_slot_app_pfs failed");

	return 0;
err:
	return -1;
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
handle_afi_describe_slots(const union afi_cmd *cmd,
		const union afi_cmd *rsp, uint32_t len)
{
	(void)cmd;
	(void)rsp;
	(void)len;

	int i;
	for (i = 0; i < FPGA_SLOT_MAX; i++) {
		struct fpga_pci_resource_map *mbox_map = &f1.mbox_slot_devs[i].map;

		if (mbox_map->vendor_id) {
			/** Display the application PFs for this slot */
			int ret = cli_show_slot_app_pfs(i);
			fail_on_quiet(ret != 0, err, "cli_show_slot_app_pfs failed");
		}
	}
	return 0;
err:
	return -1;
}

typedef void (*cmd_generator_t)(union afi_cmd *cmd, uint32_t *len);

/** Table of AFI commands to cli */
static const cmd_generator_t cmd_tbl[AFI_EXT_END] = {
	[AFI_CMD_LOAD] = make_afi_cmd_load,
	[AFI_CMD_METRICS] = make_afi_cmd_metrics,
	[AFI_CMD_CLEAR] = make_afi_cmd_clear,
};

typedef int (*rsp_handler_t)(const union afi_cmd *cmd, 
		const union afi_cmd *rsp, uint32_t len);

/** 
 * Table of AFI response handlers
 */
static const rsp_handler_t rsp_tbl[AFI_EXT_END] = {
	[AFI_CMD_METRICS] = handle_afi_cmd_metrics_rsp,
	[AFI_EXT_DESCRIBE_SLOTS] = handle_afi_describe_slots,
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
	uint32_t len = 0;

	fail_on_quiet(f1.opcode >= AFI_EXT_END, err, "Invalid opcode %u", f1.opcode);

	int ret;
	if (cmd_tbl[f1.opcode]) {
		cmd_tbl[f1.opcode](&cmd, &len);

		/** Write the AFI cmd to the mailbox */
		ret = fpga_hal_mbox_write(&cmd, len);
		fail_on_internal(ret != 0, err, CLI_INTERNAL_ERR_STR);

		/** 
		 * Read the AFI rsp from the mailbox.
		 *  -also make a minimal attempt to drain stale responses 
		 *   (if any).
		 */
		uint32_t id_retries = 0;
		ret = -EAGAIN;
		while (ret == -EAGAIN) {
			ret = fpga_hal_mbox_read(&rsp, &len);
			fail_on_user(ret != 0, err, "Error: operation timed out");

			ret = afi_validate_header(&cmd, &rsp, len);

			fail_on_internal(id_retries >= AFI_MAX_ID_RETRIES, err, 
					CLI_INTERNAL_ERR_STR);
			id_retries++;
		}
		fail_on_internal(ret != 0, err, CLI_INTERNAL_ERR_STR);
	}

	if (rsp_tbl[f1.opcode]) {
		ret = rsp_tbl[f1.opcode](&cmd, &rsp, len);
		fail_on_quiet(ret != 0, err, "Error: AFI mgmt channel invalid message");
	} 
	return 0;
err:
	return -1;
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
	cli_detach();
	cli_destroy();
	return ret;
}
