/*
 * Copyright 2016-2016 Amazon.com, Inc. or its affiliates. All Rights Reserved.
 */

/** @file
 * Amazon FPGA Image (AFI) command operations.
 */

#pragma once

#include <stdint.h>
#include <fpga_common.h>

#define AFI_CMD_API_VERSION	1
#define AFI_CMD_DATA_LEN	512 

/** 
 * AFI Protocol:
 *  -one outstanding AFI command is allowed at a time.
 *  -all AFI command fields MUST be in Host Byte Order (Little Endian).
 */
struct afi_cmd_hdr {
	/**< AFI command API version, and reserved bits */
	uint32_t version;
	/**< AFI command opcode, and reserved bits */
	uint32_t op;
	/** 
	 * Length of the payload and flags.
	 * The length of the payload consists of the least significant 
	 * 24-bits while the flags consist of the most-significant 8 bits.
	 * Flags: the least significant bit indicates if it is a request (0)
	 * or a response (1). 
	 */
	uint32_t len_flags;
	/**< VM chosen ID to correlate requests and responses */
	uint32_t id;
} __attribute__((packed));

/**< AFI command structure */
union afi_cmd {
	struct {
		struct afi_cmd_hdr hdr;	/**< AFI cmd header	*/
		uint8_t		body[];		/**< AFI cmd body */
	} __attribute__((packed));
	uint8_t	data[AFI_CMD_DATA_LEN]; /**< Pad buffer to full size */
};

/** AFI command flags */
enum {
	AFI_CMD_HDR_IS_RSP = 1 << 0,
	AFI_CMD_HDR_ALL_FLAGS = AFI_CMD_HDR_IS_RSP,
};

/** 
 * Opcodes:
 *	-new opcodes MUST be added to the end for version compatibility.
 */
enum {
	AFI_CMD_ERROR = 0,		/**< Error response opcode */
	AFI_CMD_LOAD = 1,		/**< Load AFI */
	AFI_CMD_METRICS = 2,	/**< Get loaded metadata Ids, status, stats */
	AFI_CMD_CLEAR = 3,		/**< Clear AFI */
	AFI_CMD_END
};

/** Error response. */
struct afi_cmd_err_rsp {
	/** Error, see below for error values */
	int32_t error;
} __attribute__((packed));

/** AFI_CMD_ERROR opcode, error values */
enum {
	ACE_OK = 0,
	ACE_BUSY = 3,
	ACE_INVALID_AFI_ID = 5,
	ACE_END
};

/**< Load AFI request */
struct afi_cmd_load_req {
	struct fpga_meta_ids	ids;
	uint32_t				fpga_cmd_flags; /**< e.g. see FPGA_CMD_ALL_FLAGS */
} __attribute__((packed));

/**< Metrics AFI request */
struct afi_cmd_metrics_req {
	uint32_t				fpga_cmd_flags; /**< e.g. see FPGA_CMD_ALL_FLAGS */
} __attribute__((packed));

/** Metrics AFI response */
struct afi_cmd_metrics_rsp {
	struct fpga_meta_ids	ids;
	int32_t					status; /**< e.g. see ACMS_LOADED */
	struct fpga_metrics_common	fmc;
} __attribute__((packed));

/**< Clear AFI request */
struct afi_cmd_clear_req {
	uint32_t				fpga_cmd_flags; /**< e.g. see FPGA_CMD_ALL_FLAGS */
} __attribute__((packed));

/** AFI_CMD_METRICS opcode, status values */
enum {
	ACMS_LOADED = 0,			/**< afi-slot has AFI loaded */
	ACMS_CLEARED = 1,			/**< afi-slot is cleared */
	ACMS_BUSY = 2,				/**< afi-slot is busy (e.g. loading an AFI) */ 
	ACMS_NOT_PROGRAMMED = 3,	/**< afi-slot is not programmed */
	ACMS_END,
};
