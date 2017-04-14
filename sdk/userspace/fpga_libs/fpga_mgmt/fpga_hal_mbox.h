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
 * FPGA HAL mailbox operations.
 */

#pragma once

#include <stdint.h>
#include <stdbool.h>

#include <fpga_pci.h>

#define FPGA_MBOX_MSG_DATA_LEN	4096 

/**
 * Mailbox version info.
 */
struct fpga_hal_mbox_versions {
	uint32_t	sh_version;
};

/**
 * Mailbox init structure.
 */
struct fpga_hal_mbox {
	uint32_t	timeout;	/**< timeout, e.g. N x delay_mec */
	uint32_t	delay_msec;
};

/**
 * Initialize the Mailbox
 *
 * @param[in]	mbox	the Mailbox init structure.
 *
 * @returns
 * 0 on success    
 * -1 on failure
 */
int fpga_hal_mbox_init(struct fpga_hal_mbox *mbox);

/**
 * Reset the Mailbox to initial state (e.g. clear RX and TX event).
 *
 * @param[in]	handle  handle provided by fpga_pci_attach
 *
 * @returns
 * 0 on success    
 * -1 on failure
 */
int fpga_hal_mbox_reset(pci_bar_handle_t handle);

/**
 * Get Mailbox versions.
 *
 * @param[in]		handle  handle provided by fpga_pci_attach
 * @param[in,out]	ver		Mailbox version info to return.  
 *
 * @returns
 * 0 on success    
 * -1 on failure
 */
int fpga_hal_mbox_get_versions(pci_bar_handle_t handle, 
		struct fpga_hal_mbox_versions *ver);

/**
 * Attach the Mailbox.  Wrapper around fpga_hal_mbox_reset for attach
 * semantics.
 *
 * @param[in]	handle			handle provided by fpga_pci_attach
 * @param[in]	clear_state		reset mbox to initial state.
 *
 * @returns
 * 0 on success    
 * -1 on failure
 */
int fpga_hal_mbox_attach(pci_bar_handle_t handle, bool clear_state);

/**
 * Detach the Mailbox.  Wrapper around fpga_hal_mbox_reset for detach
 * semantics.
 *
 * @param[in]	handle			handle provided by fpga_pci_attach
 * @param[in]	clear_state		reset mbox to initial state.
 *
 * @returns
 * 0 on success    
 * -1 on failure
 */
int fpga_hal_mbox_detach(pci_bar_handle_t handle, bool clear_state);

/**
 * Perform a synchronous read from the Mailbox using the timeout and delay_msec
 * values from fpga_hal_mbox_init.
 *
 * @param[in]		handle	handle provided by fpga_pci_attach
 * @param[in,out]	msg		the msg buffer to use
 * @param[in,out]	len		the msg length to set
 *
 * @returns
 * 0 on success    
 * -1 on failure
 */
int fpga_hal_mbox_read(pci_bar_handle_t handle, void *msg, uint32_t *len);

/**
 * Perform a synchronous write to the Mailbox using the timeout and delay_msec
 * values from fpga_hal_mbox_init.
 *
 * @param[in]	handle	handle provided by fpga_pci_attach
 * @param[in]	msg		the msg buffer to use
 * @param[in]	len		the msg length to write 
 *
 * @returns
 * 0 on success    
 * -1 on failure
 */
int fpga_hal_mbox_write(pci_bar_handle_t handle, void *msg, uint32_t len);

/**
 * Perform an asynchronous (non-blocking) read from the Mailbox.
 *
 * @param[in]		handle	handle provided by fpga_pci_attach
 * @param[in,out]	msg		the msg buffer to use
 * @param[in,out]	len		the msg length to set
 *
 * @returns
 * 0 on success    
 * -1 on failure
 */
int fpga_hal_mbox_read_async(pci_bar_handle_t handle, 
		void *msg, uint32_t *len);

/**
 * Perform an asynchronous (non-blocking) write to the Mailbox.
 *
 * @param[in]	handle	handle provided by fpga_pci_attach
 * @param[in]	msg		the msg buffer to use
 * @param[in]	len		the msg length to write 
 *
 * @returns
 * 0 on success    
 * -1 on failure
 */
int fpga_hal_mbox_write_async(pci_bar_handle_t handle, 
		void *msg, uint32_t len);

/** 
 * Test and Clear (TC) asynchronous write acknowledgement. 
 * e.g. use this to check if an async write was ack'd by the peer.
 * If the write was ack'd, clear the ack status within the Mailbox, 
 * and return the ack status. 
 *
 * @param[in]		handle	handle provided by fpga_pci_attach
 * @param[in,out]	ack		the ack flag to set	
 *
 * @returns
 * 0 on success    
 * -1 on failure
 */
int fpga_hal_mbox_write_async_tc_ack(pci_bar_handle_t handle, bool *ack);
