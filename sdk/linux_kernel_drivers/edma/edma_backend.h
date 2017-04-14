/*
 * Copyright 2015 Amazon.com, Inc. or its affiliates.
 *
 * This software is available to you under a choice of one of two
 * licenses.  You may choose to be licensed under the terms of the GNU
 * General Public License (GPL) Version 2, available from the file
 * COPYING in the main directory of this source tree, or the
 * BSD license below:
 *
 *     Redistribution and use in source and binary forms, with or
 *     without modification, are permitted provided that the following
 *     conditions are met:
 *
 *      - Redistributions of source code must retain the above
 *        copyright notice, this list of conditions and the following
 *        disclaimer.
 *
 *      - Redistributions in binary form must reproduce the above
 *        copyright notice, this list of conditions and the following
 *        disclaimer in the documentation and/or other materials
 *        provided with the distribution.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
 * EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
 * MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
 * NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS
 * BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN
 * ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
 * CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
 * SOFTWARE.
 */

#ifndef EDMA_BACKEND_MEMORY_H
#define EDMA_BACKEND_MEMORY_H

#include <linux/interrupt.h>

#define PCI_VENDOR_ID_ANNAPURNA_LABS    0x1c36

//TODO: add device target address to the APIs
//TODO: use SGT instead for writev, readv

int edma_backend_submit_s2m_request(u64* buffer, u32 size, void *q_handle,
		u64 target_addr);
int edma_backend_submit_m2s_request(u64* buffer, u32 size, void *q_handle,
		u64 target_addr);

int edma_backend_get_completed_s2m_request(u64** buffer, u32* size,
		void *q_handle);
int edma_backend_get_completed_m2s_request(u64** buffer, u32* size,
		void *q_handle);

int edma_backend_m2s_dma_action(void *q_handle);

int edma_backend_init(frontend_callback frontend_init, frontend_callback frontend_cleanup);

void edma_backend_cleanup(void);
int edma_backend_start(void *q_handle, int minor);
int edma_backend_stop(void *q_handle);

int edma_backend_enable_isr(struct pci_dev *pdev, u32 event_number);
int edma_backend_disable_isr(struct pci_dev *pdev, u32 event_number);
int edma_backend_register_isr(struct pci_dev *pdev, u32 event_number,
		irq_handler_t handler, const char* name, void* drv);

#endif //EDMA_BACKEND_MEMORY_H
