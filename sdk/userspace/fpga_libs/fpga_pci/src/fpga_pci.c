/*
 * Copyright 2015-2017 Amazon.com, Inc. or its affiliates. All Rights Reserved.
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

#include "fpga_pci_interal.h"

#include <string.h>

int
fpga_pci_init() {
	return fpga_plat_init();
}

int
fpga_pci_attach(int slot_id, int pf_id, int bar_id, uint32_t flags, int *handle) {
	int rc;
	struct fpga_slot_spec spec;

	memset(&spec, 0, sizeof(struct fpga_slot_spec));

	rc = fpga_pci_get_slot_spec(slot_id, pf_id, bar_id, &spec);
	fail_on(rc, out, "Unable to prefill the slot spec\n");
	spec.map.resource_num = bar_id;

	return fpga_plat_dev_attach(&spec, handle);

out:
	return 1;
}

int
fpga_pci_detatch(int handle) {
	return fpga_plat_dev_detach(handle);
}

int
fpga_pci_poke(int handle, uint64_t offset, uint32_t value) {
	return fpga_hal_dev_reg_write(handle, offset, value);
}

int
fpga_pci_poke64(int handle, uint64_t offset, uint64_t value) {
	/* not implemened */
	return 1;
}

int
fpga_pci_peek(int handle, uint64_t offset, uint32_t *value) {
	return fpga_hal_dev_reg_read(handle, offset, value);
}

int
fpga_pci_peek64(int handle, uint64_t offset, uint64_t *value) {
	/* not implemented */
	return 1;
}

int fpga_pci_write_burst(int handle, uint64_t offset, uint32_t* datap, uint32_t dword_len) {
	/* not implemented */
	return 1;
}
