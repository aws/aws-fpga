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

#include <stdio.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <sys/mman.h>
#include <string.h>
#include <fcntl.h>
#include <pthread.h>
#include <errno.h>
#include <unistd.h>

#include <limits.h>
#include <utils/lcd.h>

#include "fpga_pci_internal.h"


/**
 * FPGA PCI BARs:
 */
static pthread_mutex_t bars_mutex = PTHREAD_MUTEX_INITIALIZER;

static struct fpga_pci_bar {
	bool	 allocated;
	void	*mem_base;
	size_t	 mem_size;
} bars[FPGA_PCI_BARS_MAX];

static inline struct fpga_pci_bar *
fpga_pci_bar_get(pci_bar_handle_t handle)
{
	log_debug("handle=%d", handle);

	fail_on(handle >= FPGA_PCI_BARS_MAX, err, "Invalid handle=%d", 
			handle);

	return &bars[handle];
err:
	return NULL;
}

static int 
fpga_pci_bar_set_mem_base_size(pci_bar_handle_t handle, void *mem_base, size_t mem_size)
{
	log_debug("handle=%d", handle);

	struct fpga_pci_bar *bar = fpga_pci_bar_get(handle);
	fail_on(!bar, err, "fpga_pci_bar_get failed");
	fail_on(!mem_base, err, "mem_base is NULL");
	fail_on(!mem_size, err, "mem_size is 0");

	bar->mem_base = mem_base;
	bar->mem_size = mem_size;

	return 0;
err:
	return FPGA_ERR_FAIL;
}

static inline void * 
fpga_pci_bar_get_mem_at_offset(pci_bar_handle_t handle, uint64_t offset, uint64_t xaction_size)
{
	log_debug("handle=%d", handle);

	struct fpga_pci_bar *bar = fpga_pci_bar_get(handle);
	fail_on(!bar, err, "fpga_pci_bar_get failed");
	fail_on(!bar->allocated, err, "Not attached");
	fail_on(!bar->mem_base, err, "mem_base is NULL");
	fail_on(((uint64_t)(offset + xaction_size)) > bar->mem_size, err,
		"Invalid offset + size =0x%" PRIx64 " exceeds range" , 
		(uint64_t)(offset + xaction_size));

	return bar->mem_base + offset;
err:
	return NULL;
}

static int
fpga_pci_bar_alloc(void)
{
	log_debug("enter");

	pthread_mutex_lock(&bars_mutex);

	int i;
	for (i = 0; i < FPGA_PCI_BARS_MAX; i++) {
		struct fpga_pci_bar *bar = &bars[i];

		if (bar->allocated == false) {
			log_debug("allocated handle=%d", i);
			bar->allocated = true;

			pthread_mutex_unlock(&bars_mutex);

			return i;
		}
	}

	pthread_mutex_unlock(&bars_mutex);

	return FPGA_ERR_FAIL;
}

static int
fpga_pci_bar_free(pci_bar_handle_t handle)
{
	log_debug("handle=%d", handle);

	struct fpga_pci_bar *bar = fpga_pci_bar_get(handle);
	fail_on(!bar, err, "fpga_pci_bar_get failed");

	pthread_mutex_lock(&bars_mutex);

	memset(bar, 0, sizeof(*bar));

	pthread_mutex_unlock(&bars_mutex);

	return 0;
err:
	return FPGA_ERR_FAIL;
}

static int
fpga_pci_check_file_id(char *path, uint16_t id)
{
	fail_on(!path, err, "path is NULL");
	log_debug("path=%s", path);

	int ret = 0;
	FILE *fp = fopen(path, "r");
	fail_on(!fp, err, "Error opening %s", path);

	uint32_t tmp_id;
	ret = fscanf(fp, "%x", &tmp_id);
	fail_on(ret < 0, err_close, "Error parsing %s", path);

	fail_on(tmp_id != id, err_close, 
			"path=%s, id(0x%04x) != expected id(0x%04x)", path, tmp_id, id);

	fclose(fp);
	return 0;

err_close:
	fclose(fp);
err:
	return FPGA_ERR_FAIL;
}

static int 
fpga_pci_bar_attach(struct fpga_slot_spec *spec, int pf_id, int bar_id,
	bool write_combining, int *handle) 
{
	int fd = -1;
	log_debug("enter");

	void *mem_base = NULL;

	fail_on(!spec, err, "spec is NULL");
	fail_on(!handle, err, "handle is NULL");

	struct fpga_pci_resource_map *map = &spec->map[pf_id];

	log_info("vendor_id=0x%04x, device_id=0x%04x, DBDF:" 
			PCI_DEV_FMT ", resource_num=%u, size=%" PRIu64 ", burstable=%u",
			map->vendor_id, map->device_id, map->domain, map->bus, 
			map->dev, map->func, bar_id, map->resource_size[bar_id],
			map->resource_burstable[bar_id]);

	/** Invalid handle for error returns */
	*handle = -1;

	/** Sanity check the vendor */
	char sysfs_name[NAME_MAX + 1];
	int ret = snprintf(sysfs_name, sizeof(sysfs_name), 
			"/sys/bus/pci/devices/" PCI_DEV_FMT "/vendor", 
			map->domain, map->bus, map->dev, map->func);

	fail_on(ret < 0, err, "Error building the sysfs path for vendor");
	fail_on((size_t) ret >= sizeof(sysfs_name), err, "sysfs path too long for vendor");

	ret = fpga_pci_check_file_id(sysfs_name, map->vendor_id);
	fail_on(ret != 0, err, 
			"fpga_pci_check_file_id failed, sysfs_name=%s, vendor_id=0x%04x",
			sysfs_name, map->vendor_id);

	/** Sanity check the device */
	ret = snprintf(sysfs_name, sizeof(sysfs_name), 
			"/sys/bus/pci/devices/" PCI_DEV_FMT "/device", 
			map->domain, map->bus, map->dev, map->func);

	fail_on(ret < 0, err, "Error building the sysfs path for device");
	fail_on((size_t) ret >= sizeof(sysfs_name), err, 
			"sysfs path too long for device");

	ret = fpga_pci_check_file_id(sysfs_name, map->device_id);
	fail_on(ret != 0, err, 
			"fpga_pci_check_file_id failed, sysfs_name=%s, device_id=0x%04x",
			sysfs_name, map->device_id);

	char wc_suffix[3] = "\0";
	if (map->resource_burstable[bar_id] && write_combining) {
		strncpy(wc_suffix, "_wc", sizeof(wc_suffix));
	}
	
	/** 
	 * Open and memory map the resource.
	 *  -"_wc" is added if the memory bar is burstable.
	 */
	snprintf(sysfs_name, sizeof(sysfs_name), 
			"/sys/bus/pci/devices/" PCI_DEV_FMT "/resource%u%s", 
			map->domain, map->bus, map->dev, map->func, bar_id, wc_suffix);

	fail_on(ret < 0, err, "Error building the sysfs path for resource");
	fail_on((size_t) ret >= sizeof(sysfs_name), err, "sysfs path too long for resource");

	log_debug("Opening sysfs_name=%s", sysfs_name);

	fd = open(sysfs_name, O_RDWR | O_SYNC);
	fail_on(fd == -1, err, "open failed");

	mem_base = mmap(0, map->resource_size[bar_id], PROT_READ | PROT_WRITE, 
			MAP_SHARED, fd, 0);
	fail_on(mem_base == MAP_FAILED, err, "mmap failed");
	close(fd);
	fd = -1;

	/** Allocate a bar */
	int tmp_handle = fpga_pci_bar_alloc();
	fail_on(tmp_handle < 0, err_unmap, "fpga_pci_bar_alloc failed");

	/** Set the bar's mem base and size */
	ret = fpga_pci_bar_set_mem_base_size(tmp_handle, mem_base, 
			map->resource_size[bar_id]);
	fail_on(ret != 0, err_unmap, "fpga_pci_set_mem_base_size failed");

	/** Setup handle for return */
	*handle = tmp_handle;

	return 0;
err_unmap:
	if (mem_base) {
		ret = munmap(mem_base, map->resource_size[bar_id]);
		fail_on(ret != 0, err, "munmap failed");
	}
err:
	if (fd != -1) {
		close(fd);
	}
	errno = 0;
	return FPGA_ERR_FAIL;
}

int
fpga_pci_init() {
	log_info("FPGA_PCI_BARS_MAX=%u", FPGA_PCI_BARS_MAX);
	return 0;
}

int
fpga_pci_attach(int slot_id, int pf_id, int bar_id, uint32_t flags,
	pci_bar_handle_t *handle) 
{
	bool write_combining;
	struct fpga_slot_spec spec;
	
	(void) flags;

	int ret = -EINVAL;
	fail_on(!handle, err, "handle is NULL");
	fail_on(pf_id < 0 || pf_id >= FPGA_PF_MAX, err, "Invalid pf_id=%d", pf_id);
	fail_on(bar_id < 0 || bar_id >= FPGA_BAR_PER_PF_MAX, err, 
			"Invalid bar_id=%d", bar_id);

	memset(&spec, 0, sizeof(struct fpga_slot_spec));

	ret = fpga_pci_get_slot_spec(slot_id, &spec);
	fail_on(ret, err, "Unable to prefill the slot spec\n");

	write_combining = false;
	if (flags & BURST_CAPABLE) {
		ret = (spec.map[pf_id].resource_burstable[bar_id]) ? 0 : FPGA_ERR_FAIL;
		fail_on(ret, err, "bar is not BURST_CAPABLE (does not support write "
			"combining.)");
		write_combining = true;
	}

	return fpga_pci_bar_attach(&spec, pf_id, bar_id, write_combining, handle);
err:
	return ret;
}

int
fpga_pci_detach(pci_bar_handle_t handle) {
	log_debug("handle=%d", handle);

	struct fpga_pci_bar *bar = fpga_pci_bar_get(handle);
	fail_on(!bar, err, "fpga_pci_bar_get failed");

	int ret = munmap(bar->mem_base, bar->mem_size);
	fail_on(ret != 0, err, "munmap failed");

	ret = fpga_pci_bar_free(handle);
	fail_on(ret != 0, err, "fpga_pci_bar_free failed");
	return 0;
err:
	errno = 0;
	return FPGA_ERR_FAIL;
}

int
fpga_pci_poke(pci_bar_handle_t handle, uint64_t offset, uint32_t value) {
	log_debug("handle=%d, offset=0x%" PRIx64 ", value=0x%08x", 
			handle, offset, value);

	uint32_t *reg_ptr = (uint32_t *)fpga_pci_bar_get_mem_at_offset(handle, 
			offset, sizeof(uint32_t));
	fail_on(!reg_ptr, err, "fpga_pci_bar_get_mem_at_offset failed");

	*reg_ptr = value;

	return 0;
err:
	return FPGA_ERR_FAIL; 
}

int
fpga_pci_poke64(pci_bar_handle_t handle, uint64_t offset, uint64_t value) {
	log_debug("handle=%d, offset=0x%" PRIx64 ", value=0x%" PRIx64, 
			handle, offset, value);

	uint64_t *reg_ptr = (uint64_t *)fpga_pci_bar_get_mem_at_offset(handle,
			offset, sizeof(uint64_t));
	fail_on(!reg_ptr, err, "fpga_plat_get_mem_at_offset failed");

	*reg_ptr = value;

	return 0;
err:
	return FPGA_ERR_FAIL;
}

int
fpga_pci_peek(pci_bar_handle_t handle, uint64_t offset, uint32_t *value) {
	fail_on(!value, err, "value is NULL");

	uint32_t *reg_ptr = (uint32_t *)fpga_pci_bar_get_mem_at_offset(handle, 
			offset, sizeof(uint32_t));
	fail_on(!reg_ptr, err, "fpga_plat_get_mem_at_offset failed");

	*value = *reg_ptr;

	log_debug("handle=%d, offset=0x%" PRIx64 ", value=0x%08x", 
			handle, offset, *value);
	return 0;
err:
	return FPGA_ERR_FAIL;
}

int
fpga_pci_peek64(pci_bar_handle_t handle, uint64_t offset, uint64_t *value) {
	fail_on(!value, err, "value is NULL");

	uint64_t *reg_ptr = (uint64_t *)fpga_pci_bar_get_mem_at_offset(handle,
			offset, sizeof(uint64_t));
	fail_on(!reg_ptr, err, "fpga_plat_get_mem_at_offset failed");

	*value = *reg_ptr;

	log_debug("handle=%d, offset=0x%" PRIx64 ", value=0x%" PRIx64, 
			handle, offset, *value);
	return 0;
err:
	return FPGA_ERR_FAIL;
}

int fpga_pci_write_burst(pci_bar_handle_t handle, uint64_t offset, uint32_t* datap, uint64_t dword_len) {
	uint64_t i;
	log_debug("handle=%d, offset=0x%" PRIx64, handle, offset);

	/** get the pointer to the beginning of the range */
	uint32_t *reg_ptr = (uint32_t *)fpga_pci_bar_get_mem_at_offset(handle,
			offset, sizeof(uint32_t)*dword_len);
	fail_on(!reg_ptr, err, "fpga_plat_get_mem_at_offset failed");

	/** memcpy */
	for (i = 0; i < dword_len; ++i) {
		reg_ptr[i] = datap[i];
	}

	return 0;
err:
	return FPGA_ERR_FAIL;
}

int
fpga_pci_get_address(pci_bar_handle_t handle, uint64_t offset, size_t len,
	void **ptr)
{
	fail_on(!ptr, err, "ptr is NULL");

	*ptr = fpga_pci_bar_get_mem_at_offset(handle, offset, len);
	fail_on(!*ptr, err, "fpga_plat_get_mem_at_offset failed");
	return 0;
err:
	return FPGA_ERR_FAIL;
}

int
fpga_pci_memset(pci_bar_handle_t handle, uint64_t offset, uint32_t value,
	uint64_t dword_len)
{
	uint64_t i;
	log_debug("handle=%d, offset=0x%" PRIx64, handle, offset);

	/** get the pointer to the beginning of the range */
	uint32_t *reg_ptr = (uint32_t *)fpga_pci_bar_get_mem_at_offset(handle,
			offset, sizeof(uint32_t)*dword_len);
	fail_on(!reg_ptr, err, "fpga_plat_get_mem_at_offset failed");

	/** memset */
	for (i = 0; i < dword_len; ++i) {
		reg_ptr[i] = value;
	}

	return 0;
err:
	return FPGA_ERR_FAIL;
}
