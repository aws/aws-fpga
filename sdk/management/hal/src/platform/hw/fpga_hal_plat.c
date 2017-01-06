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
 * FPGA HAL platform operations.
 */

#include <stdio.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <sys/mman.h>
#include <fcntl.h>
#include <errno.h>

#include <fpga_hal_plat.h>
#include <limits.h>
#include <lcd.h>


static void *fpga_plat_mem_base;
static size_t fpga_plat_mem_size;

int fpga_plat_init(void)
{
	log_debug("enter");
	return 0;
}

static void
fpga_plat_set_mem_base_size(void *v, size_t size)
{
	fpga_plat_mem_base = v;
	fpga_plat_mem_size = size;
}

static void * 
fpga_plat_get_mem_base(void)
{
	return fpga_plat_mem_base;
}

static int
fpga_plat_check_mem_offset(uint32_t offset)
{
	fail_on(fpga_plat_get_mem_base() == 0, err, "Not attached");
	fail_on(offset >= fpga_plat_mem_size, err, "Invalid offset 0x%08x", offset);
	return 0;
err:
	return -1;
}

static void * 
fpga_plat_get_mem_at_offset(uint32_t offset)
{
	return fpga_plat_mem_base + offset;
}

static int
fpga_plat_check_file_id(char *path, uint16_t id)
{
	log_debug("enter");

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
	return -1;
}

int 
fpga_plat_attach(struct fpga_slot_spec *spec)
{
	log_debug("enter");
	struct fpga_pci_resource_map *map = &spec->map;

	log_info("vendor_id=0x%04x, device_id=0x%04x, DBDF:" 
			PCI_DEV_FMT ", resource_num=%u, size=%u", 
			map->vendor_id, map->device_id, map->domain, map->bus, 
			map->dev, map->func, map->resource_num, map->size);

	/** Sanity check the vendor */
	char sysfs_name[NAME_MAX + 1];
	int ret = snprintf(sysfs_name, sizeof(sysfs_name), 
			"/sys/bus/pci/devices/" PCI_DEV_FMT "/vendor", 
			map->domain, map->bus, map->dev, map->func);

	fail_on(ret < 0, err, "Error building the sysfs path for vendor");
	fail_on((size_t) ret >= sizeof(sysfs_name), err, "sysfs path too long for vendor");

	ret = fpga_plat_check_file_id(sysfs_name, map->vendor_id);
	fail_on(ret != 0, err, 
			"fpga_plat_check_file_id failed, sysfs_name=%s, vendor_id=0x%04x",
			sysfs_name, map->vendor_id);

	/** Sanity check the device */
	ret = snprintf(sysfs_name, sizeof(sysfs_name), 
			"/sys/bus/pci/devices/" PCI_DEV_FMT "/device", 
			map->domain, map->bus, map->dev, map->func);

	fail_on(ret < 0, err, "Error building the sysfs path for device");
	fail_on((size_t) ret >= sizeof(sysfs_name), err, 
			"sysfs path too long for device");

	ret = fpga_plat_check_file_id(sysfs_name, map->device_id);
	fail_on(ret != 0, err, 
			"fpga_plat_check_file_id failed, sysfs_name=%s, device_id=0x%04x",
			sysfs_name, map->device_id);

	/** Open and memory map the resource */
	snprintf(sysfs_name, sizeof(sysfs_name), 
			"/sys/bus/pci/devices/" PCI_DEV_FMT "/resource%u", 
			map->domain, map->bus, map->dev, map->func, map->resource_num);

	fail_on(ret < 0, err, "Error building the sysfs path for resource");
	fail_on((size_t) ret >= sizeof(sysfs_name), err, "sysfs path too long for resource");

	log_debug("Opening sysfs_name=%s", sysfs_name);

	int fd = open(sysfs_name, O_RDWR | O_SYNC);
	fail_on(fd == -1, err, "open failed");

	void *v = mmap(0, map->size, PROT_READ | PROT_WRITE, MAP_SHARED, fd, 0);
	fail_on(v == MAP_FAILED, err, "mmap failed");

	fpga_plat_set_mem_base_size(v, map->size);

	return 0;
err:
	errno = 0;
	return -1;
}

int 
fpga_plat_detach(void)
{
	log_debug("enter");
	int ret = munmap(fpga_plat_mem_base, fpga_plat_mem_size);
	fail_on(ret != 0, err, "munmap failed");
	fpga_plat_set_mem_base_size(0, 0);
	return 0;
err:
	errno = 0;
	return -1;
}

int 
fpga_plat_reg_read(uint32_t offset, uint32_t *value)
{
	int ret = fpga_plat_check_mem_offset(offset);
	fail_on(ret != 0, err, "Invalid offset 0x%08x, or not attached", offset);

	uint32_t *reg_ptr = (uint32_t *)fpga_plat_get_mem_at_offset(offset);
	*value = *reg_ptr;

	log_debug("offset=0x%08x, value=0x%08x", offset, *value);
	return 0;
err:
	return -1;
}

int 
fpga_plat_reg_write(uint32_t offset, uint32_t value)
{
	int ret = fpga_plat_check_mem_offset(offset);
	fail_on(ret != 0, err, "Invalid offset 0x%08x, or not attached", offset);

	log_debug("offset=0x%08x, value=0x%08x", offset, value);
	uint32_t *reg_ptr = (uint32_t *)fpga_plat_get_mem_at_offset(offset);
	*reg_ptr = value;
	return 0;
err:
	return -1;
}
