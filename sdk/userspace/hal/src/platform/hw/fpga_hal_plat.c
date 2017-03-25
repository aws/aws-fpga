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
#include <string.h>
#include <fcntl.h>
#include <pthread.h>
#include <errno.h>

#include <fpga_hal_plat.h>
#include <limits.h>
#include <lcd.h>

/**
 * platform fpga devs:
 *  -one dev structure per FPGA
 */
static pthread_mutex_t devs_mutex = PTHREAD_MUTEX_INITIALIZER;

static struct fpga_plat_dev {
	bool	 allocated;
	void	*mem_base;
	size_t	 mem_size;
} devs[FPGA_PLAT_DEVS_MAX];

int fpga_plat_init(void)
{
	log_info("FPGA_PLAT_DEVS_MAX=%u", FPGA_PLAT_DEVS_MAX);
	return 0;
}

static inline struct fpga_plat_dev *
fpga_plat_dev_get(int dev_index)
{
	log_debug("dev_index=%d", dev_index);

	fail_on(dev_index >= FPGA_PLAT_DEVS_MAX, err, "Invalid dev_index=%d", 
			dev_index);

	return &devs[dev_index];
err:
	return NULL;
}

static int 
fpga_plat_dev_set_mem_base_size(int dev_index, void *mem_base, size_t mem_size)
{
	log_debug("dev_index=%d", dev_index);

	struct fpga_plat_dev *dev = fpga_plat_dev_get(dev_index);
	fail_on(!dev, err, "fpga_plat_dev_get failed");
	fail_on(!mem_base, err, "mem_base is NULL");
	fail_on(!mem_size, err, "mem_size is 0");

	dev->mem_base = mem_base;
	dev->mem_size = mem_size;

	return 0;
err:
	return -1;
}

void * 
fpga_plat_dev_get_mem_base(int dev_index)
{
	log_debug("dev_index=%d", dev_index);

	struct fpga_plat_dev *dev = fpga_plat_dev_get(dev_index);
	fail_on(!dev, err, "fpga_plat_dev_get failed");

	return dev->mem_base;
err:
	return NULL;
}

/*
 * static inline int
fpga_plat_dev_check_mem_offset(int dev_index, uint64_t offset)
{
	log_debug("dev_index=%d", dev_index);

	struct fpga_plat_dev *dev = fpga_plat_dev_get(dev_index);
	fail_on(!dev, err, "fpga_plat_dev_get failed");

	fail_on(!dev->allocated, err, "Not attached");
	fail_on(!dev->mem_base, err, "mem_base is NULL");
	fail_on(offset >= dev->mem_size, err, 
			"Invalid offset=0x%" PRIx64, offset);
	return 0;
err:
	return -1;
}
*/

static inline void * 
fpga_plat_dev_get_mem_at_offset(int dev_index, uint64_t offset, uint32_t xaction_size)
{
	log_debug("dev_index=%d", dev_index);

	struct fpga_plat_dev *dev = fpga_plat_dev_get(dev_index);
	fail_on(!dev, err, "fpga_plat_dev_get failed");
        fail_on(!dev->allocated, err, "Not attached");
        fail_on(!dev->mem_base, err, "mem_base is NULL");
        fail_on(offset >= dev->mem_size, err,
                        "Invalid offset=0x%" PRIx64, offset);
        fail_on(((uint64_t)(offset + xaction_size)) > dev->mem_size, err,
                        "Invalid offset +  size =0x%" PRIx64 " exceeds range" , (uint64_t)(offset+xaction_size));
	return dev->mem_base + offset;
err:
	return NULL;
}

static int
fpga_plat_dev_alloc(void)
{
	log_debug("enter");

	pthread_mutex_lock(&devs_mutex);

	int i;
	for (i = 0; i < FPGA_PLAT_DEVS_MAX; i++) {
		struct fpga_plat_dev *dev = &devs[i];

		if (dev->allocated == false) {
			log_debug("allocated dev_index=%d", i);
			dev->allocated = true;

			pthread_mutex_unlock(&devs_mutex);

			return i;
		}
	}

	pthread_mutex_unlock(&devs_mutex);

	return -1;
}

static int
fpga_plat_dev_free(int dev_index)
{
	log_debug("dev_index=%d", dev_index);

	struct fpga_plat_dev *dev = fpga_plat_dev_get(dev_index);
	fail_on(!dev, err, "fpga_plat_dev_get failed");

	pthread_mutex_lock(&devs_mutex);

	memset(dev, 0, sizeof(*dev));

	pthread_mutex_unlock(&devs_mutex);

	return 0;
err:
	return -1;
}

static int
fpga_plat_check_file_id(char *path, uint16_t id)
{
	log_debug("enter");
	fail_on(!path, err, "path is NULL");

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

/************************************************************************ 
 * Multi-device attachment and use, via the dev_index.
 ************************************************************************/ 

int 
fpga_plat_dev_attach(struct fpga_slot_spec *spec, int pf_id, int bar_id,
	bool write_combining, int *dev_index)
{
	log_debug("enter");

	void *mem_base = NULL;

	fail_on(!spec, err, "spec is NULL");
	fail_on(!dev_index, err, "dev_index is NULL");

	struct fpga_pci_resource_map *map = &spec->map[pf_id];

	log_info("vendor_id=0x%04x, device_id=0x%04x, DBDF:" 
			PCI_DEV_FMT ", resource_num=%u, size=%" PRIu64 ", burstable=%u",
			map->vendor_id, map->device_id, map->domain, map->bus, 
			map->dev, map->func, bar_id, map->resource_size[bar_id],
			map->resource_burstable[bar_id]);

	/** Invalid dev_index for error returns */
	*dev_index = -1;

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

	char wc_suffix[3] = "\0";
	if (map->resource_burstable[bar_id] && write_combining) {
		strncpy(wc_suffix, "_wc", sizeof(wc_suffix));
	}
	
	/** Open and memory map the resource */
	/* adding _wc if the memory bar is burstable */
	snprintf(sysfs_name, sizeof(sysfs_name), 
			"/sys/bus/pci/devices/" PCI_DEV_FMT "/resource%u%s", 
			map->domain, map->bus, map->dev, map->func, bar_id, wc_suffix);

	fail_on(ret < 0, err, "Error building the sysfs path for resource");
	fail_on((size_t) ret >= sizeof(sysfs_name), err, "sysfs path too long for resource");

	log_debug("Opening sysfs_name=%s", sysfs_name);

	int fd = open(sysfs_name, O_RDWR | O_SYNC);
	fail_on(fd == -1, err, "open failed");

	mem_base = mmap(0, map->resource_size[bar_id], PROT_READ | PROT_WRITE,
		MAP_SHARED, fd, 0);
	fail_on(mem_base == MAP_FAILED, err, "mmap failed");

	/** Allocate a dev */
	int tmp_dev_index = fpga_plat_dev_alloc();
	fail_on(tmp_dev_index < 0, err_unmap, "fpga_plat_dev_alloc failed");

	/** Set the dev's mem base and size */
	ret = fpga_plat_dev_set_mem_base_size(tmp_dev_index, mem_base,
		map->resource_size[bar_id]);
	fail_on(ret != 0, err_unmap, "fpga_plat_set_mem_base_size failed");

	/** Setup dev_index for return */
	*dev_index = tmp_dev_index;

	return 0;
err_unmap:
	if (mem_base) {
		ret = munmap(mem_base, map->resource_size[bar_id]);
		fail_on(ret != 0, err, "munmap failed");
	}
err:
	errno = 0;
	return -1;
}

int 
fpga_plat_dev_detach(int dev_index)
{
	log_debug("dev_index=%d", dev_index);

	struct fpga_plat_dev *dev = fpga_plat_dev_get(dev_index);
	fail_on(!dev, err, "fpga_plat_dev_get failed");

	int ret = munmap(dev->mem_base, dev->mem_size);
	fail_on(ret != 0, err, "munmap failed");

	ret = fpga_plat_dev_free(dev_index);
	fail_on(ret != 0, err, "fpga_plat_dev_free failed");
	return 0;
err:
	errno = 0;
	return -1;
}

int 
fpga_plat_dev_reg_read(int dev_index, uint64_t offset, uint32_t *value)
{
	log_debug("dev_index=%d", dev_index);
	fail_on(!value, err, "value is NULL");

/*
	int ret = fpga_plat_dev_check_mem_offset(dev_index, offset);
	fail_on(ret != 0, err, "Invalid offset 0x%" PRIx64 ", or not attached", offset);
*/
	uint32_t *reg_ptr = (uint32_t *)fpga_plat_dev_get_mem_at_offset(dev_index, 
			offset, sizeof(uint32_t));
	fail_on(!reg_ptr, err, "fpga_plat_get_mem_at_offset failed");

	*value = *reg_ptr;

	log_debug("offset=0x%" PRIx64 ", value=0x%08x", offset, *value);
	return 0;
err:
	return -1;
}

int 
fpga_plat_dev_reg_write(int dev_index, uint64_t offset, uint32_t value)
{
	log_debug("dev_index=%d", dev_index);
/*
	int ret = fpga_plat_dev_check_mem_offset(dev_index, offset);
	fail_on(ret != 0, err, "Invalid offset=0x%" PRIx64 ", or not attached", 
			offset);
*/
	log_debug("offset=0x%" PRIx64 ", value=0x%08x", offset, value);
	uint32_t *reg_ptr = (uint32_t *)fpga_plat_dev_get_mem_at_offset(dev_index, 
			offset, sizeof(uint32_t));
	fail_on(!reg_ptr, err, "fpga_plat_get_mem_at_offset failed");

	*reg_ptr = value;

	return 0;
err:
	return -1;
}

int
fpga_plat_dev_reg_read64(int dev_index, uint64_t offset, uint64_t *value)
{
	log_debug("dev_index=%d", dev_index);
	fail_on(!value, err, "value is NULL");
/*
	int ret = fpga_plat_dev_check_mem_offset(dev_index, offset);
	fail_on(ret != 0, err, "Invalid offset 0x%" PRIx64 ", or not attached", offset);
*/
	uint64_t *reg_ptr = (uint64_t *)fpga_plat_dev_get_mem_at_offset(dev_index,
			offset, sizeof(uint64_t));
	fail_on(!reg_ptr, err, "fpga_plat_get_mem_at_offset failed");

	*value = *reg_ptr;

	log_debug("offset=0x%" PRIx64 ", value=0x%" PRIx64, offset, *value);
	return 0;
err:
	return -1;
}

int
fpga_plat_dev_reg_write64(int dev_index, uint64_t offset, uint64_t value)
{
	log_debug("dev_index=%d", dev_index);
/*
	int ret = fpga_plat_dev_check_mem_offset(dev_index, offset);
	fail_on(ret != 0, err, "Invalid offset=0x%" PRIx64 ", or not attached",
			offset);
*/
	log_debug("offset=0x%" PRIx64 ", value=0x%" PRIx64, offset, value);
	uint64_t *reg_ptr = (uint64_t *)fpga_plat_dev_get_mem_at_offset(dev_index,
			offset, sizeof(uint64_t));
	fail_on(!reg_ptr, err, "fpga_plat_get_mem_at_offset failed");

	*reg_ptr = value;

	return 0;
err:
	return -1;
}

int
fpga_plat_dev_reg_write_burst(int dev_index, uint64_t offset, uint32_t* datap,
	uint32_t dword_len)
{
	uint32_t i;
	log_debug("dev_index=%d", dev_index);

	/* validate the beginning of the data range 
	ret = fpga_plat_dev_check_mem_offset(dev_index, offset);
	fail_on(ret != 0, err, "Invalid offset=0x%" PRIx64 ", or not attached",
			offset);

	ret = fpga_plat_dev_check_mem_offset(dev_index,
		offset + dword_len * dword_mult - 1);
	fail_on(ret != 0, err, "Invalid offset=0x%" PRIx64 " (out of range)",
			offset);
	*/

	/* get the pointer to the beginning of the range */
	log_debug("offset=0x%" PRIx64, offset);
	uint32_t *reg_ptr = (uint32_t *)fpga_plat_dev_get_mem_at_offset(dev_index,
			offset,sizeof(uint32_t)*dword_len);
	fail_on(!reg_ptr, err, "fpga_plat_get_mem_at_offset failed");

	/* memcpy */
	for (i = 0; i < dword_len; ++i) {
		reg_ptr[i] = datap[i];
	}

	return 0;
err:
	return -1;
}

/************************************************************************ 
 * Single device attachment and use.
 * e.g. for applications that only attach to one FPGA at a time,
 * or for applications that separate FPGA access into separate worker
 * processes (e.g. for isolation).
 ************************************************************************/

int 
fpga_plat_attach(struct fpga_slot_spec *spec, int pf_id, int bar_id)
{
	log_debug("enter");

	int dev_index = -1;
	int ret = fpga_plat_dev_attach(spec, pf_id, bar_id, false, &dev_index);
	fail_on(ret != 0, err, "fpga_plat_dev_attach failed");

	if (dev_index != 0) {
		ret = fpga_plat_dev_detach(dev_index);
		fail_on(ret != 0, err, "fpga_plat_dev_detach failed");
		fail_on(true, err, "use fpga_plat_dev_attach for multi-device attachment");
	} 

	return 0;
err:
	return -1;
}

int 
fpga_plat_detach(void)
{
	log_debug("enter");
	return fpga_plat_dev_detach(0);
}

int 
fpga_plat_reg_read(uint64_t offset, uint32_t *value)
{
	log_debug("enter");
	return fpga_plat_dev_reg_read(0, offset, value);
}

int 
fpga_plat_reg_write(uint64_t offset, uint32_t value)
{
	log_debug("enter");
	return fpga_plat_dev_reg_write(0, offset, value);
}
