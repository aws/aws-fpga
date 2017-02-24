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

#include <assert.h>
#include <limits.h>
#include <fcntl.h>
#include <unistd.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <stdlib.h>
#include <string.h>
#include <sys/errno.h>
#include <stdio.h>
#include <getopt.h>
#include <dirent.h>

/**
 * Return the ID from the given sysfs file (e.g. Vendor ID, Device ID).
 *
 * @param[in]		path	the sysfs file path 
 * @param[in,out]   id		the returned id
 *
 * @returns
 *  0	on success 
 * -1	on failure
 */
static int
fpga_pci_get_id(char *path, uint16_t *id)
{
	fail_on_internal(!path, err, CLI_INTERNAL_ERR_STR);
	fail_on_internal(!id, err, CLI_INTERNAL_ERR_STR);

	int ret = 0;
	FILE *fp = fopen(path, "r");
	fail_on_quiet(!fp, err, "Error opening %s", path);

	uint32_t tmp_id;
	ret = fscanf(fp, "%x", &tmp_id);
	fail_on_quiet(ret < 0, err_close, "Error parsing %s", path);

	*id = tmp_id;

	fclose(fp);
	return 0;

err_close:
	fclose(fp);
err:
	errno = 0;
	return -1;
}

/**
 * Fill in the DBDF within the PCI resource map using the given PCI device 
 * directory name.
 *
 * @param[in]		dir_name	the PCI device directory name 
 * @param[in,out]   map			the PCI resource map to fill in 
 *
 * @returns
 *  0	on success 
 * -1	on failure
 */
static int
fpga_pci_get_dbdf(char *dir_name, struct fpga_pci_resource_map *map)
{
	fail_on_internal(!dir_name, err, CLI_INTERNAL_ERR_STR);
	fail_on_internal(!map, err, CLI_INTERNAL_ERR_STR);

	uint32_t domain;
	uint32_t bus;
	uint32_t dev;
	int func;
	int ret = sscanf(dir_name, PCI_DEV_FMT, &domain, &bus, &dev, &func);
	fail_on_internal(ret != 4, err, CLI_INTERNAL_ERR_STR); 

	map->domain = domain;
	map->bus = bus;
	map->dev = dev;
	map->func = func;
	return 0;
err:
	return -1;
}

/**
 * Return the PCI resource size using the PCI directory name and resource 
 * number.
 *
 * @param[in]		dir_name		the PCI device directory name 
 * @param[in]		resource_num	the resource number 
 * @param[in,out]   resource_size	the returned resource size
 *
 * @returns
 *  0	on success 
 * -1	on failure
 */
static int
fpga_pci_get_pci_resource_size(char *dir_name,
		uint32_t resource_num, size_t *resource_size)
{
	fail_on_internal(!dir_name, err, CLI_INTERNAL_ERR_STR);
	fail_on_internal(!resource_size, err, CLI_INTERNAL_ERR_STR);

	char sysfs_name[NAME_MAX + 1];
	int ret = snprintf(sysfs_name, sizeof(sysfs_name), 
			"/sys/bus/pci/devices/%s/resource%u", dir_name, 
			resource_num);

	fail_on_quiet(ret < 0, err, "Error building the sysfs path for resource%u",
			resource_num);
	fail_on_quiet((size_t) ret >= sizeof(sysfs_name), err, 
			"sysfs path too long for resource%u", resource_num);

	/** Check for file existence, obtain the file size */
	struct stat file_stat;
	ret = stat(sysfs_name, &file_stat);
	fail_on_quiet(ret != 0, err, "stat failed, path=%s", sysfs_name);

	*resource_size = file_stat.st_size;

	return 0;
err:
	return -1;
}


/**
 * Handle one PCI device directory with the given directory name, and see if 
 * it is an AFI mbox slot.  If so, initialize a slot device structure for it 
 * and its associated slot device (if any).
 *
 * @param[in]		dir_name	the PCI device directory name 
 *
 * @returns
 *  0	on success 
 * -1	on failure
 */
static int
fpga_pci_handle_pci_dir_name(char *dir_name, struct fpga_slot_spec *spec)
{
	uint16_t vendor_id = 0;
	uint16_t device_id = 0;

	fail_on_quiet(!dir_name, err, CLI_INTERNAL_ERR_STR);
	// fail_on_quiet(f1.slot_dev_index >= FPGA_SLOT_MAX, err, 
	// 		CLI_INTERNAL_ERR_STR);

	/** Setup and read the PCI Vendor ID */
	char sysfs_name[NAME_MAX + 1];
	int ret = snprintf(sysfs_name, sizeof(sysfs_name), 
			"/sys/bus/pci/devices/%s/vendor", dir_name);

	fail_on_quiet(ret < 0, err, "Error building the sysfs path for vendor");
	fail_on_quiet((size_t) ret >= sizeof(sysfs_name), err, "sysfs path too long for vendor");

	ret = fpga_pci_get_id(sysfs_name, &vendor_id);
	fail_on_quiet(ret != 0, err, "Error retrieving vendor_id");

	/** Setup and read the PCI Device ID */
	ret = snprintf(sysfs_name, sizeof(sysfs_name), 
			"/sys/bus/pci/devices/%s/device", dir_name);

	fail_on_quiet(ret < 0, err, "Error building the sysfs path for device");
	fail_on_quiet((size_t) ret >= sizeof(sysfs_name), err, "sysfs path too long for device");

	ret = fpga_pci_get_id(sysfs_name, &device_id);
	fail_on_quiet(ret != 0, err, "Error retrieving device_id");

	/** Check for a match to the FPGA Mbox Vendor ID and Device ID */
	if ((vendor_id == F1_MBOX_VENDOR_ID) &&
		(device_id == F1_MBOX_DEVICE_ID)) {
		//log_debug("AFI mgmt channel found, using slot_dev_index=%u\n", 
		//		f1.slot_dev_index); // <<<<

		/** Fill in the FPGA mbox slot dev, using slot_dev_index */
		struct fpga_pci_resource_map *map = &spec->map;

		/** Fill in the DBDF */
		ret = fpga_pci_get_dbdf(dir_name, map);
		fail_on_quiet(ret != 0, err, "Error retrieving DBDF from dir_name=%s",
				dir_name);

		/** Retrieve the PCI resource size for plat attach */
		size_t resource_size = 0;
		ret = fpga_pci_get_pci_resource_size(dir_name, F1_MBOX_RESOURCE_NUM, 
				&resource_size);
		fail_on_quiet(ret != 0, err, "Error retrieving resource size");

		map->vendor_id = vendor_id;
		map->device_id = device_id;
		map->resource_num = F1_MBOX_RESOURCE_NUM;
		map->size = resource_size;

		return 0;
	} else {
		/* the device did not match */
		return 1;
	}

err:
	return -1;
}

int
fpga_pci_get_slot_spec(int slot_id, int pf_id, int bar_id, struct fpga_slot_spec *spec)
{
	bool found_afi_slot = false;
	char *path = "/sys/bus/pci/devices";
	DIR *dirp = opendir(path);
	fail_on_internal(!dirp, err, CLI_INTERNAL_ERR_STR);
	int slot_dev_index = 0;
	int search_max = min(FPGA_SLOT_MAX, slot_id);
	struct fpga_slot_spec search_spec;

	/** Loop through the sysfs device directories */
	for (;;) {
		struct dirent entry; 
		struct dirent *result;
		memset(&entry, 0, sizeof(entry));

		readdir_r(dirp, &entry, &result);
		if (result == NULL) {
			/** No more directories */
			break;
		}

		/** Handle the current directory entry */
		memset(&search_spec, 0, sizeof(struct fpga_slot_spec));
		int ret = fpga_pci_handle_pci_dir_name(entry.d_name, &search_spec);
		if (ret == 0) {
			found_afi_slot = true;
			slot_dev_index++;

			if (slot_dev_index >= search_max) {
				break;
			}
		}
	}

	closedir(dirp);

	/** 
	 * Return errors back to the user:
	 *  -no AFI slots found.
	 *  -invalid AFI slot specified.
	 */
	fail_on_user(!found_afi_slot, err, "No fpga-image-slots found");

	*spec = search_spec;
	spec->map.resource_num = bar_id;
	spec->map.func = pf_id;
	return 0;

err:
	return -1;
}
