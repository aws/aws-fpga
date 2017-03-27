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

#include "fpga_pci_internal.h"

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
	fail_on(!path, err, CLI_INTERNAL_ERR_STR);
	fail_on(!id, err, CLI_INTERNAL_ERR_STR);

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
	return FPGA_ERR_FAIL;
}

/**
 * Write a '1' to the given sysfs file.
 *
 * @param[in]		path	the sysfs file path
 *
 * @returns
 *  0	on success
 * -1	on failure
 */
static int
fpga_pci_write_one2file(char *path)
{
	int ret = -1;

	int fd = open(path, O_WRONLY);
	fail_on_quiet(fd == -1, err, "opening %s", path);

	char buf[] = { '1', 0 };
	ret = -!!write_loop(fd, buf, sizeof(buf));
	fail_on_quiet(ret != 0, err_close, "error writing %s", path);

err_close:
	close(fd);
err:
	return ret;
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
	fail_on(!dir_name, err, CLI_INTERNAL_ERR_STR);
	fail_on(!map, err, CLI_INTERNAL_ERR_STR);

	uint32_t domain;
	uint32_t bus;
	uint32_t dev;
	int func;
	int ret = sscanf(dir_name, PCI_DEV_FMT, &domain, &bus, &dev, &func);
	fail_on(ret != 4, err, CLI_INTERNAL_ERR_STR);

	map->domain = domain;
	map->bus = bus;
	map->dev = dev;
	map->func = func;
	return 0;
err:
	return FPGA_ERR_FAIL;
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
fpga_pci_get_pci_resource_info(char *dir_name,
		uint8_t resource_num, uint64_t *resource_size, bool *burstable)
{
	int ret;

	fail_on(!dir_name, err, CLI_INTERNAL_ERR_STR);
	fail_on(!resource_size, err, CLI_INTERNAL_ERR_STR);

	char sysfs_name[NAME_MAX + 1];
	ret = snprintf(sysfs_name, sizeof(sysfs_name),
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

	ret = snprintf(sysfs_name, sizeof(sysfs_name),
			"/sys/bus/pci/devices/%s/resource%u_wc", dir_name,
			resource_num);

	fail_on_quiet(ret < 0, err, "Error building the sysfs path for resource%u",
			resource_num);
	fail_on_quiet((size_t) ret >= sizeof(sysfs_name), err,
			"sysfs path too long for resource%u", resource_num);

	memset(&file_stat, 0, sizeof(struct stat));
	ret = stat(sysfs_name, &file_stat);
	*burstable = (ret == 0);

	return 0;
err:
	return FPGA_ERR_FAIL;
}

static int
fpga_pci_handle_resources(char *dir_name, struct fpga_pci_resource_map *map)
{
	int ret;
	static const uint8_t resource_nums[4] = {0, 1, 2, 4};

	for (unsigned int i = 0; i < sizeof_array(resource_nums); ++i) {
		bool burstable = false;
		uint64_t resource_size = 0;
		uint8_t resource_num = resource_nums[i];
		if (resource_num > sizeof_array(map->resource_size)) {
			continue;
		}
		ret = fpga_pci_get_pci_resource_info(dir_name, resource_num,
		                                     &resource_size,
		                                     &burstable);
		if (ret) {
			log_debug("Unable to read resource information for %d", resource_num);
		}
		map->resource_size[resource_num] = resource_size;
		map->resource_burstable[resource_num] = burstable;
	}
	return 0;
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
fpga_pci_handle_pci_dir_name(char *dir_name, struct fpga_pci_resource_map *map)
{
	uint16_t vendor_id = 0;
	uint16_t device_id = 0;

	fail_on_quiet(!dir_name, err, CLI_INTERNAL_ERR_STR);

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

	/** Fill in the DBDF */
	ret = fpga_pci_get_dbdf(dir_name, map);
	fail_on_quiet(ret != 0, err, "Error retrieving DBDF from dir_name=%s",
			dir_name);

	map->vendor_id = vendor_id;
	map->device_id = device_id;

	return 0;
err:
	return FPGA_ERR_FAIL;
}

/**
 * Using the mbox_map, fill in the app_map and the app_dir_name.
 *
 * The app device is found via a fixed mapping given the mbox device.
 *
 * @param[in]		mbox_map		the mbox PCI resource map
 * @param[in,out]   app_map			the app PCI resource map to fill in
 * @param[in,out]   app_dir_name	the app PCI resource dir name to fill in
 * @param[in,out]   app_dir_name_size	the size of the app_dir_name buffer
 *
 * @returns
 *  0	on success
 * -1	on failure
 */
static int
fpga_pci_mbox2app(struct fpga_pci_resource_map *mbox_map, 
		struct fpga_pci_resource_map *app_map,
		char *app_dir_name, size_t app_dir_name_size)
{
	uint16_t vendor_id = 0;
	uint16_t device_id = 0;

	fail_on_quiet(!mbox_map || !app_map || !app_dir_name || !app_dir_name_size, 
			err, CLI_INTERNAL_ERR_STR);

	/** Fill in the app map */
	*app_map = *mbox_map;
	app_map->dev = F1_MBOX_DEV2APP_DEV(mbox_map->dev);
	
	/** Construct the app dir name based on the app_map */
	int ret = snprintf(app_dir_name, app_dir_name_size, PCI_DEV_FMT, 
			app_map->domain, app_map->bus, 
			app_map->dev, app_map->func);

	fail_on(ret < 0, err, "Error building the app_dir_name");
	fail_on((size_t) ret >= app_dir_name_size, err, "app_dir_name too long");

	/** Setup and read the PCI Vendor ID */
	char sysfs_name[NAME_MAX + 1];
	ret = snprintf(sysfs_name, sizeof(sysfs_name), 
			"/sys/bus/pci/devices/%s/vendor", app_dir_name);

	fail_on_quiet(ret < 0, err, "Error building the sysfs path for vendor");
	fail_on_quiet((size_t) ret >= sizeof(sysfs_name), err, "sysfs path too long for vendor");

	ret = fpga_pci_get_id(sysfs_name, &vendor_id);
	fail_on_quiet(ret != 0, err, "Error retrieving vendor_id");

	/** Setup and read the PCI Device ID */
	ret = snprintf(sysfs_name, sizeof(sysfs_name), 
			"/sys/bus/pci/devices/%s/device", app_dir_name);

	fail_on_quiet(ret < 0, err, "Error building the sysfs path for device");
	fail_on_quiet((size_t) ret >= sizeof(sysfs_name), err, "sysfs path too long for device");

	ret = fpga_pci_get_id(sysfs_name, &device_id);
	fail_on_quiet(ret != 0, err, "Error retrieving device_id");

	app_map->vendor_id = vendor_id;
	app_map->device_id = device_id;

	return 0;
err:
	return FPGA_ERR_FAIL;
}

int
fpga_pci_get_all_slot_specs(struct fpga_slot_spec spec_array[], int size)
{
	bool found_afi_slot = false;
	char *path = "/sys/bus/pci/devices";
	DIR *dirp = opendir(path);
	fail_on(!dirp, err, CLI_INTERNAL_ERR_STR);

	struct dirent entry, *result;
	int slot_dev_index = 0;
	struct fpga_slot_spec search_spec;
	struct fpga_pci_resource_map search_map, app_map;
	char app_dir_name[NAME_MAX + 1];

	memset(&search_spec, 0, sizeof(struct fpga_slot_spec));

	/** 
	 * Loop through the sysfs device directories
	 * -we first find the mbox dev then handle the app dev as a fixed
	 *  mapping based off of the mbox dev's pci resource map 
	 *  (see fpga_pci_mbox2app).
	 * -this approach is simple and more efficient than the
	 *  alternative of requiring an additional sort of the dirent entries by
	 *  the PCI device number (DBDF).
	 */
	while (true) {
		memset(&entry, 0, sizeof(struct dirent));
		readdir_r(dirp, &entry, &result);
		if (result == NULL) {
			/** No more directories */
			break;
		}

		/** Handle the current directory entry */
		memset(&search_map, 0, sizeof(struct fpga_pci_resource_map));
		int ret = fpga_pci_handle_pci_dir_name(entry.d_name, &search_map);
		if (ret != 0) {
			continue;
		}

		if (search_map.vendor_id == F1_MBOX_VENDOR_ID &&
			search_map.device_id == F1_MBOX_DEVICE_ID) {

			/* Retrieve the PCI resource size for plat attach after confirming
			 * these devices are FPGAs. */
			/* mbox resources */
			ret = fpga_pci_handle_resources(entry.d_name, &search_map);
			fail_on_quiet(ret != 0, err, "Error retrieving resource information");

			/* app resources */
			memset(&app_map, 0, sizeof(struct fpga_pci_resource_map));
			app_dir_name[0] = 0;
			ret = fpga_pci_mbox2app(&search_map, &app_map, 
					app_dir_name, sizeof(app_dir_name));
			fail_on_quiet(ret != 0, err, "Error retrieving app pf information");

			ret = fpga_pci_handle_resources(app_dir_name, &app_map);
			fail_on_quiet(ret != 0, err, "Error retrieving resource information");

			/* copy the results into the spec_array */
			spec_array[slot_dev_index].map[FPGA_APP_PF] = app_map;
			spec_array[slot_dev_index].map[FPGA_MGMT_PF] = search_map;

			found_afi_slot = true;
			slot_dev_index += 1;
			if (slot_dev_index >= size) {
				break;
			}
		}
	}

	fail_on_quiet(!found_afi_slot, err, "No fpga-image-slots found");

	closedir(dirp);

	return 0;
err:
	if (dirp) {
		closedir(dirp);
	}
	return FPGA_ERR_FAIL;
}

int
fpga_pci_get_slot_spec(int slot_id, struct fpga_slot_spec *spec)
{
	unsigned int size;
	struct fpga_slot_spec spec_array[FPGA_SLOT_MAX];

	int ret = -EINVAL;
	fail_on(slot_id < 0 || slot_id >= FPGA_SLOT_MAX, err,
			"Invalid slot_id=%d", slot_id);
	fail_on(!spec, err, "spec is NULL");

	memset(spec_array, 0, sizeof(spec_array));

	/* tell fpga_pci_get_all_slot_specs not to search past the slot number */
	size = min(sizeof_array(spec_array), (unsigned) slot_id + 1);
	ret = fpga_pci_get_all_slot_specs(spec_array, size);
	fail_on_quiet(ret, err, "Unable to read PCI device information.");

	if (spec_array[slot_id].map[FPGA_APP_PF].vendor_id == 0) {
		log_error("No device matching specified id: %d", slot_id);
		return -ENOENT;
	}

	*spec = spec_array[slot_id];
	return 0;
err:
	return FPGA_ERR_FAIL;
}

int
fpga_pci_get_resource_map(int slot_id, int pf_id,
	struct fpga_pci_resource_map *map)
{
	int ret;

	if (slot_id < 0 || slot_id >= FPGA_SLOT_MAX ||
		pf_id < 0 || pf_id >= FPGA_PF_MAX ||
		!map) {
		return -EINVAL;
	}

	struct fpga_slot_spec slot_spec;
	memset(&slot_spec, 0, sizeof(struct fpga_slot_spec));

	ret = fpga_pci_get_slot_spec(slot_id, &slot_spec);
	fail_on_quiet(ret, out, "fpga_pci_get_slot_spec failed");

	*map = slot_spec.map[pf_id];
out:
	return ret;
}

/**
 * Remove the application PF for the given app map.
 *  
 * @param[out]  app_map         the application device resource map to remove 
 *  
 * @returns
 *  0   on success 
 * -1   on failure
 */         
static int
fpga_pci_remove_app_pf(struct fpga_pci_resource_map *app_map)
{   
    fail_on(!app_map, err, CLI_INTERNAL_ERR_STR);
            
    /** Construct the PCI device directory name using the PCI_DEV_FMT */
    char dir_name[NAME_MAX + 1];
    int ret = snprintf(dir_name, sizeof(dir_name), PCI_DEV_FMT,
        app_map->domain, app_map->bus, app_map->dev, app_map->func);
            
    fail_on_quiet(ret < 0, err, "Error building the dir_name");
    fail_on_quiet((size_t) ret >= sizeof(dir_name), err, "dir_name too long");

    /** Setup the path to the device's remove file */
    char sysfs_name[NAME_MAX + 1];
    ret = snprintf(sysfs_name, sizeof(sysfs_name),
            "/sys/bus/pci/devices/%s/remove", dir_name);

    fail_on_quiet(ret < 0, err,
            "Error building the sysfs path for remove file");
    fail_on_quiet((size_t) ret >= sizeof(sysfs_name), err,
            "sysfs path too long for remove file");

    /** Write a "1" to the device's remove file */
    ret = fpga_pci_write_one2file(sysfs_name);
    fail_on_quiet(ret != 0, err, "cli_write_one2file failed");
    
    bool done = false;
    uint32_t retries = 0;
    while (!done) {
        /** Check for file existence, should fail */
        struct stat file_stat;
        ret = stat(sysfs_name, &file_stat);
        if (ret != 0) {
            done = true;
        } else { 
            fail_on_quiet(retries >= F1_REMOVE_APP_PF_MAX_RETRIES, err,
                    "remove failed for path=%s", sysfs_name);
            retries++;
            msleep(F1_REMOVE_APP_PF_DELAY_MSEC);
        }
    }
    
    return 0;
err:
    return FPGA_ERR_FAIL;
}   

/** 
 * PCI rescan.
 *  
 * @returns
 *  0   on success 
 * -1   on failure
 */
static int
fpga_pci_rescan(void)
{
	/** Setup and write '1' to the PCI rescan file */
	char sysfs_name[NAME_MAX + 1];
	int ret = snprintf(sysfs_name, sizeof(sysfs_name), "/sys/bus/pci/rescan");

	fail_on_quiet(ret < 0, err,
			"Error building the sysfs path for PCI rescan file");
	fail_on_quiet((size_t) ret >= sizeof(sysfs_name), err,
			"sysfs path too long for PCI rescan file");

	/** Write a "1" to the PCI rescan file */
	ret = fpga_pci_write_one2file(sysfs_name);
	fail_on_quiet(ret != 0, err, "fpga_pci_write_one2file failed");

	return 0;
err:
	return FPGA_ERR_FAIL;
}

int
fpga_pci_rescan_slot_app_pfs(int slot_id)
{
	struct fpga_slot_spec spec; 
	int ret = fpga_pci_get_slot_spec(slot_id, &spec); 
	fail_on_quiet(ret != 0, err, "fpga_pci_get_slot_spec failed");

	ret = fpga_pci_remove_app_pf(&spec.map[FPGA_APP_PF]); 
	fail_on_quiet(ret != 0, err, "fpga_pci_remove_app_pf failed");

	ret = fpga_pci_rescan();
	fail_on_quiet(ret != 0, err, "fpga_pci_rescan failed");

	return 0;
err:
	return FPGA_ERR_FAIL;
}
