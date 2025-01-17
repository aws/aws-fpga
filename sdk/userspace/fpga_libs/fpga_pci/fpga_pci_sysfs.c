/*
 * Copyright 2020 Amazon.com, Inc. or its affiliates. All Rights Reserved.
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
#include <pthread.h>

static int fpga_pci_rescan(void);
static int fpga_pci_check_app_pf(struct fpga_pci_resource_map *app_map,
	bool exists);
static int fpga_pci_check_app_pf_sysfs(char *dir_name, bool exists);

#if !defined(_BSD_SOURCE) && !defined(_SVID_SOURCE)
pthread_mutex_t fpga_pci_readdir_mutex = PTHREAD_MUTEX_INITIALIZER;
#else
#define FPGA_PCI_USE_READDIR_R
#endif

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
	int ret = 0;

	fail_on_with_code(!path, err, ret, FPGA_ERR_SOFTWARE_PROBLEM, "path is NULL");
	fail_on_with_code(!id, err, ret, FPGA_ERR_SOFTWARE_PROBLEM, "id is NULL");

	FILE *fp = fopen(path, "r");
	fail_on_quiet((ret = (!fp) ? -errno: 0), err, "Error opening %s", path);

	uint32_t tmp_id;
	ret = fscanf(fp, "%x", &tmp_id);
	fail_on_quiet(ret < 0, err_close, "Error parsing %s", path);

	*id = tmp_id;

	fclose(fp);
	return 0;

err_close:
	fclose(fp);
	ret = FPGA_ERR_UNRESPONSIVE; /* couldn't parse the id */
err:
	errno = 0;
	return ret;
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
	int ret = FPGA_ERR_FAIL;

	int fd = open(path, O_WRONLY);
	fail_on(fd == -1, err, "opening %s", path);

	char buf[] = { '1', 0 };
	ret = -!!write_loop(fd, buf, sizeof(buf));
	fail_on(ret != 0, err_close, "error writing %s", path);

err_close:
	close(fd);
err:
	errno = 0;
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
	int ret = 0;
	fail_on_with_code(!dir_name, err, ret, FPGA_ERR_SOFTWARE_PROBLEM,
		"dir_name is NULL");
	fail_on_with_code(!map, err, ret, FPGA_ERR_SOFTWARE_PROBLEM, "map is NULL");

	uint32_t domain;
	uint32_t bus;
	uint32_t dev;
	int func;
	ret = sscanf(dir_name, PCI_DEV_FMT, &domain, &bus, &dev, &func);
	fail_on_with_code(ret != 4, err, ret, FPGA_ERR_SOFTWARE_PROBLEM,
		"sscanf failed for DBDF");

	map->domain = domain;
	map->bus = bus;
	map->dev = dev;
	map->func = func;
	ret = 0;
err:
	return ret;
}

/**
 * Return PCI resource info using the PCI directory name and resource
 * number.
 *
 * @param[in]		dir_name		the PCI device directory name
 * @param[in]		resource_num	the resource number
 * @param[in,out]   resource_size	the returned resource size
 * @param[in,out]   burstable		the returned resource burstable flag
 *
 * @returns
 *  0	on success
 * -1	on failure
 */
static int
fpga_pci_get_pci_resource_info(char *dir_name,
		uint8_t resource_num, uint64_t *resource_size, bool *burstable)
{
	int ret, err_rc;

	err_rc = 0;

	fail_on_with_code(!dir_name, err, err_rc, FPGA_ERR_SOFTWARE_PROBLEM,
		"dir_name is NULL");
	fail_on_with_code(!resource_size, err, err_rc, FPGA_ERR_SOFTWARE_PROBLEM,
		"resource_size is NULL");
	fail_on_with_code(!burstable, err, err_rc, FPGA_ERR_SOFTWARE_PROBLEM,
		"burstable is NULL");

	char sysfs_name[NAME_MAX + 1];
	ret = snprintf(sysfs_name, sizeof(sysfs_name),
			"/sys/bus/pci/devices/%s/resource%u", dir_name,
			resource_num);

	fail_on_with_code(ret < 0, err, err_rc, FPGA_ERR_SOFTWARE_PROBLEM,
		"Error building the sysfs path for resource%u", resource_num);
	fail_on_with_code((size_t) ret >= sizeof(sysfs_name), err, err_rc,
		FPGA_ERR_SOFTWARE_PROBLEM,
		"sysfs path too long for resource%u", resource_num);

	/** Check for file existence, obtain the file size */
	struct stat file_stat;
	ret = stat(sysfs_name, &file_stat);
	fail_on_quiet(err_rc = (ret != 0) ? FPGA_ERR_PCI_MISSING : 0, err,
		"stat failed, path=%s", sysfs_name);

	*resource_size = file_stat.st_size;

	ret = snprintf(sysfs_name, sizeof(sysfs_name),
			"/sys/bus/pci/devices/%s/resource%u_wc", dir_name,
			resource_num);

	fail_on_with_code(ret < 0, err, err_rc, FPGA_ERR_SOFTWARE_PROBLEM,
		"Error building the sysfs path for resource%u", resource_num);
	fail_on_with_code((size_t) ret >= sizeof(sysfs_name), err, err_rc,
		FPGA_ERR_SOFTWARE_PROBLEM,
		"sysfs path too long for resource%u", resource_num);

	memset(&file_stat, 0, sizeof(struct stat));
	ret = stat(sysfs_name, &file_stat);
	*burstable = (ret == 0);

err:
	errno = 0;
	return err_rc;
}

/**
 * Return the PCI resources for the given sysfs directory name.
 *
 * @param[in]		dir_name	the PCI device directory name
 * @param[in,out]	map			the PCI resource map
 *
 * @returns
 *  0	on success
 * -1	on failure
 */
static int
fpga_pci_get_resources(char *dir_name, struct fpga_pci_resource_map *map)
{
	int ret;
	bool found_one_device = false;
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
		if (ret == FPGA_ERR_PCI_MISSING) {
			log_debug("Unable to read resource information for %d", resource_num);
		} else if (ret != 0) {
			return ret;
		} else {
			map->resource_size[resource_num] = resource_size;
			map->resource_burstable[resource_num] = burstable;
			found_one_device = true;
		}
	}
	return (found_one_device) ? 0 : FPGA_ERR_PCI_MISSING;
}


/**
 * Return the PCI resource map identifiers for the given sysfs directory name.
 *
 * @param[in]		dir_name	the PCI device directory name
 * @param[in,out]	map			the PCI resource map
 *
 * @returns
 *  0	on success
 * -1	on failure
 */
static int
fpga_pci_get_resource_map_ids(char *dir_name, struct fpga_pci_resource_map *map)
{
	int ret = 0;
	uint16_t vendor_id = 0;
	uint16_t device_id = 0;
	uint16_t subsystem_vendor_id = 0;
	uint16_t subsystem_device_id = 0;

	fail_on_with_code(!dir_name, err, ret, FPGA_ERR_SOFTWARE_PROBLEM,
		"dir_name is NULL");

	/** Setup and read the PCI Vendor ID */
	char sysfs_name[NAME_MAX + 1];
	ret = snprintf(sysfs_name, sizeof(sysfs_name),
			"/sys/bus/pci/devices/%s/vendor", dir_name);

	fail_on_with_code(ret < 0, err, ret, FPGA_ERR_SOFTWARE_PROBLEM,
		"Error building the sysfs path for vendor");
	fail_on_with_code((size_t) ret >= sizeof(sysfs_name), err, ret,
		FPGA_ERR_SOFTWARE_PROBLEM, "sysfs path too long for vendor");

	ret = fpga_pci_get_id(sysfs_name, &vendor_id);
	fail_on_quiet(ret != 0, err, "Error retrieving vendor_id");

	/** Setup and read the PCI Device ID */
	ret = snprintf(sysfs_name, sizeof(sysfs_name),
			"/sys/bus/pci/devices/%s/device", dir_name);

	fail_on_with_code(ret < 0, err, ret, FPGA_ERR_SOFTWARE_PROBLEM,
		"Error building the sysfs path for device");
	fail_on_with_code((size_t) ret >= sizeof(sysfs_name), err, ret,
		FPGA_ERR_SOFTWARE_PROBLEM, "sysfs path too long for device");

	ret = fpga_pci_get_id(sysfs_name, &device_id);
	fail_on_quiet(ret != 0, err, "Error retrieving device_id");

	/** Setup and read the PCI Subsystem Vendor ID */
	ret = snprintf(sysfs_name, sizeof(sysfs_name),
			"/sys/bus/pci/devices/%s/subsystem_vendor", dir_name);

	fail_on_with_code(ret < 0, err, ret, FPGA_ERR_SOFTWARE_PROBLEM,
		"Error building the sysfs path for subsystem_vendor");
	fail_on_with_code((size_t) ret >= sizeof(sysfs_name), err, ret,
		FPGA_ERR_SOFTWARE_PROBLEM, "sysfs path too long for subsystem_vendor");

	ret = fpga_pci_get_id(sysfs_name, &subsystem_vendor_id);
	fail_on_quiet(ret != 0, err, "Error retrieving subsystem_vendor");

	/** Setup and read the PCI Subsystem Device ID */
	ret = snprintf(sysfs_name, sizeof(sysfs_name),
			"/sys/bus/pci/devices/%s/subsystem_device", dir_name);

	fail_on_with_code(ret < 0, err, ret, FPGA_ERR_SOFTWARE_PROBLEM,
		"Error building the sysfs path for subsystem_device");
	fail_on_with_code((size_t) ret >= sizeof(sysfs_name), err, ret,
		FPGA_ERR_SOFTWARE_PROBLEM, "sysfs path too long for subsystem_device");

	ret = fpga_pci_get_id(sysfs_name, &subsystem_device_id);
	fail_on_quiet(ret != 0, err, "Error retrieving subsystem_device");

	/** Fill in the DBDF */
	ret = fpga_pci_get_dbdf(dir_name, map);
	fail_on(ret != 0, err, "Error retrieving DBDF from dir_name=%s",
			dir_name);

	/** Setup the returned IDs */
	map->vendor_id = vendor_id;
	map->device_id = device_id;
	map->subsystem_vendor_id = subsystem_vendor_id;
	map->subsystem_device_id = subsystem_device_id;

	ret = 0;
err:
	return ret;
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
	int ret = 0;

	fail_on_with_code(!mbox_map || !app_map || !app_dir_name || !app_dir_name_size,
		err, ret, FPGA_ERR_SOFTWARE_PROBLEM, "Invalid input parameters");

	/** Construct the app dir name based on the mbox_map */
	ret = snprintf(app_dir_name, app_dir_name_size, PCI_DEV_FMT,
			mbox_map->domain, mbox_map->bus,
			GET_DEV_NUM_FROM_FPGA_MBOX_MAP(mbox_map), GET_FUNC_NUM_FROM_FPGA_MBOX_MAP(mbox_map));

	fail_on_with_code(ret < 0, err, ret, FPGA_ERR_SOFTWARE_PROBLEM,
		"Error building the app_dir_name");
	fail_on_with_code((size_t) ret >= app_dir_name_size, err, ret,
		FPGA_ERR_SOFTWARE_PROBLEM, "app_dir_name too long");

	/**
	 * Check that the app_pf exists.  If not found, make a minimal attempt to
	 * recover it.
	 */
	ret = fpga_pci_check_app_pf_sysfs(app_dir_name, true); /** exists==true*/
	fail_on(ret != 0, err, "fpga_pci_check_app_pf_sysfs failed");

	/**
	 * Fill in the app_map for the given app_dir_name.  If the app_dir_name is
	 * not yet ready (e.g. sysfs files are in the process of being recreated
	 * due to a remove/rescan) make a minimal retry attempt.
	 */
	bool done = false;
	uint32_t retries = 0;
	while (!done) {
		ret = fpga_pci_get_resource_map_ids(app_dir_name, app_map);
		if (ret == 0) {
			done = true;
		} else {
			fail_on_with_code(retries >= FPGA_CHECK_APP_PF_MAX_RETRIES, err, ret,
				FPGA_ERR_UNRESPONSIVE,
				"fpga_pci_get_resource_map_ids failed for app_dir_name=%s",
				app_dir_name);
			msleep(FPGA_CHECK_APP_PF_DELAY_MSEC);
			retries++;
		}
	}

	ret = 0;
err:
	return ret;
}

int fpga_acquire_readdir_lock() {
#if !defined(FPGA_PCI_USE_READDIR_R)
  return pthread_mutex_lock(&fpga_pci_readdir_mutex);
#else
  return 0;
#endif
}

int fpga_release_readdir_lock() {
#if !defined(FPGA_PCI_USE_READDIR_R)
  return pthread_mutex_unlock(&fpga_pci_readdir_mutex);
#else
  return 0;
#endif
}

static inline bool fpga_slot_spec_is_initialized(struct fpga_slot_spec *spec)
{
	struct fpga_pci_resource_map *map = &spec->map[FPGA_MGMT_PF];
	return !(map->domain == 0 && map->bus == 0 &&
		map->dev == 0 && map->func == 0);
}


static int
fpga_pci_slot_spec_compare(const void *a, const void *b)
{
	struct fpga_slot_spec *spec_a = (*((struct fpga_slot_spec **)a));
	struct fpga_slot_spec *spec_b = (*((struct fpga_slot_spec **)b));

	int test;

	/* make sure than uninitialized entries fall to the bottom of the list */
	bool a_initialized = fpga_slot_spec_is_initialized(spec_a);
	bool b_initialized = fpga_slot_spec_is_initialized(spec_b);
	if (a_initialized != b_initialized) {
		return (a_initialized) ? -1 : 1;
	}

	test = spec_a->map[FPGA_MGMT_PF].domain - spec_b->map[FPGA_MGMT_PF].domain;
	if (test != 0) return test;

	test = spec_a->map[FPGA_MGMT_PF].bus - spec_b->map[FPGA_MGMT_PF].bus;
	if (test != 0) return test;

	test = spec_a->map[FPGA_MGMT_PF].dev - spec_b->map[FPGA_MGMT_PF].dev;
	if (test != 0) return test;

	return spec_a->map[FPGA_MGMT_PF].func - spec_b->map[FPGA_MGMT_PF].func;
}

static int
fpga_pci_mbox_scan(struct fpga_slot_spec spec_array_out[], int size)
{
	int ret;
	bool found_afi_slot = false;
	char *path = "/sys/bus/pci/devices";
	DIR *dirp = opendir(path);
	fail_on(!dirp, err, "opendir failed for path=%s", path);

	struct dirent *entry;
#if defined(FPGA_PCI_USE_READDIR_R)
	struct dirent entry_stack, *result;
	entry = &entry_stack;
	memset(entry, 0, sizeof(struct dirent));
#else
	/*
	 * Protect calls to readdir with a mutex because multiple threads may call
	 * this function, which always reads from the same directory. The man page
	 * for readdir says the POSIX spec does not require threadsafety.
	 */
	fpga_acquire_readdir_lock();
#endif

	unsigned int slot_dev_index = 0;
	struct fpga_pci_resource_map search_map;

	/* allocate space for sorting the spec_array */
	struct fpga_slot_spec *spec_array[FPGA_SLOT_MAX];
	struct fpga_slot_spec spec_array_storage[FPGA_SLOT_MAX];
	memset(spec_array_storage, 0, sizeof(spec_array_storage));
	for (int i = 0; i < FPGA_SLOT_MAX; ++i) {
		spec_array[i] = &spec_array_storage[i];
	}

	/*
   * Loop through the sysfs device directories
	 * -we first find the mbox dev then handle the app dev as a fixed
	 *  mapping based off of the mbox dev's pci resource map
	 *  (see fpga_pci_mbox2app).
	 */
	while (true) {

#if defined(FPGA_PCI_USE_READDIR_R)
		memset(entry, 0, sizeof(struct dirent));
		readdir_r(dirp, entry, &result);
		if (result == NULL) {
			/** No more directories */
			break;
		}
#else
		entry = readdir(dirp);
		if (entry == NULL) {
			/** No more directories */
			break;
		}
#endif

		/** Handle the current directory entry */
		memset(&search_map, 0, sizeof(struct fpga_pci_resource_map));
		ret = fpga_pci_get_resource_map_ids(entry->d_name, &search_map);
		if (ret != 0) {
			continue;
		}

		if (search_map.vendor_id == FPGA_MBOX_VENDOR_ID &&
			(IS_F1((&search_map)) || IS_F2((&search_map)))) {
			/* mbox resources */
			ret = fpga_pci_get_resources(entry->d_name, &search_map);
			fail_on(ret != 0, err_unlock, "Error retrieving resource information");

			/* copy the results into the spec_array */
			spec_array[slot_dev_index]->map[FPGA_MGMT_PF] = search_map;
			found_afi_slot = true;
			slot_dev_index += 1;
			if (slot_dev_index >= sizeof_array(spec_array)) {
				break;
			}
		}
	}
#if !defined(FPGA_PCI_USE_READDIR_R)
	fpga_release_readdir_lock();
#endif
	fail_on_with_code(!found_afi_slot, err, ret, FPGA_ERR_PCI_MISSING,
		"No fpga-image-slots found");

	closedir(dirp);

	/* sort the spec_array and copy it into the out parameter */
	qsort(spec_array, sizeof_array(spec_array), sizeof(spec_array[0]),
		fpga_pci_slot_spec_compare);
	for (unsigned int i = 0; i < min((unsigned) size, sizeof_array(spec_array)); ++i) {
		spec_array_out[i] = *spec_array[i];
	}

	errno = 0;
	return 0;

err_unlock:
#if !defined(FPGA_PCI_USE_READDIR_R)
	fpga_release_readdir_lock();
#endif

err:
	if (dirp) {
		closedir(dirp);
	}
	errno = 0;
	return ret;
}

/**
 * Fill in the application PF information in a slot spec which already
 * has the mailbox PF initialized.
 */
static int
fpga_pci_complete_slot_spec(struct fpga_slot_spec *spec)
{
	int ret;
	char app_dir_name[NAME_MAX + 1];
	struct fpga_pci_resource_map app_map;

	/* fill in app resources */
	memset(&app_map, 0, sizeof(struct fpga_pci_resource_map));
	app_dir_name[0] = 0;
	ret = fpga_pci_mbox2app(&spec->map[FPGA_MGMT_PF], &app_map,
		app_dir_name, sizeof(app_dir_name));
	fail_on(ret != 0, out, "Error retrieving app pf information");

	ret = fpga_pci_get_resources(app_dir_name, &app_map);
	fail_on(ret != 0, out, "Error retrieving resource information");

	/* copy the results into the spec_array */
	spec->map[FPGA_APP_PF] = app_map;

out:
	return ret;
}

int
fpga_pci_get_all_slot_specs(struct fpga_slot_spec spec_array[], int size)
{
	int rc;

	rc = fpga_pci_mbox_scan(spec_array, size);
	fail_on(rc, out, "failed to enumerate FPGA slots");

	for (int i = 0; i < size; ++i) {
		/* after encountering the first empty slot, stop iterating */
		if (!fpga_slot_spec_is_initialized(&spec_array[i])) {
			break;
		}
		/* fill in app resources */
		rc = fpga_pci_complete_slot_spec(&spec_array[i]);
		fail_on(rc, out, "unabled to get APP PF info for slot %d", i);
	}

out:
	return rc;
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

	ret = fpga_pci_mbox_scan(spec_array, size);
	fail_on(ret, err, "failed to enumerate FPGA slots");

	ret = fpga_pci_complete_slot_spec(&spec_array[slot_id]);
	fail_on(ret, err, "unabled to get APP PF info for slot %d", slot_id);

	if (!fpga_slot_spec_is_initialized(&spec_array[slot_id])) {
		log_error("No device matching specified id: %d", slot_id);
		return -ENOENT;
	}

	*spec = spec_array[slot_id];
	return 0;
err:
	return ret;
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
	fail_on(ret, out, "fpga_pci_get_slot_spec failed");

	*map = slot_spec.map[pf_id];
out:
	return ret;
}

/**
 * Check if there is a driver attached for the given app_map.
 *
 * @param[in]   app_map     the application device resource map
 * @param[out]  attached    flag to fill in
 *
 * @returns
 *  0   on success, non-zero on error
 */
static int
fpga_pci_check_app_pf_driver(struct fpga_pci_resource_map *app_map,
    bool *attached)
{
	int ret = 0;

	fail_on_with_code(!app_map, err, ret, FPGA_ERR_SOFTWARE_PROBLEM,
		"app_map is NULL");
	fail_on_with_code(!attached, err, ret, FPGA_ERR_SOFTWARE_PROBLEM,
		"attached is NULL");

	/** Construct the PCI device directory name using the PCI_DEV_FMT */
	char dir_name[NAME_MAX + 1];
	ret = snprintf(dir_name, sizeof(dir_name), PCI_DEV_FMT,
		app_map->domain, app_map->bus, app_map->dev, app_map->func);

	fail_on_with_code(ret < 0, err, ret, FPGA_ERR_SOFTWARE_PROBLEM,
		"Error building the dir_name");
	fail_on_with_code((size_t) ret >= sizeof(dir_name), err, ret,
		FPGA_ERR_SOFTWARE_PROBLEM, "dir_name too long");

	/** Setup the path to the app_pf */
	char sysfs_name[NAME_MAX + 1];
	ret = snprintf(sysfs_name, sizeof(sysfs_name),
		"/sys/bus/pci/devices/%s/driver", dir_name);

	fail_on_with_code(ret < 0, err, ret, FPGA_ERR_SOFTWARE_PROBLEM,
		"Error building the sysfs path for app_pf");
	fail_on_with_code((size_t) ret >= sizeof(sysfs_name), err, ret,
		FPGA_ERR_SOFTWARE_PROBLEM, "sysfs path too long for app_pf");

	log_debug("Checking path=%s for existence", sysfs_name);

	/** Check for file existence */
	struct stat file_stat;
	ret = stat(sysfs_name, &file_stat);

	/** Setup for return */
	*attached = (ret == 0) ? true : false;

	ret = 0;
err:
	errno = 0;
	return ret;
}

/**
 * Check that the application PF exists or not based on the dir_name and
 * exists flag.  If the application PF is supposed to exist but was not
 * found, perform a minimal attempt at recovery be performing a PCI rescan.
 *
 * @param[in]	dir_name	the application PF device directory name
 * @param[in]	exists		flag to check existence or non-existence
 *
 * @returns
 *  0   on success, non-zero on error
 */
static int
fpga_pci_check_app_pf_sysfs(char *dir_name, bool exists)
{
	int ret = 0;

	fail_on(!dir_name, err, "dir_name is NULL");

	/** Setup the path to the app_pf */
	char sysfs_name[NAME_MAX + 1];
	ret = snprintf(sysfs_name, sizeof(sysfs_name),
		"/sys/bus/pci/devices/%s", dir_name);

	fail_on_with_code(ret < 0, err, ret, FPGA_ERR_SOFTWARE_PROBLEM,
		"Error building the sysfs path for app_pf");
	fail_on_with_code((size_t) ret >= sizeof(sysfs_name), err, ret,
		FPGA_ERR_SOFTWARE_PROBLEM, "sysfs path too long for app_pf");

	bool done = false;
	uint32_t retries = 0;
	while (!done) {
		/** Check for file existence */
		struct stat file_stat;
		ret = stat(sysfs_name, &file_stat);
		if (!!ret == !exists) {
			done = true;
		} else {
			fail_on_with_code(retries >= FPGA_CHECK_APP_PF_MAX_RETRIES, err,
				ret, FPGA_ERR_UNRESPONSIVE, "exists=%u, failed for path=%s", exists,
				sysfs_name);
			if (exists) {
				ret = fpga_pci_rescan();
				fail_on(ret, err, "fpga_pci_rescan failed");
			}
			msleep(FPGA_CHECK_APP_PF_DELAY_MSEC);
			retries++;
		}
	}

	ret = 0;
err:
	errno = 0;
	return ret;
}

/**
 * Check that the application PF exists or not based on the app_map and
 * exists flag.  If the application PF is supposed to exist but was not
 * found, perform a minimal attempt at recovery be performing a PCI rescan.
 *
 * @param[in]	app_map		the application device resource map
 * @param[in]	exists		flag to check existence or non-existence
 *
 * @returns
 *  0   on success, non-zero on error
 */
static int
fpga_pci_check_app_pf(struct fpga_pci_resource_map *app_map, bool exists)
{
	int ret = 0;

	fail_on_with_code(!app_map, err, ret, FPGA_ERR_SOFTWARE_PROBLEM,
		"app_map is NULL");

	/** Construct the PCI device directory name using the PCI_DEV_FMT */
	char dir_name[NAME_MAX + 1];
	ret = snprintf(dir_name, sizeof(dir_name), PCI_DEV_FMT,
		app_map->domain, app_map->bus, app_map->dev, app_map->func);

	fail_on(ret < 0, err, "Error building the dir_name");
	fail_on((size_t) ret >= sizeof(dir_name), err, "dir_name too long");

	ret = fpga_pci_check_app_pf_sysfs(dir_name, exists);
	fail_on(ret != 0, err, "fpga_check_app_pf_sysfs failed");

	ret = 0;
err:
	return ret;
}

/**
 * Remove the application PF for the given app map.
 *
 * @param[out]  app_map         the application device resource map to remove
 *
 * @returns
 *  0   on success, non-zero on error
 */
static int
fpga_pci_remove_app_pf(struct fpga_pci_resource_map *app_map)
{
	int ret = 0;
	fail_on_with_code(!app_map, err, ret, FPGA_ERR_SOFTWARE_PROBLEM,
		"app_map is NULL");

	/** Construct the PCI device directory name using the PCI_DEV_FMT */
	char dir_name[NAME_MAX + 1];
	ret = snprintf(dir_name, sizeof(dir_name), PCI_DEV_FMT,
		app_map->domain, app_map->bus, app_map->dev, app_map->func);

	fail_on_with_code(ret < 0, err, ret, FPGA_ERR_SOFTWARE_PROBLEM,
		"Error building the dir_name");
	fail_on_with_code((size_t) ret >= sizeof(dir_name), err, ret,
		FPGA_ERR_SOFTWARE_PROBLEM, "dir_name too long");

	/** Setup the path to the device's remove file */
	char sysfs_name[NAME_MAX + 1];
	ret = snprintf(sysfs_name, sizeof(sysfs_name),
		"/sys/bus/pci/devices/%s/remove", dir_name);

	fail_on_with_code(ret < 0, err, ret, FPGA_ERR_SOFTWARE_PROBLEM,
		"Error building the sysfs path for remove file");
	fail_on_with_code((size_t) ret >= sizeof(sysfs_name), err, ret,
		FPGA_ERR_SOFTWARE_PROBLEM, "sysfs path too long for remove file");

	/** Write a "1" to the device's remove file */
	ret = fpga_pci_write_one2file(sysfs_name);
	fail_on_with_code(ret != 0, err, ret, FPGA_ERR_UNRESPONSIVE,
		"cli_write_one2file failed");

#if 0
	/** Check that the app_pf does not exist */
	/**
	 * NOTE:
	 * A concurrent (remove)+rescan action on another FPGA slot will make this
	 * FPGA's app_pf visible again, so we should not error out here if we see
	 * that the app_pf is still present.
	 */
	ret = fpga_pci_check_app_pf_sysfs(dir_name, false); /** exists==false */
	fail_on(ret != 0, err, "fpga_pci_check_app_pf_sysfs failed");
#endif

	ret = 0;
err:
	errno = 0;
	return ret;
}

/**
 * PCI rescan.
 *
 * @returns
 *  0   on success, non-zero on error
 */
static int
fpga_pci_rescan(void)
{
	/** Setup and write '1' to the PCI rescan file */
	char sysfs_name[NAME_MAX + 1];
	int ret = snprintf(sysfs_name, sizeof(sysfs_name), "/sys/bus/pci/rescan");

	fail_on_with_code(ret < 0, err, ret, FPGA_ERR_SOFTWARE_PROBLEM,
		"Error building the sysfs path for PCI rescan file");
	fail_on_with_code((size_t) ret >= sizeof(sysfs_name), err, ret,
		FPGA_ERR_SOFTWARE_PROBLEM, "sysfs path too long for PCI rescan file");

	/** Write a "1" to the PCI rescan file */
	ret = fpga_pci_write_one2file(sysfs_name);
	fail_on_with_code(ret != 0, err, ret, FPGA_ERR_UNRESPONSIVE,
		"fpga_pci_write_one2file failed");

	ret = 0;
err:
	return ret;
}

int
fpga_pci_rescan_slot_app_pfs(int slot_id)
{
	/** Get the slot spec */
	struct fpga_slot_spec spec;
	int ret = fpga_pci_get_slot_spec(slot_id, &spec);
	fail_on(ret != 0, err, "fpga_pci_get_slot_spec failed");

	/** Check if there is a driver attached to the given app_map */
	struct fpga_pci_resource_map *app_map = &spec.map[FPGA_APP_PF];
	bool attached = false;
	ret = fpga_pci_check_app_pf_driver(app_map, &attached);
	fail_on(ret != 0, err, "fpga_pci_check_app_pf_driver failed");

	/** Remove the app_pf */
	ret = fpga_pci_remove_app_pf(app_map);
	fail_on(ret != 0, err, "fpga_pci_remove_app_pf failed");

	/**
	 * If we found a driver attached to the given app_map, increase
	 * the wait time between remove and rescan.
	 * Note that if the driver takes a long time to complete the
	 * PCI remove fuction (e.g. longer than the below wait time),
	 * we may still fail to expose the changed PCI IDs in the rescan step.
   	 */
	uint32_t delay_msec = (attached) ?
		FPGA_REMOVE_APP_PF_LONG_DELAY_MSEC : FPGA_REMOVE_APP_PF_SHORT_DELAY_MSEC;

	log_info("Driver for " PCI_DEV_FMT " %s attached, waiting %u msec before rescan",
		app_map->domain, app_map->bus, app_map->dev, app_map->func,
		(attached) ? "is" : "is not", delay_msec);

	msleep(delay_msec);

	/** PCI rescan */
	ret = fpga_pci_rescan();
	fail_on(ret != 0, err, "fpga_pci_rescan failed");

	/** Check that the app_pf exists */
	ret = fpga_pci_check_app_pf(app_map, true); /** exists==true */
	fail_on(ret != 0, err, "fpga_pci_check_app_pf failed");

	ret = 0;
err:
	return ret;
}
