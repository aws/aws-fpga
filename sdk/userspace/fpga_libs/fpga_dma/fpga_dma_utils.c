/*
 * Copyright 2015-2018 Amazon.com, Inc. or its affiliates. All Rights Reserved.
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
#include <fcntl.h>
#include <errno.h>
#include <stdlib.h>
#include <unistd.h>
#include <string.h>
#include <sys/stat.h>
#include <fcntl.h>
#include <libgen.h>

#include <sys/types.h>
#include <dirent.h>

#include "utils/log.h"
#include "fpga_dma.h"
#include "fpga_pci.h"

#define MAX_FD_LEN  256
#define PCI_DEV_FMT "%04x:%02x:%02x.%d"

typedef int (*get_dev_number_t)(char *, int *);

struct dma_opts_s {
    char *drv_name;
    char *drv_model_name;
    char *drv_write_name;
    char *drv_read_name;
    uint8_t n_channels;
    get_dev_number_t get_dev_number_f;
};

static int fpga_dma_get_xdma_dev_number(char *device_name, int *device_num);
static int fpga_dma_get_edma_dev_number(char *device_name, int *device_num);

static const struct dma_opts_s xdma_opts = {
    .drv_name = "xdma",
    .drv_model_name = "xdma",
    .drv_write_name = "h2c",
    .drv_read_name = "c2h",
    .n_channels = 4,
    .get_dev_number_f = fpga_dma_get_xdma_dev_number,
};

static const struct dma_opts_s edma_opts = {
    .drv_name = "edma",
    .drv_model_name = "edma-drv",
    .drv_write_name = "queue",
    .drv_read_name = "queue",
    .n_channels = 1,
    .get_dev_number_f = fpga_dma_get_edma_dev_number,
};

static const struct dma_opts_s *fpga_dma_get_dma_opts(
    enum fpga_dma_driver which_driver)
{
    switch (which_driver) {
        case FPGA_DMA_EDMA: return &edma_opts;
        case FPGA_DMA_XDMA: return &xdma_opts;
        default: return NULL;
    }
}

int fpga_dma_open_queue(enum fpga_dma_driver which_driver, int slot_id,
     int channel, bool is_read)
{
    int rc, fd;
    char device_file[FPGA_DEVICE_FILE_NAME_MAX_LEN];

    rc = fpga_dma_device_id(which_driver, slot_id, channel, is_read,
        device_file);
    /* TODO: this isn't really the right error code. */
    fail_on_with_code(rc, err, rc, -EINVAL,
        "unable to get device id to open DMA queue");

    fd = open(device_file, is_read ? O_RDONLY : O_WRONLY);
    fail_on_with_code(fd < 0, err, rc, fd, "unable to open DMA device queue: %s",
        device_file);

    return fd;
err:
    return rc;
}

int fpga_dma_device_id(enum fpga_dma_driver which_driver, int slot_id,
    int channel, bool is_read,
    char device_file[static FPGA_DEVICE_FILE_NAME_MAX_LEN])
{
    int rc = 0;
    int device_num;
    char read_or_write[16];
    const struct dma_opts_s *dma_opts = fpga_dma_get_dma_opts(which_driver);
    fail_on(rc = (dma_opts == NULL) ? -EINVAL : 0, out, "invalid DMA driver");

    fail_on(rc = (channel >= dma_opts->n_channels || channel < 0) ? -EINVAL : 0,
        out, "invalid channel specification");

    if (is_read) {
        rc = snprintf(read_or_write, sizeof(read_or_write), "%s",
            dma_opts->drv_read_name);
    } else {
        rc = snprintf(read_or_write, sizeof(read_or_write), "%s",
            dma_opts->drv_write_name);
    }

    if (rc < 1) {
        return FPGA_ERR_SOFTWARE_PROBLEM;
    }

    rc = fpga_pci_get_dma_device_num(which_driver, slot_id, &device_num);
    fail_on(rc != 0, out, "Unable to get device number");


    rc = snprintf(device_file, MAX_FD_LEN, "/dev/%s%i_%s_%d",
                  dma_opts->drv_name,
                  device_num,
                  read_or_write,
                  channel);
    fail_on_with_code(rc < 0, out, rc, FPGA_ERR_SOFTWARE_PROBLEM,
        "Could not generate device_file");
    rc = 0;

out:
    return rc;
}

int fpga_dma_burst_read(int fd, uint8_t *buffer, size_t xfer_sz,
    size_t address)
{
    int rc;
    size_t read_offset = 0;
    fail_on(rc = (fd < 0) ? -EINVAL : 0, out,
        "Invalid file descriptor passed to function.");

    while (read_offset < xfer_sz) {
        rc = pread(fd,
            /* buf pointer  */ buffer + read_offset,
            /* size of xfer */ xfer_sz - read_offset,
            /* read address */ address + read_offset);
        if (rc < 0) {
            fail_on_with_code(rc < 0, out, rc, -errno, "call to pread failed.");
        }
        read_offset += rc;
    }
    rc = 0;
out:
    return rc;
}


int fpga_dma_burst_write(int fd, uint8_t *buffer, size_t xfer_sz,
    size_t address)
{
    int rc;
    size_t write_offset = 0;
    fail_on(rc = (fd < 0) ? -EINVAL : 0, out,
        "Invalid file descriptor passed to function.");

    while (write_offset < xfer_sz) {
        rc = pwrite(fd,
            /* buf pointer  */ buffer + write_offset,
            /* size of xfer */ xfer_sz - write_offset,
            /* read address */ address + write_offset);
        if (rc < 0) {
            fail_on_with_code(rc < 0, out, rc, -errno, "call to pwrite failed.");
        }
        write_offset += rc;
    }
    rc = 0;
out:
    return rc;
}

int fpga_pci_get_dma_device_num(enum fpga_dma_driver which_driver,
    int slot_id, int *device_num)
{
    int rc;
    char dbdf[16];
    char path[64];
    int _device_num;
    struct dirent *entry;
    char real_path[MAX_FD_LEN];
    char *possible_dbdf = NULL;
    struct fpga_pci_resource_map resource;
    char sysfs_path_instance[MAX_FD_LEN + sizeof(entry->d_name) + sizeof(path)];

    const struct dma_opts_s *dma_opts = fpga_dma_get_dma_opts(which_driver);
    fail_on_with_code(!dma_opts, err, rc, -EINVAL, "invalid DMA driver");
    rc = snprintf(path, sizeof(path), "/sys/class/%s", dma_opts->drv_name);
    fail_on_with_code(rc < 1, err, rc, FPGA_ERR_SOFTWARE_PROBLEM,
        "snprintf failed");

    /* This call must be before the lock, because the call holds the lock. */
    rc = fpga_pci_get_resource_map(slot_id, FPGA_APP_PF, &resource);
    fail_on(rc, err, "Could not get resource map");
    rc = snprintf(dbdf,
                  sizeof(dbdf),
                  PCI_DEV_FMT,
                  resource.domain,
                  resource.bus,
                  resource.dev,
                  resource.func);
    fail_on_with_code(rc < 1, err, rc, FPGA_ERR_SOFTWARE_PROBLEM,
        "Could not record DBDF");

    DIR *dirp = opendir(path);
    fail_on_with_code(!dirp, err, rc, FPGA_ERR_SOFTWARE_PROBLEM,
        "opendir failed for path=%s", path);

#if defined(FPGA_PCI_USE_READDIR_R)
    struct dirent entry_stack, *result;
    entry = &entry_stack;
    memset(entry, 0, sizeof(struct dirent));
#else
    /**
     * Protect calls to readdir with a mutex because multiple threads may call
     * this function, which always reads from the same directory. The man page
     * for readdir says the POSIX spec does not require threadsafety.
     */
    pthread_mutex_lock(&fpga_pci_readdir_mutex);
#endif

    while (true) {
        /* reset so that the loop termination detection below works */
        _device_num = -1;

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

        rc = (*dma_opts->get_dev_number_f)(entry->d_name, &_device_num);
        if (rc != 0) {
            continue;
        }

        rc = snprintf(sysfs_path_instance, sizeof(sysfs_path_instance),
            "%s/%s/device", path, entry->d_name);
        fail_on_with_code(rc < 2, err_unlock, rc, FPGA_ERR_SOFTWARE_PROBLEM,
            "snprintf failed to build sysfs path");
        possible_dbdf = realpath(sysfs_path_instance, real_path);
        if (possible_dbdf == NULL) {
            continue;
        }
        possible_dbdf = basename(real_path);
        if (strncmp(possible_dbdf, dbdf, 12) == 0) {
            break; /* found device */
        }
        /* continue... */
    }
#if !defined(FPGA_PCI_USE_READDIR_R)
    pthread_mutex_unlock(&fpga_pci_readdir_mutex);
#endif
    fail_on_with_code(_device_num == -1, err, rc, FPGA_ERR_PCI_MISSING,
        "Unable to find device num");

    closedir(dirp);
    *device_num = _device_num;
    errno = 0;
    return 0;

err_unlock:
#if !defined(FPGA_PCI_USE_READDIR_R)
    pthread_mutex_unlock(&fpga_pci_readdir_mutex);
#endif

err:
    if (dirp) {
        closedir(dirp);
    }
    errno = 0;
    return rc;
}

static int fpga_dma_get_xdma_dev_number(char *device_name, int *device_num)
{
    int rc;
    int num;
    rc = sscanf(device_name, "xdma%d_control", &num);
    if (rc == 1) {
        *device_num = num;
        return 0;
    }
    return FPGA_ERR_SOFTWARE_PROBLEM;
}

static int fpga_dma_get_edma_dev_number(char *device_name, int *device_num)
{
    int rc;
    int num;
    rc = sscanf(device_name, "edma%d_queue_0", &num);
    if (rc == 1) {
        *device_num = num;
        return 0;
    }
    return FPGA_ERR_SOFTWARE_PROBLEM;
}
