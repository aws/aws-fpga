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

#include "utils/log.h"
#include "fpga_dma.h"
#include "fpga_pci.h"

#define MAX_FD_LEN  256
#define PCI_DEV_FMT "%04x:%02x:%02x.%d"

struct dma_opts_s {
    char *drv_name;
    char *drv_model_name;
    char *drv_write_name;
    char *drv_read_name;
    uint8_t n_channels;
};

static const struct dma_opts_s xdma_opts = {
    .drv_name = "xdma",
    .drv_model_name = "xdma",
    .drv_write_name = "h2c",
    .drv_read_name = "c2h",
    .n_channels = 4,
};

static const struct dma_opts_s edma_opts = {
    .drv_name = "edma",
    .drv_model_name = "edma-drv",
    .drv_write_name = "queue",
    .drv_read_name = "queue",
    .n_channels = 1,
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
    fail_on(rc, err, "unable to get device id to open DMA queue");

    fd = open(device_file, is_read ? O_RDONLY : O_WRONLY);
    fail_on(rc = (fd < 0) ? fd : 0, err, "unable to open DMA device queue: %s",
        device_file);

    return fd;
err:
    if (rc > 0) {
        return -rc;
    } else {
        return rc;
    }
}


int fpga_dma_device_id(enum fpga_dma_driver which_driver, int slot_id,
    int channel, bool is_read,
    char device_file[static FPGA_DEVICE_FILE_NAME_MAX_LEN])
{
    int rc = 0;
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
        return FPGA_ERR_FAIL;
    }

    if (which_driver == FPGA_DMA_EDMA) {
        /* TODO: this is not likely to work for multiple slots */
        #define DRV_CHANNEL_FMT "/dev/%s%i_%s_0"
        return snprintf(device_file, MAX_FD_LEN, DRV_CHANNEL_FMT,
            dma_opts->drv_name, slot_id, read_or_write);
    } else if (which_driver == FPGA_DMA_XDMA) {
        /* We have an XDMA driver, we do not know if the descriptors
         * /dev/xdma[07]_[hc]2[ch]_0 correspond to the slots. We will discover
         * using the sysfs mappings of the FPGA card mapping on PCI
         */
        struct fpga_pci_resource_map resource;
        char dbdf[16];
        char sysfs_path[32];
        int actual_instance = -1;
        char real_path[MAX_FD_LEN];

        rc = fpga_pci_get_resource_map(slot_id, FPGA_APP_PF, &resource);
        fail_on(rc, out, "Could not get resource map");
        rc = snprintf(dbdf,
                      16,
                      PCI_DEV_FMT,
                      resource.domain,
                      resource.bus,
                      resource.dev,
                      resource.func);
        fail_on(rc < 1, out, "Could not record DBDF");
        sprintf(sysfs_path, "/sys/class/xdma/");
        for (int s = 0; s < FPGA_SLOT_MAX; s++) {
            char sysfs_path_instance[MAX_FD_LEN];
            char *possible_dbdf = NULL;
            sprintf(sysfs_path_instance, "%sxdma%d_%s_%d/device",
                sysfs_path, s, dma_opts->drv_read_name, channel);
            /* Check if device exists in sys fs */
            if (access(sysfs_path_instance, F_OK) != 0)
                continue;

            possible_dbdf = realpath(sysfs_path_instance, real_path);
            if (possible_dbdf == NULL) {
                fail_on(true, out, "Could not get real path of the device file");
            }
            possible_dbdf = basename(real_path);
            if (strncmp(possible_dbdf, dbdf, 12) == 0) {
                actual_instance = s;
                break;
            }
            continue;
        }
        fail_on(actual_instance == -1, out,
            "Could not find the actual XDMA driver instance for the slot");
        rc = snprintf(device_file,
                      MAX_FD_LEN,
                      DRV_CHANNEL_FMT,
                      dma_opts->drv_name,
                      actual_instance,
                      read_or_write);
        fail_on(rc = (rc < 0) ? FPGA_ERR_FAIL : 0, out,
            "Could not generate device_file");
    }
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
            fail_on((rc = (rc < 0) ? -errno : 0), out, "call to pread failed.");
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
            fail_on((rc = (rc < 0) ? -errno : 0), out, "call to pwrite failed.");
        }
        write_offset += rc;
    }
    rc = 0;
out:
    return rc;
}
