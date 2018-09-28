/*
 * Amazon FPGA Hardware Development Kit
 *
 * Copyright 2018 Amazon.com, Inc. or its affiliates. All Rights Reserved.
 *
 * Licensed under the Amazon Software License (the "License"). You may not use
 * this file except in compliance with the License. A copy of the License is
 * located at
 *
 *    http://aws.amazon.com/asl/
 *
 * or in the "license" file accompanying this file. This file is distributed on
 * an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, express or
 * implied. See the License for the specific language governing permissions and
 * limitations under the License.
 */

#include <stdio.h>
#include <fcntl.h>
#include <errno.h>
#include <string.h>
#include <stdlib.h>
#include <unistd.h>
#include <poll.h>

#include "fpga_pci.h"
#include "fpga_mgmt.h"
#include "fpga_dma.h"
#include "utils/lcd.h"

#include "test_dram_dma_common.h"

#define	MEM_16G              (1ULL << 34)
#define USER_INTERRUPTS_MAX  (16)

/* use the standard out logger */
static const struct logger *logger = &logger_stdout;

void usage(const char* program_name);
int retention_dma_example(int slot_id, size_t buffer_size);

int main(int argc, char **argv) {
    int rc;
    int slot_id = 0;

    switch (argc) {
    case 1:
        break;
    case 3:
        sscanf(argv[2], "%x", &slot_id);
        break;
    default:
        usage(argv[0]);
        return 1;
    }

    /* setup logging to print to stdout */
    rc = log_init("test_dram_dma");
    fail_on(rc, out, "Unable to initialize the log.");
    rc = log_attach(logger, NULL, 0);
    fail_on(rc, out, "%s", "Unable to attach to the log.");

    /* initialize the fpga_plat library */
    rc = fpga_mgmt_init();
    fail_on(rc, out, "Unable to initialize the fpga_mgmt library");

    /* check that the AFI is loaded */
    log_info("Checking to see if the right AFI is loaded...");
    rc = check_slot_config(slot_id);
    fail_on(rc, out, "slot config is not correct");

    /* run the dma test example */
    rc = retention_dma_example(slot_id, 1ULL << 24);
    fail_on(rc, out, "DMA example failed");

out:
    log_info("TEST %s", (rc == 0) ? "PASSED" : "FAILED");
    return rc;
}

void usage(const char* program_name) {
    printf("usage: %s [--slot <slot>]\n", program_name);
}

/**
 * This example fills a buffer with random data and then uses DMA to copy that
 * buffer into each of the 4 DDR DIMMS.
 */
int retention_dma_example(int slot_id, size_t buffer_size)
{
    char *afi_id;
    int write_fd, read_fd, dimm, rc;
    struct fpga_mgmt_image_info info = {0};

    union fpga_mgmt_load_local_image_options opt;
    static const uint32_t cli_request_timeout    = 60;   /* number of times to poll */
    static const uint32_t cli_request_poll_delay = 1000; /* msec */

    write_fd = -1;
    read_fd = -1;

    uint8_t *write_buffer = malloc(buffer_size);
    uint8_t *read_buffer = malloc(buffer_size);
    if (write_buffer == NULL || read_buffer == NULL) {
        rc = -ENOMEM;
        goto out;
    }

    /* get local image description to get the AFI id */
    rc = fpga_mgmt_describe_local_image(slot_id, &info, 0);
    fail_on(rc, out, "Unable to get local image information. Are you running "
        "as root?");
    afi_id = &info.ids.afi_id[0];

    /* open the write (host to card) DMA queue */
    write_fd = fpga_dma_open_queue(FPGA_DMA_XDMA, slot_id,
        /*channel*/ 0, /*is_read*/ false);
    fail_on((rc = (write_fd < 0) ? -1 : 0), out, "unable to open write dma queue");

    /* generate some random data to put in the buffer */
    rc = fill_buffer_urandom(write_buffer, buffer_size);
    fail_on(rc, out, "unabled to initialize buffer");

    /* DMA the buffer into each of the 4 DIMMs */
    for (dimm = 0; dimm < 4; dimm++) {
        log_info("Using DMA to write data to DIMM %d", dimm);
        rc = fpga_dma_burst_write(write_fd, write_buffer, buffer_size,
            dimm * MEM_16G);
        fail_on(rc, out, "DMA write failed on DIMM: %d, rc = %d (%s)", dimm, rc,
            fpga_mgmt_strerror(rc));
    }

    close(write_fd);
    write_fd = -1;

    /* setup the load AFI request object */
    fpga_mgmt_init_load_local_image_options(&opt);
    opt.slot_id = slot_id;
    opt.afi_id = afi_id;
    opt.flags = FPGA_CMD_DRAM_DATA_RETENTION; /* load with retention */

    /* load the AFI */
    log_info("loading afi %s ...", afi_id);
    rc = fpga_mgmt_load_local_image_sync_with_options(&opt,
        cli_request_timeout, cli_request_poll_delay, 0);
    fail_on(rc != 0, out, "err: %d, %s", rc, fpga_mgmt_strerror(rc));
    log_info("load complete");

    /* open the read (card to host) DMA queue */
    read_fd = fpga_dma_open_queue(FPGA_DMA_XDMA, slot_id,
        /*channel*/ 0, /*is_read*/ true);
    fail_on((rc = (read_fd < 0) ? -1 : 0), out, "unable to open read dma queue");

    /* read each DIMM and compare it to the original buffer */
    bool passed = true;
    for (dimm = 0; dimm < 4; dimm++) {
        rc = fpga_dma_burst_read(read_fd, read_buffer, buffer_size,
            dimm * MEM_16G);
        fail_on(rc, out, "DMA read failed on DIMM: %d, rc = %d (%s)", dimm, rc,
            fpga_mgmt_strerror(rc));

        uint64_t differ = buffer_compare(read_buffer, write_buffer, buffer_size);
        if (differ != 0) {
            log_error("DIMM %d failed with %lu bytes which differ", dimm, differ);
            passed = false;
        } else {
            log_info("DIMM %d passed!", dimm);
        }
    }
    rc = (passed) ? 0 : 1;

out:
    /* clean up */
    if (write_buffer != NULL) {
        free(write_buffer);
    }
    if (read_buffer != NULL) {
        free(read_buffer);
    }
    if (write_fd >= 0) {
        close(write_fd);
    }
    if (read_fd >= 0) {
        close(read_fd);
    }
    /* if there is an error code, exit with status 1 */
    return (rc != 0 ? 1 : 0);
}
