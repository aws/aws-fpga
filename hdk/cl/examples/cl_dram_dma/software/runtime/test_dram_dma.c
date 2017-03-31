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
#include <fcntl.h>
#include <errno.h>
#include <string.h>
#include <stdlib.h>
#include <unistd.h>

#include <fpga_pci.h>
#include <fpga_mgmt.h>
#include <utils/lcd.h>

static uint16_t pci_vendor_id = 0x1D0F; /* Amazon PCI Vendor ID */
static uint16_t pci_device_id = 0xF001;
/* */

#define	MEM_16G		(1ULL << 34)

/* use the stdout logger */
const struct logger *logger = &logger_stdout;

int dma_example(int slot_id);

int main(int argc, char **argv) {
    int rc;
    int slot_id;

    /* setup logging to print to stdout */
    rc = log_init("test_dram_dma");
    fail_on(rc, out, "Unable to initialize the log.");
    rc = log_attach(logger, NULL, 0);
    fail_on(rc, out, "%s", "Unable to attach to the log.");

    /* initialize the fpga_plat library */
    rc = fpga_mgmt_init();
    fail_on(rc, out, "Unable to initialize the fpga_mgmt library");

    slot_id = 0;
    return dma_example(slot_id);


out:
    return 1;
}

static int
check_slot_config(int slot_id)
{
    int rc;
    struct fpga_mgmt_image_info info = {0};

    /* get local image description, contains status, vendor id, and device id */
    rc = fpga_mgmt_describe_local_image(slot_id, &info, 0);
    fail_on(rc, out, "Unable to get local image information");

    /* check to see if the slot is ready */
    if (info.status != FPGA_STATUS_LOADED) {
        rc = 1;
        fail_on(rc, out, "Slot %d is not ready", slot_id);
    }

    /* confirm that the AFI that we expect is in fact loaded */
    if (info.spec.map[FPGA_APP_PF].vendor_id != pci_vendor_id ||
        info.spec.map[FPGA_APP_PF].device_id != pci_device_id) {
        rc = 1;
        fail_on(rc, out, "The PCI vendor id and device of the loaded image are "
                         "not the expected values.");
    }

out:
    return rc;
}

/*    static const uint32_t DRAM_ACCESS_DISABLE_REGS[4] =
        {0x130, 0x230, 0x330, 0x430};
        rc = fpga_pci_poke(pci_bar_handle, DRAM_ACCESS_DISABLE_REGS[i], 0);
*/

/* helper function to initialize a buffer that would be written to the FPGA later */

void
rand_string(char *str, size_t size)
{
    static const char charset[] =
        "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRTSUVWXYZ1234567890";
    static bool seeded = false;

    if (!seeded) {
        srand(time(NULL));
        seeded = true;
    }

    for(int i = 0; i < size-1; ++i) {
        unsigned int key = rand() % (sizeof charset - 1);
        str[i] = charset[key];
    }

    str[size-1] = '\0';
}

/* 
 * Write 4 identical buffers to the 4 different DRAM channels of the AFI
 * using fsync() between the writes and read to insure order
 */

int dma_example(int slot_id) {
    int fd, rc;
    char *write_buffer, *read_buffer;
    static const size_t buffer_size = 128;
    int channel=0;

    read_buffer = NULL;
    write_buffer = NULL;
    fd = -1;

    /* make sure the AFI is loaded and ready */
    rc = check_slot_config(slot_id);
    fail_on(rc, out, "slot config is not correct");

    fd = open("/dev/edma0_queue_0", O_RDWR);
    fail_on((rc = (fd < 0)? 1:0), out, "unable to open DMA queue. "
        "Is the kernel driver loaded?");

    write_buffer = (char *)malloc(buffer_size);
    read_buffer = (char *)malloc(buffer_size);
    if (write_buffer == NULL || read_buffer == NULL) {
        rc = ENOMEM;
        goto out;
    }

    rand_string(write_buffer, buffer_size);

    for (channel=0;channel < 4; channel++) {
    	
	rc = pwrite(fd, write_buffer, buffer_size, 0x010000000 + channel*MEM_16G);
	
    	fail_on((rc = (rc < 0)? 1:0), out, "call to pwrite failed.");

    }

    /* fsync() will make sure the write made it to the target buffer 
     * before read is done
     */

    fsync(fd);

    for (channel=0;channel < 4; channel++) {
    	rc = pread(fd, read_buffer, buffer_size, 0x010000000 + channel*MEM_16G);
    	fail_on((rc = (rc < 0)? 1:0), out, "call to pread failed.");

    	if (memcmp(write_buffer, read_buffer, buffer_size) == 0) {
        	printf("DRAM DMA read the same string as it wrote on channel %d (it worked correctly!)\n", channel);
    	} else {
        	int i;

        	printf("Bytes written to channel %d:\n", channel);
        	for (i = 0; i < buffer_size; ++i) {
            		printf("%c", write_buffer[i]);
        	}
        	
		printf("\n\n");

        	printf("Bytes read:\n");
        	for (i = 0; i < buffer_size; ++i) {
            		printf("%c", read_buffer[i]);
        	}
        printf("\n\n");
    	}
    }

out:
    if (write_buffer != NULL) {
        free(write_buffer);
    }
    if (read_buffer != NULL) {
        free(read_buffer);
    }
    if (fd >= 0) {
        close(fd);
    }
    /* if there is an error code, exit with status 1 */
    return (rc != 0 ? 1 : 0);
}
