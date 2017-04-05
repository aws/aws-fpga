// Amazon FPGA Hardware Development Kit
//
// Copyright 2016 Amazon.com, Inc. or its affiliates. All Rights Reserved.
//
// Licensed under the Amazon Software License (the "License"). You may not use
// this file except in compliance with the License. A copy of the License is
// located at
//
//    http://aws.amazon.com/asl/
//
// or in the "license" file accompanying this file. This file is distributed on
// an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, express or
// implied. See the License for the specific language governing permissions and
// limitations under the License.

#include <stdio.h>
#include <fcntl.h>
#include <errno.h>
#include <string.h>
#include <stdlib.h>
#include <unistd.h>
#include <poll.h>

#include <fpga_pci.h>
#include <fpga_mgmt.h>
#include <utils/lcd.h>

static uint16_t pci_vendor_id = 0x1D0F; /* Amazon PCI Vendor ID */
static uint16_t pci_device_id = 0xF001;
/* */

#define	MEM_16G		(1ULL << 34)

/* use the stdout logger */
const struct logger *logger = &logger_stdout;

int dma_example(int slot_id, char* device_file);
int interrupt_example(int slot_id);

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

    rc = dma_example(slot_id, "/dev/edma0_queue_0");
    fail_on(rc, out, "DMA example failed");

    rc = interrupt_example(slot_id);
    fail_on(rc, out, "Interrupt example failed");


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
        printf("The slot appears loaded, but the pci vendor or device ID doesn't "
               "match the expected values. You may need to rescan the fpga with \n"
               "fpga-describe-local-image -S %i -R\n"
               "and check /dev/ for the new device file\n",slot_id);
        fail_on(rc, out, "The PCI vendor id and device of the loaded image are "
                         "not the expected values.");
    }

out:
    return rc;
}


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

int dma_example(int slot_id, char* device_file) {
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

    fd = open(device_file, O_RDWR);
    if(fd<0){
        printf("Cannot open device file %s.\nMaybe the EDMA "
               "driver isn't installed, isn't modified to attach to the PCI ID of "
               "your CL, or you're using a device file that doesn't exist?\n"
               "Remember that rescanning your FPGA can change the device file.\n",
               device_file);
        fail_on((rc = (fd < 0)? 1:0), out, "unable to open DMA queue. ");
    }

    write_buffer = (char *)malloc(buffer_size);
    read_buffer = (char *)malloc(buffer_size);
    if (write_buffer == NULL || read_buffer == NULL) {
        rc = ENOMEM;
        goto out;
    }

    rand_string(write_buffer, buffer_size);

    for (channel=0;channel < 4; channel++) {
    	
	rc = pwrite(fd, write_buffer, buffer_size, 0x10000000 + channel*MEM_16G);
	
    	fail_on((rc = (rc < 0)? 1:0), out, "call to pwrite failed.");

    }

    /* fsync() will make sure the write made it to the target buffer 
     * before read is done
     */

    fsync(fd);

    for (channel=0;channel < 4; channel++) {
    	rc = pread(fd, read_buffer, buffer_size, 0x10000000 + channel*MEM_16G);
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

int interrupt_example(int slot_id){
    pci_bar_handle_t pci_bar_handle = PCI_BAR_HANDLE_INIT;
    struct pollfd fds[1];
    uint32_t fd, rd,  read_data;
    char event_file_name[256] = "/dev/fpga0_event0";
//    char event_file_name[256] = "/dev/xdma0_events_0";
    int rc = 0;
    int poll_timeout = 3000;
    int num_fds = 1;
    //int exp_intr_count = 1;
    int pf_id = 0;
    int bar_id = 0;
    int fpga_attach_flags = 0;
    uint32_t interrupt_reg_offset = 0xd00;
    int interrupt_number = 0;


    printf("Starting MSI-X Interrupt test \n");
    rc = fpga_pci_attach(slot_id, pf_id, bar_id, fpga_attach_flags, &pci_bar_handle);
    fail_on(rc, out, "Unable to attach to the AFI on slot id %d", slot_id);

    printf("Polling device file: %s for interrupt events \n", event_file_name);
    if((fd = open(event_file_name, O_RDONLY)) == -1) {
        printf("Error - invalid device\n");
        rc = 1;
        fail_on(rc, out, "Unable to open event device");
    }
    fds[0].fd = fd;
    fds[0].events = POLLIN;


    //Clear the interrupt register
    rc = fpga_pci_poke(pci_bar_handle, interrupt_reg_offset , 0x1 <<(16 + interrupt_number) );
    fail_on(rc, out, "Unable to write to the fpga !");
    rd = poll(fds, num_fds, poll_timeout);

    //Generate and check the MSI-X Interrupts
    printf("Checking to make sure Interrupt trigger and status bits are initially 0 \n");
    rc = fpga_pci_peek(pci_bar_handle, interrupt_reg_offset, &read_data);
    fail_on(rc, out, "Unable to read read from the fpga !");

    if(read_data != 0) {
        printf("Error: Initial values of Interrupt trigger and status bits is not 0 .Actual data = %x \n", read_data);
        rc = 1;
    }
//Try clearing
    rd = poll(fds, num_fds, poll_timeout);
    rd = poll(fds, num_fds, poll_timeout);
    if (rd & POLLIN) {
        printf("Error: Unexpected interrupt events found in the events file: %s\n", event_file_name);
        rc = 1;
//        fail_on(rc, out, "Unexpected interrupts found, not triggered by test");
    }
    close(fd);

    printf("Triggering MSI-X Interrupt 0\n");
    rc = fpga_pci_poke(pci_bar_handle, interrupt_reg_offset , 1 << interrupt_number);
    fail_on(rc, out, "Unable to write to the fpga !");

    rd = poll(fds, num_fds, poll_timeout);
    if( rd >0 && fds[0].revents & POLLIN){
        printf("Interrupt present for Interrupt 0 It worked!\n");
        //Clear the interrupt register
        rc = fpga_pci_poke(pci_bar_handle, interrupt_reg_offset , 0x1 << (16 + interrupt_number) );
        fail_on(rc, out, "Unable to write to the fpga !");
    }
    else{
        printf("No interrupt generated- something went wrong.\n");
        rc = 1;
        fail_on(rc, out, "Interrupt generation failed");
    }

out:
    if(fd){
        close(fd);
    }
    return rc;
}

