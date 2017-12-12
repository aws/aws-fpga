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

int dma_example(int slot_id);
int interrupt_example(int slot_id, int interrupt_number);
int axi_mstr_example(int slot_id);
int axi_mstr_ddr_access(int slot_id, pci_bar_handle_t pci_bar_handle, uint32_t ddr_hi_addr, uint32_t ddr_lo_addr, uint32_t  ddr_data);

void usage(const char* program_name) {
    printf("usage: %s [--slot <slot>]\n", program_name);
}

int main(int argc, char **argv) {
    int rc;
    int slot_id = 0;
    int interrupt_number;

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

    rc = dma_example(slot_id);
    fail_on(rc, out, "DMA example failed");

    interrupt_number = 0;

    rc = interrupt_example(slot_id, interrupt_number);
    fail_on(rc, out, "Interrupt example failed");

    rc = axi_mstr_example(slot_id);
    fail_on(rc, out, "AXI Master example failed");

out:
    return rc;
}

static int
check_slot_config(int slot_id)
{
    int rc;
    struct fpga_mgmt_image_info info = {0};

    /* get local image description, contains status, vendor id, and device id */
    rc = fpga_mgmt_describe_local_image(slot_id, &info, 0);
    fail_on(rc, out, "Unable to get local image information. Are you running as root?");

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
               "Note that rescanning can change which device file in /dev/ a FPGA will map to.\n"
               "To remove and re-add your edma driver and reset the device file mappings, run\n"
               "`sudo rmmod edma-drv && sudo insmod <aws-fpga>/sdk/linux_kernel_drivers/edma/edma-drv.ko`\n",
               slot_id);
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

int dma_example(int slot_id) {
    int fd, rc;
    char device_file_name[256];
    char *write_buffer, *read_buffer;
    static const size_t buffer_size = 128;
    int channel=0;

    read_buffer = NULL;
    write_buffer = NULL;
    fd = -1;

    rc = sprintf(device_file_name, "/dev/edma%i_queue_0", slot_id);
    fail_on((rc = (rc < 0)? 1:0), out, "Unable to format device file name.");
    printf("device_file_name=%s\n", device_file_name);

    /* make sure the AFI is loaded and ready */
    rc = check_slot_config(slot_id);
    fail_on(rc, out, "slot config is not correct");

    fd = open(device_file_name, O_RDWR);
    if(fd<0){
        printf("Cannot open device file %s.\nMaybe the EDMA "
               "driver isn't installed, isn't modified to attach to the PCI ID of "
               "your CL, or you're using a device file that doesn't exist?\n"
               "See the edma_install manual at <aws-fpga>/sdk/linux_kernel_drivers/edma/edma_install.md\n"
               "Remember that rescanning your FPGA can change the device file.\n"
               "To remove and re-add your edma driver and reset the device file mappings, run\n"
               "`sudo rmmod edma-drv && sudo insmod <aws-fpga>/sdk/linux_kernel_drivers/edma/edma-drv.ko`\n",
               device_file_name);
        fail_on((rc = (fd < 0)? 1:0), out, "unable to open DMA queue. ");
    }

    write_buffer = (char *)malloc(buffer_size);
    read_buffer = (char *)malloc(buffer_size);
    if (write_buffer == NULL || read_buffer == NULL) {
        rc = ENOMEM;
        goto out;
    }

    rand_string(write_buffer, buffer_size);

    for (channel=0; channel < 4; channel++) {
        size_t write_offset = 0;
        while (write_offset < buffer_size) {
            if (write_offset != 0) {
                printf("Partial write by driver, trying again with remainder of buffer (%lu bytes)\n",
                    buffer_size - write_offset);
            }
            rc = pwrite(fd,
                write_buffer + write_offset,
                buffer_size - write_offset,
                0x10000000 + channel*MEM_16G + write_offset);
            if (rc < 0) {
                fail_on((rc = (rc < 0)? errno:0), out, "call to pwrite failed.");
            }
            write_offset += rc;
        }
        rc = 0;
    }

    /* fsync() will make sure the write made it to the target buffer 
     * before read is done
     */

    rc = fsync(fd);
    fail_on((rc = (rc < 0)? errno:0), out, "call to fsync failed.");

    for (channel=0; channel < 4; channel++) {
        size_t read_offset = 0;
        while (read_offset < buffer_size) {
            if (read_offset != 0) {
                printf("Partial read by driver, trying again with remainder of buffer (%lu bytes)\n",
                    buffer_size - read_offset);
            }
            rc = pread(fd,
                read_buffer + read_offset,
                buffer_size - read_offset,
                0x10000000 + channel*MEM_16G + read_offset);
            if (rc < 0) {
                fail_on((rc = (rc < 0)? errno:0), out, "call to pread failed.");
            }
            read_offset += rc;
        }
        rc = 0;

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
         
            rc = 1; 
            fail_on(rc, out, "Data read from DMA did not match data written with DMA. Was there an fsync() between the read and write?");
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

int interrupt_example(int slot_id, int interrupt_number){
    pci_bar_handle_t pci_bar_handle = PCI_BAR_HANDLE_INIT;
    struct pollfd fds[1];
    uint32_t fd, rd,  read_data;
    char event_file_name[256];
    int rc = 0;
    int poll_timeout = 1000;
    int num_fds = 1;
    int pf_id = 0;
    int bar_id = 0;
    int fpga_attach_flags = 0;
    int poll_limit = 20;
    uint32_t interrupt_reg_offset = 0xd00;

  
    rc = sprintf(event_file_name, "/dev/fpga%i_event%i", slot_id, interrupt_number);
    fail_on((rc = (rc < 0)? 1:0), out, "Unable to format event file name.");

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

    printf("Triggering MSI-X Interrupt 0\n");
    rc = fpga_pci_poke(pci_bar_handle, interrupt_reg_offset , 1 << interrupt_number);
    fail_on(rc, out, "Unable to write to the fpga !");

    // Poll checks whether an interrupt was generated, and also clears the interrupt in the device file, so we can detect future interrupts
    rd = poll(fds, num_fds, poll_timeout);
    if( rd >0 && fds[0].revents & POLLIN){
        // Check how many interrupts were generated
        printf("Interrupt present for Interrupt %i. It worked!\n", interrupt_number);
        //Clear the interrupt register
        rc = fpga_pci_poke(pci_bar_handle, interrupt_reg_offset , 0x1 << (16 + interrupt_number) );
        fail_on(rc, out, "Unable to write to the fpga !");
    }
    else{
        printf("No interrupt generated- something went wrong.\n");
        rc = 1;
        fail_on(rc, out, "Interrupt generation failed");
    }
    close(fd);

    //Clear the interrupt register
    do{
        // In this CL, a successful interrupt is indicated by the CL setting bit <interrupt_number + 16>
        // of the interrupt register. Here we check that bit is set and write 1 to it to clear.
        rc = fpga_pci_peek(pci_bar_handle, interrupt_reg_offset, &read_data);
        fail_on(rc, out, "Unable to read from the fpga !");
        read_data = read_data & (1 << (interrupt_number + 16));

        rc = fpga_pci_poke(pci_bar_handle, interrupt_reg_offset , read_data );
        fail_on(rc, out, "Unable to write to the fpga !");

        poll_limit--;
    } while (!read_data && poll_limit > 0);

out:
    if(fd){
        close(fd);
    }
    return rc;
}

int axi_mstr_example(int slot_id) {
    int rc;
    pci_bar_handle_t pci_bar_handle = PCI_BAR_HANDLE_INIT;
    int pf_id = 0;
    int bar_id = 0;
    int fpga_attach_flags = 0;
    uint32_t ddr_hi_addr, ddr_lo_addr, ddr_data;

    rc = fpga_pci_attach(slot_id, pf_id, bar_id, fpga_attach_flags, &pci_bar_handle);
    fail_on(rc, out, "Unable to attach to the AFI on slot id %d", slot_id);

    printf("Starting AXI Master to DDR test \n");

    /* DDR A Access */
    ddr_hi_addr = 0x00000001;
    ddr_lo_addr = 0xA021F700;
    ddr_data    = 0xA5A61A2A;

    rc = axi_mstr_ddr_access(slot_id, pci_bar_handle, ddr_hi_addr, ddr_lo_addr, ddr_data);
    fail_on(rc, out, "Unable to access DDR A.");

    /* DDR B Access */
    ddr_hi_addr = 0x00000004;
    ddr_lo_addr = 0x529C8400;
    ddr_data    = 0x1B80C948;

    rc = axi_mstr_ddr_access(slot_id, pci_bar_handle, ddr_hi_addr, ddr_lo_addr, ddr_data);
    fail_on(rc, out, "Unable to access DDR B.");

    /* DDR C Access */
    ddr_hi_addr = 0x00000008;
    ddr_lo_addr = 0x2078BC00;
    ddr_data    = 0x8BD18801;

    rc = axi_mstr_ddr_access(slot_id, pci_bar_handle, ddr_hi_addr, ddr_lo_addr, ddr_data);
    fail_on(rc, out, "Unable to access DDR C.");

    /* DDR D Access */
    ddr_hi_addr = 0x0000000C;
    ddr_lo_addr = 0xD0167700;
    ddr_data    = 0xCA02183D;

    rc = axi_mstr_ddr_access(slot_id, pci_bar_handle, ddr_hi_addr, ddr_lo_addr, ddr_data);
    fail_on(rc, out, "Unable to access DDR D.");

out:
    return rc;
}

/* Helper function for accessing DDR controllers via AXI Master block */
int axi_mstr_ddr_access(int slot_id, pci_bar_handle_t pci_bar_handle, uint32_t ddr_hi_addr, uint32_t ddr_lo_addr, uint32_t  ddr_data) {
    int rc;
    static uint32_t ccr_offset  = 0x500;
    static uint32_t cahr_offset = 0x504;
    static uint32_t calr_offset = 0x508;
    static uint32_t cwdr_offset = 0x50C;
    static uint32_t crdr_offset = 0x510;
    uint32_t read_data;
    int poll_limit = 20;

    /* Issue AXI Master Write Command */
    rc = fpga_pci_poke(pci_bar_handle, cahr_offset, ddr_hi_addr);
    fail_on(rc, out, "Unable to write to AXI Master CAHR register!");
    rc = fpga_pci_poke(pci_bar_handle, calr_offset, ddr_lo_addr);
    fail_on(rc, out, "Unable to write to AXI Master CALR register!");
    rc = fpga_pci_poke(pci_bar_handle, cwdr_offset, ddr_data);
    fail_on(rc, out, "Unable to write to AXI Master CWDR register!");
    rc = fpga_pci_poke(pci_bar_handle, ccr_offset, 0x1);
    fail_on(rc, out, "Unable to write to AXI Master CCR register!");

    /* Poll for done */
    do{
        // Read the CCR until the done bit is set
        rc = fpga_pci_peek(pci_bar_handle, ccr_offset, &read_data);
        fail_on(rc, out, "Unable to read AXI Master CCR from the fpga !");
        read_data = read_data & (0x2);
        poll_limit--;
    } while (!read_data && poll_limit > 0);
    fail_on((rc = !read_data), out, "AXI Master write to DDR did not complete. Done bit not set in CCR.");

    /* Issue AXI Master Read Command */
    rc = fpga_pci_poke(pci_bar_handle, ccr_offset, 0x5);
    fail_on(rc, out, "Unable to write to AXI Master CCR register!");

    /* Poll for done */
    poll_limit = 20;
    do{
        // Read the CCR until the done bit is set
        rc = fpga_pci_peek(pci_bar_handle, ccr_offset, &read_data);
        fail_on(rc, out, "Unable to read AXI Master CCR from the fpga !");
        read_data = read_data & (0x2);
        poll_limit--;
    } while (!read_data && poll_limit > 0);
    fail_on((rc = !read_data), out, "AXI Master read from DDR did not complete. Done bit not set in CCR.");

    /* Compare Read/Write Data */
    // Read the CRDR for read data
    rc = fpga_pci_peek(pci_bar_handle, crdr_offset, &read_data);
    fail_on(rc, out, "Unable to read AXI Master CRDR from the fpga !");
    if(read_data == ddr_data) {
        rc = 0;
        printf("Resulting value at address 0x%x%x matched expected value 0x%x. It worked!\n", ddr_hi_addr, ddr_lo_addr, ddr_data);
    }
    else{
        rc = 1;
        fail_on(rc, out, "Resulting value, 0x%x did not match expected value 0x%x at address 0x%x%x. Something didn't work.\n", read_data, ddr_data, ddr_hi_addr, ddr_lo_addr);
    }

out:
    return rc;
}
