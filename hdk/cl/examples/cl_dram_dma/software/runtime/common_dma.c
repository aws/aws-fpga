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
#include <stdint.h>
#include <stdbool.h>
#include <stdarg.h>

#include <utils/sh_dpi_tasks.h>

#include "common_dma.h"

static uint16_t pci_vendor_id = 0x1D0F; /* Amazon PCI Vendor ID */
static uint16_t pci_device_id = 0xF001;

void usage(const char* program_name) {
    printf("usage: %s [--slot <slot>]\n", program_name);
}

/* helper function to initialize a buffer that would be written to the FPGA later */
void
rand_string(char *str, size_t size)
{
    static const char charset[] =
        "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRTSUVWXYZ1234567890";
    static bool seeded = false;
    int i;

    if (!seeded) {
        srand(time(NULL));
        seeded = true;
    }

    for(i = 0; i < size; ++i) {
        unsigned int key = rand() % (sizeof charset - 1);
        str[i] = charset[key];
    }

    str[size-1] = '\0';
}

#ifndef SV_TEST

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

int open_dma_queue(int slot_id)
{
    int fd, rc;
    char device_file_name[256];

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
out:
    return fd;
}

#endif

int fpga_driver_write_buffer_to_cl(int slot_id, int channel, int fd, size_t buffer_size, size_t address){
    int rc;
    size_t write_offset =0;

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
out:
    return rc;
}

int fpga_driver_read_cl_to_buffer(int slot_id, int channel, int fd, size_t buffer_size, size_t address){
   size_t read_offset =0;
   int rc;
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
out:
    return rc;
}

void fpga_read_cl_to_buffer(int slot_id, int channel, int fd, size_t buffer_size, size_t address) {
#ifdef SV_TEST
  sv_fpga_start_cl_to_buffer(slot_id, channel, buffer_size, address);
#else
  fpga_driver_read_cl_to_buffer(slot_id, channel, fd, buffer_size, address);
#endif
  dma_memcmp(buffer_size);
}

void fpga_write_buffer_to_cl(int slot_id, int channel, int fd, size_t buffer_size, size_t address){
#ifdef SV_TEST
  sv_fpga_start_buffer_to_cl(slot_id, channel, buffer_size, write_buffer, address);
#else
  fpga_driver_write_buffer_to_cl(slot_id, channel, fd, buffer_size, address);
#endif
}

int dma_memcmp (size_t buffer_size) {
   int rc = 0;
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
#ifndef SV_TEST
      rc = 1; 
      fail_on(rc, out, "Data read from DMA did not match data written with DMA. Was there an fsync() between the read and write?");
#else
      error_count++;
#endif
   }
out:
   return rc;
}

#ifdef SV_TEST

int send_rdbuf_to_c(char* rd_buf)

{
// Vivado does not support svGetScopeFromName
  #ifndef VIVADO_SIM
    svScope scope;
    scope = svGetScopeFromName("tb");
    svSetScope(scope);
  #endif

   int i;

   //For Questa simulator the first 8 bytes are not transmitted correctly, so the buffer is transferred with 8 extra bytes and those bytes are removed here. Made this default for all the simulators.
   for (i = 0; i < buffer_size; ++i) {
      read_buffer[i] = rd_buf[i+8];
   }

   //end of line character is not transferered correctly. So assign that here. 
   read_buffer[buffer_size-1] = '\0';

   return 0;

} 

#endif



