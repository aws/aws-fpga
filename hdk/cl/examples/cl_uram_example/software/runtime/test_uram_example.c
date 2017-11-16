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
#include <string.h>
#include <unistd.h>

#include <fpga_pci.h>
#include <fpga_mgmt.h>
#include <utils/lcd.h>

/* Constants determined by the CL */
/* a set of register offsets; this CL has only one */
/* these register addresses should match the addresses in */
/* /aws-fpga/hdk/cl/examples/common/cl_common_defines.vh */

#define URAM_REG_ADDR UINT64_C(0x500)

/*
 * pci_vendor_id and pci_device_id values below are Amazon's and avaliable to use for a given FPGA slot. 
 * Users may replace these with their own if allocated to them by PCI SIG
 */
static uint16_t pci_vendor_id = 0x1D0F; /* Amazon PCI Vendor ID */
static uint16_t pci_device_id = 0xF000; /* PCI Device ID preassigned by Amazon for F1 applications */

/* use the stdout logger for printing debug information  */
const struct logger *logger = &logger_stdout;

/* Declaring the local functions */

int uram_example(int slot, int pf_id, int bar_id, uint32_t value);
void help(void);

/* Declating auxilary house keeping functions */
int initialize_log(char* log_name);
int check_afi_ready(int slot);

void help(void)
{
  printf("===== ================================ =====\n");	
  printf("                URAM EXAMPLE\n");
  printf("===== ================================ =====\n");
  printf("This software allows you to write into and read from the URAMs\n");	
  printf("Run the software and follow the instructions:\n");
  printf("\t\tsudo ./uram_example\n");
}

void usage(char* program_name) {
    printf("usage: %s [--slot <slot-id>] [<command> <value>]\n", program_name);
    help();
}

/*** Global Variables ***/
uint32_t nb_iter;
uint32_t glb_value;

int main(int argc, char **argv) {
  int rc;
  int slot_id = 0;
  char command[256];
  uint32_t value;
  int command_set = 0;
  
  // Process command line args
  {
      int i;
      for (i = 1; i < argc; i++) {
          if (!strcmp(argv[i], "--slot")) {
              i++;
              if (i >= argc) {
                  printf("error: missing slot-id\n");
                  usage(argv[0]);
                  return 1;
              }
              sscanf(argv[i], "%d", &slot_id);
          } else if (!command_set) {
              sscanf(argv[i++], "%s", command);
              if (i >= argc) {
                  printf("error: missing <value>\n");
                  usage(argv[0]);
                  return 1;
              }
              sscanf(argv[i], "%x", &value);
              command_set = 1;
          } else {
              printf("error: Invalid arg: %s", argv[i]);
              usage(argv[0]);
              return 1;
          }
      }
  }

  if (!command_set) {
    printf("===== ========================== =====\n");	
    printf("===== Starting with uram_example =====\n");	
    printf("===== ========================== =====\n");	
    printf("Enter your command followed by your 32 bits hexadecimal value (without 0x)\n");	
    printf("Example: find FEEDBABE\n");
    printf("Example: add CAFE4B1D\n");
    printf("Example: del DEADDEAD\n");
    scanf("%s %x", command, &value);
  }
  glb_value = value;
 
  // The 3 MSB are used to encode {find, add, del} when writing to the CL
  // On a read they indicate {find_ok, del_ok, busy}
  value = value & 0x1FFFFFFF;
  if(strcmp("find", command) == 0) {
      value = value | 0x80000000;
  } else {
      if(strcmp("add", command) == 0) {
          value = value | 0x40000000;
      } else {
          if(strcmp("del", command) == 0) {
              // del also sets the find bit.
              value = value | 0xa0000000;
          } else {
              printf("Error: Invalid command: %s. Please choose between find, add or del\n", command);
              return 1;
          }
      }
  }
  
  /* initialize the fpga_pci library so we could have access to FPGA PCIe from this applications */
  rc = fpga_pci_init();
  fail_on(rc, out, "Unable to initialize the fpga_pci library");
  
  rc = check_afi_ready(slot_id);
  fail_on(rc, out, "AFI not ready");
  
  /* Accessing the CL registers via AppPF BAR0, which maps to sh_cl_ocl_ AXI-Lite bus between AWS FPGA Shell and the CL*/

  rc = uram_example(slot_id, FPGA_APP_PF, APP_PF_BAR0, value);
  fail_on(rc, out, "peek-poke example failed");

  return rc;

out:
  return 1;
}

/*
 * An example to attach to an arbitrary slot, pf, and bar with register access.
 */
int uram_example(int slot_id, int pf_id, int bar_id, uint32_t value) {
  int rc;
  int timeout;
  uint32_t find_ok = 0;
  uint32_t find_ko = 0;
  uint32_t busy = 0;
  uint32_t del_info = (value >> 29) & 0x00000001;
  
  /* pci_bar_handle_t is a handler for an address space exposed by one PCI BAR on one of the PCI PFs of the FPGA */
  pci_bar_handle_t pci_bar_handle = PCI_BAR_HANDLE_INIT;

  /* attach to the fpga, with a pci_bar_handle out param
   * To attach to multiple slots or BARs, call this function multiple times,
   * saving the pci_bar_handle to specify which address space to interact with in
   * other API calls.
   * This function accepts the slot_id, physical function, and bar number
   */
  rc = fpga_pci_attach(slot_id, pf_id, bar_id, 0, &pci_bar_handle);
  fail_on(rc, out, "Unable to attach to the AFI on slot id %d", slot_id);
  
  // Write
  printf("Writing 0x%08x\n", value);
  rc = fpga_pci_poke(pci_bar_handle, URAM_REG_ADDR, value);
  fail_on(rc, out, "Unable to write to the fpga !");

  // Wait for the busy status to be cleared
  busy = 1;
  while(busy == 1) {
    if(timeout == 10) {
      printf("Timeout - Something went wrong with the HW. Please do\n");
      printf("\t\tsudo fpga-clear-local-image -S %d\n", slot_id);
      printf("And reload your AFI\n");
      printf("\t\tsudo fpga-load-local-image -S %d -I agfi-xxxxxxxxxxxxxxxxx\n", slot_id);
      return 1;
    }
    if (timeout) {
      printf("Please wait, it may take time ...\n");
    }
    // Wait for the HW to process
    usleep(1000000);
    timeout++;

    // Read
    rc = fpga_pci_peek(pci_bar_handle, URAM_REG_ADDR, &value);
    fail_on(rc, out, "Unable to read read from the fpga !");
    find_ok = value >> 31;
    find_ko = (value >> 30) & 0x00000001;
    busy = (value >> 29) & 0x00000001;
    value = value & 0x1fffffff;
    printf("Read 0x%08x find_ok=%d find_ko=%d, busy=%d\n", value, find_ok, find_ko, busy);
  }
  
  if(find_ok == 1) {
    if(del_info == 1) {
      printf("Deletion OK : The value 0x%x has been deleted successfully\n", glb_value); 
    } else {
      printf("Find OK : The value 0x%x is present in the URAM\n", glb_value); 
    }
  } else {
    if(find_ko == 1) {
      printf("Find KO : The value 0x%x is NOT present in the URAM\n", glb_value); 
    } else {
      printf("The value 0x%x has been added to the URAM successfully\n", glb_value);
    }
  }

    
out:
  /* clean up */
  if (pci_bar_handle >= 0) {
    rc = fpga_pci_detach(pci_bar_handle);
    if (rc) {
      printf("Failure while detaching from the fpga.\n");
    }
  }

  /* if there is an error code, exit with status 1 */
  return (rc != 0 ? 1 : 0);
}


/*
 * check if the corresponding AFI for hello_world is loaded
 */

int check_afi_ready(int slot_id) {
  struct fpga_mgmt_image_info info = {0}; 
  int rc;
 
  /* get local image description, contains status, vendor id, and device id. */
  rc = fpga_mgmt_describe_local_image(slot_id, &info,0);
  fail_on(rc, out, "Unable to get AFI information from slot %d. Are you running as root?",slot_id);
 
  /* check to see if the slot is ready */
  if (info.status != FPGA_STATUS_LOADED) {
    rc = 1;
    fail_on(rc, out, "AFI in Slot %d is not in READY state !", slot_id);
  }
 
  //printf("AFI PCI  Vendor ID: 0x%x, Device ID 0x%x\n",
  //    info.spec.map[FPGA_APP_PF].vendor_id,
  //    info.spec.map[FPGA_APP_PF].device_id);
 
  /* confirm that the AFI that we expect is in fact loaded */
  if (info.spec.map[FPGA_APP_PF].vendor_id != pci_vendor_id ||
      info.spec.map[FPGA_APP_PF].device_id != pci_device_id) {
      printf("AFI does not show expected PCI vendor id and device ID. If the AFI "
             "was just loaded, it might need a rescan. Rescanning now.\n");
 
      rc = fpga_pci_rescan_slot_app_pfs(slot_id);
      fail_on(rc, out, "Unable to update PF for slot %d",slot_id);
      /* get local image description, contains status, vendor id, and device id. */
      rc = fpga_mgmt_describe_local_image(slot_id, &info,0);
      fail_on(rc, out, "Unable to get AFI information from slot %d",slot_id);
 
      printf("AFI PCI  Vendor ID: 0x%x, Device ID 0x%x\n",
          info.spec.map[FPGA_APP_PF].vendor_id,
          info.spec.map[FPGA_APP_PF].device_id);
 
      /* confirm that the AFI that we expect is in fact loaded after rescan */
      if (info.spec.map[FPGA_APP_PF].vendor_id != pci_vendor_id ||
           info.spec.map[FPGA_APP_PF].device_id != pci_device_id) {
          rc = 1;
          fail_on(rc, out, "The PCI vendor id and device of the loaded AFI are not "
                           "the expected values.");
      }
  }
  
  return rc;
 
out:
    return 1;
}
