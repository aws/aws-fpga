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

#include <fpga_pci.h>
#include <fpga_mgmt.h>
#include <utils/lcd.h>

/* Constants determined by the CL */
/* a set of register offsets; this CL has only one */
/* these register addresses should match the addresses in */
/* /aws-fpga/hdk/cl/examples/common/cl_common_defines.vh */

#define HELLO_WORLD_REG_ADDR UINT64_C(0x0)

#define DDR_SH_ADDR UINT64_C(0xE01000000)
#define DDR_B_ADDR UINT64_C(0xD02000000)
#define DDR_A_ADDR UINT64_C(0xC02000000)

#define HELLO_WORLD_REG_ADDR_CONTROL UINT64_C(0x00)
#define HELLO_WORLD_REG_ADDR_STATUS UINT64_C(0x04)

#define HELLO_WORLD_REG_ADDR_SRC_MSB_ADDR UINT64_C(0x1C)
#define HELLO_WORLD_REG_ADDR_DST_MSB_ADDR UINT64_C(0x24)

#define HELLO_WORLD_REG_ADDR_SRC_ADDR UINT64_C(0x18)
#define HELLO_WORLD_REG_ADDR_DST_ADDR UINT64_C(0x20)
#define HELLO_WORLD_REG_ADDR_BYTES UINT64_C(0x28)


/*
 * pci_vendor_id and pci_device_id values below are Amazon's and avaliable to use for a given FPGA slot. 
 * Users may replace these with their own if allocated to them by PCI SIG
 */
static uint16_t pci_vendor_id = 0x1D0F; /* Amazon PCI Vendor ID */
static uint16_t pci_device_id = 0xF000; /* PCI Device ID preassigned by Amazon for F1 applications */


/* use the stdout logger for printing debug information  */
const struct logger *logger = &logger_stdout;

/* Declaring the local functions */

int peek_poke_example(int slot, int pf_id, int bar_id);
int vled_example(int slot);

/* Declating auxilary house keeping functions */
int initialize_log(char* log_name);
int check_afi_ready(int slot);


int main(int argc, char **argv) {
    int rc;
    int slot_id;

    /* initialize the fpga_pci library so we could have access to FPGA PCIe from this applications */
    rc = fpga_pci_init();
    fail_on(rc, out, "Unable to initialize the fpga_pci library");

    /* This demo works with single FPGA slot, we pick slot #0 as it works for both f1.2xl and f1.16xl */

    slot_id = 0;

    rc = check_afi_ready(slot_id);
    fail_on(rc, out, "AFI not ready");
    
    /* Accessing the CL registers via AppPF BAR0, which maps to sh_cl_ocl_ AXI-Lite bus between AWS FPGA Shell and the CL*/

    printf("\n");

    printf("===== AXI CDMA Example =====\n");	
    rc = peek_poke_example(slot_id, FPGA_APP_PF, APP_PF_BAR1);
    fail_on(rc, out, "peek-poke example failed");



  
    return rc;
    
   
out:
    return 1;
}



/*
 * An example to attach to an arbitrary slot, pf, and bar with register access.
 */
int peek_poke_example(int slot_id, int pf_id, int bar_id) {
    int rc;
    int rc_0;
    int rc_4;
    int rc_sda;

    /* pci_bar_handle_t is a handler for an address space exposed by one PCI BAR on one of the PCI PFs of the FPGA */

    pci_bar_handle_t pci_bar_handle = PCI_BAR_HANDLE_INIT;
    pci_bar_handle_t pci_bar_handle_0 = PCI_BAR_HANDLE_INIT;
    pci_bar_handle_t pci_bar_handle_4 = PCI_BAR_HANDLE_INIT;

    pci_bar_handle_t pci_bar_handle_sda = PCI_BAR_HANDLE_INIT;


    /* attach to the fpga, with a pci_bar_handle out param
     * To attach to multiple slots or BARs, call this function multiple times,
     * saving the pci_bar_handle to specify which address space to interact with in
     * other API calls.
     * This function accepts the slot_id, physical function, and bar number
     */
    rc = fpga_pci_attach(slot_id, pf_id, bar_id, 0, &pci_bar_handle);
    fail_on(rc, out, "Unable to attach to the AFI on slot id %d", slot_id);

    rc_0 = fpga_pci_attach(slot_id, pf_id, 0, 0, &pci_bar_handle_0);
    fail_on(rc_0, out, "Unable to attach to the AFI on slot id %d", slot_id);

    rc_4 = fpga_pci_attach(slot_id, pf_id, 4, 0, &pci_bar_handle_4);
    fail_on(rc_4, out, "Unable to attach to the AFI on slot id %d", slot_id);

    rc_sda = fpga_pci_attach(slot_id, FPGA_MGMT_PF, MGMT_PF_BAR4, 0, &pci_bar_handle_sda);
    fail_on(rc_sda, out, "Unable to attach to the AFI on slot id %d", slot_id);

    uint32_t value;


    int loop_var;





    printf("Checking DDR4_A/B/D and DDR4_C(SH) Calibration with SDA-AXI GPIO\n");

    rc_sda = fpga_pci_peek(pci_bar_handle_sda, HELLO_WORLD_REG_ADDR, &value);
    fail_on(rc_sda, out, "Unable to read read from the fpga !");

   while(value != 0x0000000F)
    {
    rc_sda = fpga_pci_peek(pci_bar_handle_sda, HELLO_WORLD_REG_ADDR, &value);
    fail_on(rc_sda, out, "Unable to read read from the fpga !");
    printf("register: 0x%x\n", value);
    }  
    printf("DDR4_A/B/D and DDR4_C(SH) Calibrated! GPIO Input Value: 0x%x\n", value);

    printf("\n");

    printf("Writing for VLED (0xAAAA) with OCL-AXI GPIO\n");

    value = 0x0000AAAA;
    rc_0 = fpga_pci_poke(pci_bar_handle_0, HELLO_WORLD_REG_ADDR, value);
    fail_on(rc_0, out, "Unable to write to the fpga !");




    printf("\n");

    printf("Writing to SH_DDR Source Buffer 1KB\n");

    for ( loop_var = 0; loop_var < 256; loop_var++ ) {
       rc_4 = fpga_pci_poke(pci_bar_handle_4, (DDR_SH_ADDR + loop_var*4), loop_var);
       fail_on(rc_4, out, "Unable to write to the fpga !"); 
            
    }
    printf("Finished writing to SH_DDR Source Buffer\n");

    printf("\n");
    printf("Setting Up CDMA Transfers with USR-AXI CDMA AXI4 Lite Registers\n");

    value = 0x01000000;
    rc = fpga_pci_poke(pci_bar_handle, HELLO_WORLD_REG_ADDR_SRC_ADDR, value);
    fail_on(rc, out, "Unable to write to the fpga !");  

    value = 0x0000000E;
    rc = fpga_pci_poke(pci_bar_handle, HELLO_WORLD_REG_ADDR_SRC_MSB_ADDR, value);
    fail_on(rc, out, "Unable to write to the fpga !");  
    
    value = 0x02000000;
    rc = fpga_pci_poke(pci_bar_handle, HELLO_WORLD_REG_ADDR_DST_ADDR, value);
    fail_on(rc, out, "Unable to write to the fpga !");

    value = 0x0000000D;
    rc = fpga_pci_poke(pci_bar_handle, HELLO_WORLD_REG_ADDR_DST_MSB_ADDR, value);
    fail_on(rc, out, "Unable to write to the fpga !");  
    
    value = 0x00000400;
    rc = fpga_pci_poke(pci_bar_handle, HELLO_WORLD_REG_ADDR_BYTES, value);
    fail_on(rc, out, "Unable to write to the fpga !");
    printf("Executing CDMA Transfers on DDR4_SH and polling status register\n");
    printf("\n");

    rc = fpga_pci_peek(pci_bar_handle, HELLO_WORLD_REG_ADDR_STATUS, &value);
    fail_on(rc, out, "Unable to read read from the fpga !");
    
    while(value != 0x00001002)
    {
    rc = fpga_pci_peek(pci_bar_handle, HELLO_WORLD_REG_ADDR_STATUS, &value);
    fail_on(rc, out, "Unable to read read from the fpga !");
    }
    printf("CDMA Transfer Complete!\n");
    printf("AXI CDMA Status Register Value: 0x%x\n", value);



    printf("\n");
    printf("Reading and verifying DDR_B Dst Buffer 1KB\n");

    for ( loop_var = 0; loop_var < 256; loop_var++ ) {
 
       rc_4 = fpga_pci_peek(pci_bar_handle_4, (DDR_B_ADDR + loop_var*4), &value);
       fail_on(rc_4, out, "Unable to read read from the fpga !");
       //printf("register: 0x%x\n", value);

       if (value != loop_var)
    	{
          printf("Data mismatch!");
    	}
            
    }

    printf("\n");
    printf("CDMA Transfer Successful!\n");


out:
    /* clean up */
    if (pci_bar_handle >= 0) {
        rc = fpga_pci_detach(pci_bar_handle);
        if (rc) {
            printf("Failure while detaching from the fpga.\n");
        }
    }

    if (pci_bar_handle_0 >= 0) {
        rc_0 = fpga_pci_detach(pci_bar_handle_0);
        if (rc_0) {
            printf("Failure while detaching from the fpga.\n");
        }
    }

    if (pci_bar_handle_4 >= 0) {
        rc_4 = fpga_pci_detach(pci_bar_handle_4);
        if (rc_4) {
            printf("Failure while detaching from the fpga.\n");
        }
    }


    if (pci_bar_handle_sda >= 0) {
        rc_sda = fpga_pci_detach(pci_bar_handle_sda);
        if (rc_sda) {
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

    printf("AFI PCI  Vendor ID: 0x%x, Device ID 0x%x\n",
        info.spec.map[FPGA_APP_PF].vendor_id,
        info.spec.map[FPGA_APP_PF].device_id);

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
