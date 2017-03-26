/*
 * Copyright 2015-2016 Amazon.com, Inc. or its affiliates. All Rights Reserved.
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
#include <stdint.h>
#include <stdbool.h>

#include <fpga_pci.h>
#include <fpga_mgmt.h>
#include <utils/lcd.h>

/* Constants determined by the CL */
/* a set of register offsets; this CL has only one */
/* these register addresses should match the addresses in */
/* /aws-fpga/hdk/cl/examples/common/cl_common_defines.vh */

#define HELLO_WORLD_REG_ADDR UINT64_C(0x500)
#define VLED_REG_ADDR	UINT64_C(0x504)

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

    /* setup logging to print to stdout */
    /* This code is provided to help debug the software and not required by AWS FPGA */
    initialize_log("test_hello_world");

    /* initialize the fpga_pci library so we could have access to FPGA PCIe from this applications */
    rc = fpga_pci_init();
    fail_on(rc, out, "Unable to initialize the fpga_pci library");

    /* This demo works with single FPGA slot, we pick slot #0 as it works for both f1.2xl and f1.16xl */

    slot_id = 0;

    check_afi_ready(slot_id);
    
    /* Accessing the CL registers via AppPF BAR0, which maps to sh_cl_ocl_ AXI-Lite bus between AWS FPGA Shell and the CL*/

    printf("Developers are encourged to modify the Virtual DIP Switch by calling the linux shell command to demonstrate how AWS FPGA Virtual DIP switches can be used to change a CustomLogic functionality:\n");
    printf("$ fpga-set-virtual-dip-switch -S (slot-id) -D (16 digit setting)\n\n");

    printf("===== Starting with peek_poke_example =====\n");	
    rc = peek_poke_example(slot_id, FPGA_APP_PF, APP_PF_BAR0);
    if (rc)
	return rc;

    printf("===== Starting with vLED example =====\n");
    rc = vled_example(slot_id); 
  
    return rc;
    
   
out:
    return 1;
}



/*
 * An example to attach to an arbitrary slot, pf, and bar with register access.
 */
int peek_poke_example(int slot_id, int pf_id, int bar_id) {
    int rc;
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

    /* write a value into the mapped address space */
    uint32_t value = 0xefbeadde;
    rc = fpga_pci_poke(pci_bar_handle, HELLO_WORLD_REG_ADDR, value);
    fail_on(rc, out, "Unable to write to the fpga !");

    /* read it back and print it out; you should expect the byte order to be
     * reversed (That's what this CL does) */
    rc = fpga_pci_peek(pci_bar_handle, HELLO_WORLD_REG_ADDR, &value);
    fail_on(rc, out, "Unable to read read from the fpga !");
    printf("register: 0x%x\n", value);

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

int vled_example(int slot_id) {
   int rc;
   pci_bar_handle_t pci_bar_handle = PCI_BAR_HANDLE_INIT;

    /* attach to the fpga, with a pci_bar_handle out param
     * To attach to multiple slots or BARs, call this function multiple times,
     * saving the pci_bar_handle to specify which address space to interact with in
     * other API calls.
     * This function accepts the slot_id, physical function, and bar number
     * for the specific Virtual LED register in this CL design, it is 
     * mapped behind the ocl_ bus, which maps to BAR0 in the FPGA application PF
     */
    rc = fpga_pci_attach(slot_id, FPGA_APP_PF, APP_PF_BAR0, 0, &pci_bar_handle);
    fail_on(rc, out, "Unable to attach to the AFI on slot id %d", slot_id);

    /* write this value to the led register
     * The developer can later read the Virtual LED through
     * linux shell command: $ fpga-get-virtual-led 
     */

    uint32_t led_reg_value = 0x5555;
    rc = fpga_pci_poke(pci_bar_handle, VLED_REG_ADDR, led_reg_value);
    fail_on(rc, out, "Unable to write to the fpga !");

    printf("Wrote 0x%x to the LED trigger register in Hello World CL\n", led_reg_value);
    printf("Please call AWS FPGA tool: $ fpga-get-virtual-led\n");
    printf("to see what LED is being set on the CL to shell cl_shell_vled interface\n");

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
    fail_on(rc, out, "Unable to get AFI information from slot %d",slot_id);

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
        rc = 1;
        fail_on(rc, out, "The PCI vendor id and device of the loaded AFI are not "
                         "the expected values.");
    }
    
    return rc;

out:
    return 1;
}


/*
 * Auxilary functin to set up a logger for printing
 * in this case, it redirect log to stdout
 */

int initialize_log(char* log_name) {
    int rc;
    /* setup logging to print to stdout */
    /* This code is provided to help debug the software and not required by AWS FPGA */
    rc = log_init(log_name);
    fail_on(rc, out, "Unable to initialize the log.");
    rc = log_attach(logger, NULL, 0);
    fail_on(rc, out, "%s", "Unable to attach to the log.");

    return rc;

out:
    return 1;
}
