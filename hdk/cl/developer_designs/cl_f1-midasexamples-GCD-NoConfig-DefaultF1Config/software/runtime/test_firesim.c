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
#include <assert.h>
#include <string.h>

#include <sys/types.h>
#include <sys/stat.h>
#include <fcntl.h>

#ifdef SV_TEST
#ifndef VIVADO_SIM
#include "svdpi.h"
#endif
#endif

#include "common_dma.h"

/* this is the connector from the FireSim driver to the XSim simulation.
 * this gets built into an XSim simulator including everything that goes
 * on the FPGA. the FireSim driver is then built and communicates via pipes
 * to this xsim simulation. */

void test_main(uint32_t *exit_code) {

    //The statements within SCOPE ifdef below are needed for HW/SW co-simulation with VCS
    #ifdef SCOPE
      svScope scope;
      scope = svGetScopeFromName("tb");
      svSetScope(scope);
    #endif

    int slot_id = 0;
    int rc;

    /* initialize the fpga_pci library so we could have access to FPGA PCIe from this applications */
    rc = fpga_pci_init();

    int bar_id = APP_PF_BAR0;
    int pf_id = FPGA_APP_PF;

    /* pci_bar_handle_t is a handler for an address space exposed by one PCI BAR on one of the PCI PFs of the FPGA */
    // unused in SV_TESTs
    pci_bar_handle_t pci_bar_handle = PCI_BAR_HANDLE_INIT;

    /* setup pipes */
    char * driver_to_xsim = "/tmp/driver_to_xsim";
    char * xsim_to_driver = "/tmp/xsim_to_driver";
    mkfifo(xsim_to_driver, 0666);
    printf("opening driver_to_xsim\n");
    int driver_to_xsim_fd = open(driver_to_xsim, O_RDONLY);
    printf("opening xsim_to_driver\n"); 
    int xsim_to_driver_fd = open(xsim_to_driver, O_WRONLY);

    char buf[8];
    while(1) {
        int readbytes = read(driver_to_xsim_fd, buf, 8);
        if (readbytes != 8) {
            if (readbytes != 0) {
                printf("only read %d bytes\n", readbytes);
                exit(1);
            }
            continue;
        }
        uint64_t cmd = *((uint64_t*)buf);
        if (cmd >> 63) {
            //write
            uint32_t addr = (cmd >> 32) & 0x7FFFFFFF;
            uint32_t data = cmd & 0xFFFFFFFF;
            fpga_pci_poke(pci_bar_handle, addr, data);
        } else {
            // read
            uint32_t addr = cmd & 0xFFFFFFFF;
            uint32_t dat;
            fpga_pci_peek(pci_bar_handle, addr, &dat);
            uint64_t ret = dat;
            write(xsim_to_driver_fd, (char*)&ret, 8);
        }
    }
    *exit_code = 0;
}
