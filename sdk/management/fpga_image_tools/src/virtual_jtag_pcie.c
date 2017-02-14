/*
 * PCIe xvcserver
 *
 */

#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <fcntl.h>
#include <sys/mman.h>
#include <assert.h>

#include <unistd.h>

#include <sys/time.h>


#include <sys/ioctl.h>
#include <errno.h>




int open_port(uint32_t slot_id) {
   
/* attach to slot S */

   return (0);
}

void close_port(void* jtag_pci_bar) {
/* detach jtag_pci_bar */
}

void set_tck(void *client_data, unsigned long nsperiod, unsigned long *result) {
    *result = nsperiod;
}

void shift_tms_tdi(
    void *client_data,
    unsigned long bitcount,
    unsigned char *tms_buf,
    unsigned char *tdi_buf,
    unsigned char *tdo_buf) {

    int ret = 0;
    struct timeval stop, start;

    if (verbose) {
        gettimeofday(&start, NULL);
    }

    /* struct xil_xvc_ioc xvc_ioc;

    xvc_ioc.opcode = 0x01; // 0x01 for normal, 0x02 for bypass
    xvc_ioc.length = bitcount;
    xvc_ioc.tms_buf = tms_buf;
    xvc_ioc.tdi_buf = tdi_buf;
    xvc_ioc.tdo_buf = tdo_buf;

    int ret = ioctl(pcie->fd, XDMA_IOCXVC, &xvc_ioc); */
    
    if (ret < 0)
    {
        int errsv = errno;
        printf("IOC Error %d\n", errsv);
    }


    if (verbose) {
        gettimeofday(&stop, NULL);
        printf("IOC shift internal took %lu u-seconds with %lu bits. Return value %d\n", stop.tv_usec - start.tv_usec, bitcount, ret);
    }
}

