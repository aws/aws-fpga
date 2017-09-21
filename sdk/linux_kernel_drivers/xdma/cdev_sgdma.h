/*******************************************************************************
 *
 * Xilinx XDMA IP Core Linux Driver
 *
 * Copyright(c) Sidebranch.
 * Copyright(c) Xilinx, Inc.
 *
 * Karen Xie <karen.xie@xilinx.com>
 * Leon Woestenberg <leon@sidebranch.com>
 *
 ******************************************************************************/
#ifndef _XDMA_IOCALLS_POSIX_H_
#define _XDMA_IOCALLS_POSIX_H_

#include <linux/ioctl.h>


#define IOCTL_XDMA_PERF_V1 (1)
#define XDMA_ADDRMODE_MEMORY (0)
#define XDMA_ADDRMODE_FIXED (1)

/*
 * S means "Set" through a ptr,
 * T means "Tell" directly with the argument value
 * G means "Get": reply by setting through a pointer
 * Q means "Query": response is on the return value
 * X means "eXchange": switch G and S atomically
 * H means "sHift": switch T and Q atomically
 *
 * _IO(type,nr)		    no arguments
 * _IOR(type,nr,datatype)   read data from driver
 * _IOW(type,nr.datatype)   write data to driver
 * _IORW(type,nr,datatype)  read/write data
 *
 * _IOC_DIR(nr)		    returns direction
 * _IOC_TYPE(nr)	    returns magic
 * _IOC_NR(nr)		    returns number
 * _IOC_SIZE(nr)	    returns size
 */

struct xdma_performance_ioctl
{
        /* IOCTL_XDMA_IOCTL_Vx */
        uint32_t version;
        uint32_t transfer_size;
        /* measurement */
        uint32_t stopped;
        uint32_t iterations;
        uint64_t clock_cycle_count;
        uint64_t data_cycle_count;
        uint64_t pending_count;
};



/* IOCTL codes */

#define IOCTL_XDMA_PERF_START   _IOW('q', 1, struct xdma_performance_ioctl *)
#define IOCTL_XDMA_PERF_STOP    _IOW('q', 2, struct xdma_performance_ioctl *)
#define IOCTL_XDMA_PERF_GET     _IOR('q', 3, struct xdma_performance_ioctl *)
#define IOCTL_XDMA_ADDRMODE_SET _IOW('q', 4, int)
#define IOCTL_XDMA_ADDRMODE_GET _IOR('q', 5, int)
#define IOCTL_XDMA_ALIGN_GET    _IOR('q', 6, int)

#endif /* _XDMA_IOCALLS_POSIX_H_ */
