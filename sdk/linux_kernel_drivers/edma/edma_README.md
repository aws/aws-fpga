# Using AWS EDMA in C/C++ application

## Table of Content

1. [Overview](#overview)
2. [Quick Example](#quickExample)
3. [Detailed Description](#detailed)
4. [Frequently Asked Questions](#faqs)

# Overview

Amazon Elastic-DMA (EDMA) Driver is provided as an option transfer data between the FPGA and the Instance's CPU memory.

Amazon EDMA driver objectives:
1. Open source driver
2. Easy to install and use, and does not require driver development expertise to use
3. Support multiple FPGAs per instance, and multiple queues per FPGA
4. Expandable by developers
5. High-performance multi-queue interface, to lower CPU overhead.

EDMA driver source code is distributed with AWS FPGA HDK and SDK.

[EDMA Installation Guide](./edma_install.md) provides detailed guidelines how to compile, install and trouble shoot EDMA instalation.

** NOTE: Usage of EDMA is not mandatory, and AWS FPGA provides memory-mapped PCIe address space for direct communication between CPU and FPGA. **

For a complete description of the various CPU to FPGA communication options and various options available for the programmer, please review the [Programmers' View](https://github.com/aws/aws-fpga/blob/master/hdk/docs/Programmers_View.md).


# Quick Example

Before diving into the detail specification of the EDMA, here’s a short intuitive example how the developer could use the EDMA in a process:

The Program below will uses standard linux system call open() to  create a file descriptor (fd), mapping to a pair of EDMA queues (one for read and one for write).


```
#include <stdio.h>
#include <fcntl.h>
#include <errno.h>
#include <unistd.h>

#define BUF_SIZE    256
#define OFFSET_IN_FPGA_DRAM 1024

int main(){
    char* srcBuf;
    char* dstBuf;
    int fd;
    int i;
    int ret;
    
    srcBuf = malloc(BUF_SIZE);
    dstBuf = malloc(BUF_SIZE);
    
    /* Initialize srcBuf */
    for(i=0;i<BUF_SIZE;i++)
        srcBuf[i]=(char) (i%256);
        
    if((fd = open("/dev/edma0_queue0",O_RDWR)) == -1)
    {
              perror("open failed with errno %d\n",errno);
    }
    
    /* Write the entire source buffer to offset OFFSET_IN_FPGA_DRAM */
    
    ret = pwrite(fd , srcBuf, BUF_SIZE, OFFSET_IN_FPGA_DRAM);
    
    if( ret < 0)
    {
              perror("write failed with errno %d\n",errno);
    }
    
    printf("Tried to write %u bytes, succeeded in writing %u bytes\n", BUF_SIZE, ret);
    
    /* ensure the write made it to the Shell/CL interface */
    fsync(fd);
    
    ret = pread(fd, dstBuf, BUF_SIZE, OFFSET_IN_FPGA_DRAM);
    
    if(ret < 0)
    {
              perror("read failed with errno %d\n",errno);
    }

    printf("Tried reading %u byte, succeeded in read %u bytes\n", BUF_SIZE,ret);
    
    if(close(fd) < 0)
    {
              perror("close failed with errno %d\n",errno);
    }

    printf("Data read is %s\n", dstBuf);

} 
```

# Detailed Description

## Using file operations to perform DMA

The EDMA can be used in any developer program (running in user space) using simple device operations following standard linux/posix system calls.  Each EDMA queue is has a `/dev/edmaX_queueN` filename, hence it support linux character device APIs.

As DMA channel/queue would get a file-descriptors in the userspace applications, and data movement application (like read() and write() ) would use a buffer pointer _(void*)_ to the instance CPU memory, while using file offset _(off\_t)_ to present the write-to/read-from address in the FPGA.

**NOTE: In EC2 F1 instances, the file offset represent the write-to/read-from address in the FPGA relative to AppPF BAR4 128GiB address space. The DMA can not access any other PCIe BAR space.** Refer to [FPGA PCIe Memory Address Map](aws-fpga/hdk/docs/AWS_Fpga_Pcie_Memory_Map.md).


## Initialization and tear down API

Using the standard:
`int open(const char \*pathname, int flags);`

Where file name is one of the `/dev/edmaX_queueY` (X is the FPGA slot, Y is the specific queue), with the only flags recommended is `O_RDWR`, **and all other flags will be ignored.**  

Multiple threads or processes can open the same file, and it is the developer's responsibility to ensure coordination/serialization, if required, using `lock` system call.

A corresponding `close()` is used to release the DMA queue.  The `close()` call will block until all other pending calls (like read or write) finish, any call to the file-descriptor following close() will return error. If `close()` waits for more than 3seconds and all other pending calls did not finish, it will force a close, and the FPGA and its edma driver will be in unknown state.


## Write APIs

The two standard linux/posix APIs for write are listed below:

***ssize_t write(int fd, void\* buf, size_t count)*** 

***ssize_t pwrite(int fd, void\* buf, size_t count, off_t offset)***   (Recommended, see [explaination](#seek))

The file-descriptor (fd) must have been opened successfully before calling write()/pwrite().

`buf`, the poiter to the source buffer to write to FPGA can have arbiterary size and alignment.

EDMA driver is responsible on mapping the `buf` memory range to list of physical addresses that the hardware DMA can use. 

EDMA driver will take care of copying and/or pinning the user-space `buf` memory, and the developer doesn't need to worry about it.

### Writes are semi-asynchronous

To improve write performance, and allow the application to write small messages and increase concurrency, the `write()`/`pwrite()` **may** copy the write data to an intermediate transmit buffer in the kernel, that will later be drained to the FPGA.

** Developers' who want to guarantee that the writen data has reached the CL (Custom Logic) portion of the FPGA, must call `fsync()` after `write()`/`pwrite()`.**

//TBD - talk about return error values

## Read APIs 

***ssize_t read(int fd, void\* buf, size_t count)*** 

***ssize_t pread(int fd, void\* buf, size_t count, off_t offset)***   (Recommended, see [explaination](#seek))

Both `read()` and `pread()` are blocking calls, and the call will wait until data is returned.

//TBD - talk about read timeout and read error

//TBD - talk about return error values

## Read-after-Write (lack of) ordering and fsync()

To improve write performance and minimize blocking the userspace application calling `write()/pwrite()` system call, EDMA implement an intermediate write buffer before data is written to the FPGA Shell/CL interface.

If the developer want to issue `read()/pread()` from an address range that was previously written, the developer should issue fsync() to ensure the intermediate write buffer is flushed to the FPGA before the read is executed.


## Seek API

The EDMA driver implements the standard lseek() linux/posix system call, which will modify the current read/write pointer from the FPGA memory space. 

**WARNING: ** Calling lseek() without proper locking is pronged for errors, as concurrent/multi-threaded design could call lseek() concurrently and without an atomic followup with read/write().

//TBD - talk whether we have same position for read and write or they are separate

** Developers are encouraged to use pwrite() and pread(), which will perform lseek and write/read in atomic way **
  
## poll()

//TBD - alex - pls update


## Concurrency and Multi-threading

EDMA support concurrent multiple access from multiple processes and multiple threads within one process.  Multiple processes can call open()/close() to the same file-descriptor.

It is the developer's responsibility to make sure write to same memory region from different threads/processes is coordinated and not overlapping.

Worth re-iterating the recommended use of pread()/pwrite() over a sequency of lseek() + read()/write().


## Error Handling

The driver handles some error cases and passes other errors to the user.

The EDMA and its driver is designed to try to recover gracefully from errors, specifically application crashes or bugs in the Custom Logic portion of the FPGA. While the design tries to cover all known cases, there may be corner cases that are not recovered. The EDMA will print errors and logis to linux `dmesg` service indicating unrecoverable error.


#### Error: Application process crash 

In case a crash in the developer's user-space application, the operating system kernel takes care of all open file-descriptors (EDMA queues) associated with the process. Release (equivalent of `close()`) is called for every open file descriptor. When kernel closes them, the driver free and release all the transient read data and interrupt events from the FPGA to the application. The driver will also try to drain all outstanding write data to the FPGA.  If either of these tasks don’t finish after a timeout process, an error is reported in linux `dmesg` and the FPGA itself and EDMA driver may be in unknown.

#### Error: API Time-out

Timeout errors can occur in few place including:

1. Application stuck on `write()/pwrite()`, or its data that is stuck in transient buffer for too long because the CL is not accepting the data

2. A read() from CL portion of the FPGA that is stuck, causing the read() to block forever

The EDMA queue will have a timeout mechanism for this cases, and will automatically trigger tear-down process, and following the same procedure description in “Application process crash.” 


## Statistics Gathering

// TBD - alex, pls update all the information below

Stattistics are gathered using SysFS. Each edma has a sysfs entry matching the device (i.e. /dev/edma4 will have /sys/edma/edma4), and all the stats will be under that sysfs entry.
To see what available stats are there simply run 

`ls -l /sys/edma/edma4/*`
to read a specific start use cat utility

`cat /sys/edma/edma4/queue0/s2m_count`



# FAQ


**Q: How do I get the Source code of the EDMA driver and compile it?**

Amazon EDMA driver is included [AWS FPGA HDK/SDK](http://github.com/aws/aws-fpga/blob/master/sdk/linux_device_driver/edma), and may be included pre-installed in some Amazon Linux distribution.

Follow the [installation guide](./edma_install.md) for more details.

**Q: How to Discover the Available FPGAs with EDMA?**

Once the edma driver is running, then all the available devices would be found in /dev directory as /dev/edmaX.

    `$ ls /dev/edma*`
    
Each edma would expose multiple queues under /dev/edmaX_queueN (depending how many queues are supported by the AFI) and the developer could work directly with these queues.



**Q: When my write()/pwrite() call is returned, am I guaranteed that the data reached the FPGA?** 

Not necessary, the write() function will move the data from the user process to the kernel, which uses a 4MByte transient buffer per queue to transfer to the FPGA.   To optimize performance, the write() is returned to the user process once all data copies to the write transient buffer.  This is a common practice in modern OS where writes are stored in cache/transient buffer


**Q: What happens if write()/pwrite() have a length larger than the transient buffer?**

In this case, the process calling the write() will be blocked while the EDMA is writing data to the FPGA and freeing buffer


**Q: How do i know that last write did go to the FPGA?**

For performance optimization a write() call returns after the data has been copied to the kernel space. The only way to make sure the CL has processed the data is by calling fsync(). fsync() is a blocking call that will return only after all the data in the kernel transient buffers is written.


**Q: What will happen if the CL is not able to accept all write data? **

In this case, the EDMA will stop writing and drainingthe transient buffer, eventually causing the process that uses this particular queue to stall on a future write()/pwrite() command.  Paramount to note that this will not block the PCIe and other instance MMIO access to the CL through PCIe BAR will go through, as well EDMA for other queues.



**Q: Will EDMA drop data?**

During normal operations, the EDMA will NOT drop data, even when the CL is not able to accept data or running out of the transient buffer.  Both these scenarios are considered transient, and EDMA will not drop any data.

The only two cases the EDMA will drop data area:
1. Abrupt crash of the user process managing this queue
2. A close() function that times-out (could happen if the CL is not willing to accept data from EDMA)
  
  

**Q: Will my read()/pread() time out?**

If the read() function return -1, an error has occurred, and this error is reported in errno pseudo variable.
please refer to TBD for a list of supported errno values

// TBD - alex, pls update

**Q: How would I check if EDMA encountered errors?**

EDMA would output its log through the standard Linux dmesg service.

`$ dmesg | grep “edma” `

**Q: Will EDMA use interrupts during data transfers?**

EDMA in kernel driver uses MSI-X interrupts,  one interrupt pair of EDMA read/write queues.
To know what IRQ number is used for EDMA, the user can 

`$ cat /proc/interrupts`


**Q: Would EDMA support transfer of Scatter-gather list?**

AWS is considering this for future versions of EDMA to include scatter-gather-list (SGL) based transfers using IOCTL API. 

