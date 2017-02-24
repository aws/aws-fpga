# Using AWS EDMA in C/C++ application

## Table of Content

1. [Overview](#overview)
2. [Quick Example](#quickExample)
3. [Detailed Description](#detailed)
  - [File Descriptors](#fd)
  - [Setup and tear down](#openclose)
  - [Write calls](#write)
  - [Read calls](#read)
  - [FSync call](#fsync)
  - [Seek call](#seek)
  - [Poll call](#poll)
  - [Concurrency, multi-threading](#concurrency)
  - [Error handling](#error)
  - [Statistics](#stats)
4. [Frequently Asked Questions](#faqs)

<a name="overview"></a>
# Overview

Amazon Elastic-DMA (EDMA) Driver is provided as an option transfer data between the FPGA and the Instance's CPU memory.

Amazon EDMA driver objectives:
1. Open source driver
2. Easy to install and use, and does not require driver development expertise to use
3. Support multiple FPGAs per instance, and multiple queues per FPGA
4. Expandable by developers
5. High-performance multi-queue interface, to lower CPU overhead.

EDMA driver source code is distributed with AWS FPGA HDK and SDK.

[EDMA Installation Guide](./edma_install.md) provides detailed guidelines how to compile, install and troubleshoot EDMA installation.

** NOTE: Usage of EDMA is not mandatory, and AWS FPGA provides memory-mapped PCIe address space for direct communication between CPU and FPGA. **

For a complete description of the different CPU to FPGA communication options and various options available for the programmer, please review the [Programmers' View](https://github.com/aws/aws-fpga/blob/master/hdk/docs/Programmers_View.md).

<a name="quickExample"></a>
# Quick Example

Before diving into the detail specification of the EDMA, here’s a short, intuitive example how the developer could use the EDMA in a process:

The Program below will use standard Linux system call open() to create a file descriptor (fd), mapping to a pair of EDMA queues (one for `read()` and one for `write()`).


```
#include <stdlib.h>
#include <stdio.h>
#include <fcntl.h>
#include <errno.h>
#include <unistd.h>

#define BUF_SIZE    256
#define OFFSET_IN_FPGA_DRAM 0x10000000

static char *rand_str(char *str, size_t size)
{
    const char charset[] = "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRTSUVWXYZ1234567890";
    int i;

    for(i = 0; i < size; i++){
        int key = rand() % (int) (sizeof charset - 1);
        str[i] = charset[key];
    }

    str[size-1] = '\0';

    return str;
}


int main(){
    char* srcBuf;
    char* dstBuf;
    int fd;
    int i;
    int ret;

    srcBuf = (char*)malloc(BUF_SIZE * sizeof(char));
    dstBuf = (char*)malloc(BUF_SIZE * sizeof(char));

    /* Initialize srcBuf */
    rand_str(srcBuf, BUF_SIZE);

    if((fd = open("/dev/edma0_queue_0",O_RDWR)) == -1)
    {
              perror("open failed with errno");
    }

    /* Write the entire source buffer to offset OFFSET_IN_FPGA_DRAM */

    ret = pwrite(fd , srcBuf, BUF_SIZE, OFFSET_IN_FPGA_DRAM);

    if( ret < 0)
    {
              perror("write failed with errno");
    }

    printf("Tried to write %u bytes, succeeded in writing %u bytes\n", BUF_SIZE, ret);

    /* ensure the write made it to the Shell/CL interface */
    fsync(fd);

    ret = pread(fd, dstBuf, BUF_SIZE, OFFSET_IN_FPGA_DRAM);

    if(ret < 0)
    {
              perror("read failed with errno");
    }

    printf("Tried reading %u byte, succeeded in read %u bytes\n", BUF_SIZE,ret);

    if(close(fd) < 0)
    {
              perror("close failed with errno");
    }

    printf("Data read is %s\n", dstBuf);

} 
```

<a name="detailed"></a>
# Detailed Description

<a name="fd"></a>
## Using file operations to perform DMA

The EDMA can be used in any developer program (running in user space) using simple device operations following standard Linux/POSIX system calls.  Each EDMA queue is has a `/dev/edmaX_queueY` filename, hence it support Linux character device APIs.

As DMA channel/queue would get a file-descriptors in the userspace applications, and data movement application (like `read()` and `write()` ) would use a buffer pointer `void*` to the instance CPU memory, while using file offset `off_t` to present the write-to/read-from address in the FPGA.

**NOTE: ** In EC2 F1 instances, the file offset represent the write-to/read-from address in the FPGA relative to AppPF BAR4 128GiB address space. The DMA can not access any other PCIe BAR space. Refer to [FPGA PCIe Memory Address Map](aws-fpga/hdk/docs/AWS_Fpga_Pcie_Memory_Map.md).  


<a name="openclose"></a>
## Initialization and Tear Down API

Using the standard:
`int open(const char *pathname, int flags);`

Where file name is one of the `/dev/edmaX_queueY` (X is the FPGA slot, Y is the specific queue), with the only flags recommended is `O_RDWR`, and all other flags will be ignored.

Multiple threads or processes can open the same file, and it is the developer's responsibility to ensure coordination/serialization, if required, using `lock` system call.

A corresponding `close()` is used to release the DMA queue.  The `close()` call will block until all other pending calls (like read or write) finish, any call to the file-descriptor following close() will return an error. 
If `close()` waits for more than 3 seconds and all other pending calls did not finish, it will panic, and the FPGA will be left in undefined state. Linux `dmesg` log service would include more debug information.

<a name="write"></a>
## Write APIs

The two standard linux/posix APIs for write are listed below:

***ssize_t write(int fd, void\* buf, size_t count)*** 

***ssize_t pwrite(int fd, void\* buf, size_t count, off_t offset)***   (Recommended, see [explaination](#seek))

The file-descriptor (fd) must have been opened successfully before calling `write()/pwrite()`.

`buf`, the pointer to the source buffer to write to FPGA can have arbitrary size and alignment.

EDMA driver is responsible for mapping the `buf` memory range to list of physical addresses that the hardware DMA can use. 

EDMA driver will take care of copying and/or pinning the user-space `buf` memory, and the developer doesn't need to worry about it.

### Writes are Semi-asynchronous

To improve write performance, and allow the application to write small messages and increase concurrency, the `write()`/`pwrite()` **may** copy the write data to an intermediate transmit buffer in the kernel, that will later be drained to the FPGA.

Developers' who want to guarantee that the writen data has reached the CL (Custom Logic) portion of the FPGA, must call `fsync()` after `write()`/`pwrite()`. See [Fsync description](#fsync).


<a name="read"></a>
## Read APIs 

***ssize_t read(int fd, void\* buf, size_t count)*** 

***ssize_t pread(int fd, void\* buf, size_t count, off_t offset)***   (Recommended, see [explaination](#seek))

Both `read()` and `pread()` are blocking calls, and the call will wait until data is returned.

Read will return the number of successful bytes, and it is the user responsibility to call `read()` with the correct offset again if the return value is not equal to count. In a case of DMA timeout (3 seconds), EIO will be returned. 

Possible errors:
EIO - DMA timeout or transaction failure.
ENOMEM - System is out of memory.

**NOTE:** In case of any of the before mentioned errors, the FPGA and EDMA will be left in unknown state, with linux `dmesg` log potentially providing more insight on the error.

<a name="fsync"></a>
## Write Synchronization, Read-after-Write (lack of) Ordering and fsync()

To improve write performance and minimize blocking the userspace application calling `write()/pwrite()` system call, EDMA implement an intermediate write buffer before data is written to the FPGA Shell/CL interface.

If the developer wants to issue `read()/pread()` from an address range that was previously written, the developer should issue fsync() to ensure the intermediate write buffer is flushed to the FPGA before the read is executed.

`fsync()` will wait between 1-4 seconds for all pending DMA write transaction to complete, and will return EIO if not all transactions are completed. In EIO is returned, the FPGA and EDMA driver are left in unknown state, linux `dmesg` log service could have additional debug infromation.


<a name="seek"></a>
## Seek API

The EDMA driver implements the standard `lseek()` Linux/POSIX system call, which will modify the current read/write pointer from the FPGA memory space. 

**WARNING: ** Calling `lseek()` without proper locking is pronged for errors, as concurrent/multi-threaded design could call `lseek()` concurrently and without an atomic follow up with `read()/write()`.

The file_pos is a file attribute; therefore, it is incremented by both `write()` and `read()` operations by the number of bytes that were successfully written or read.

**Developers are encouraged to use pwrite() and pread(), which will perform lseek and write/read in an atomic way**

<a name="poll"></a>
## Poll API

The poll() function provides applications with a mechanism for multiplexing input over a set of file descriptors for matching user events. This is used by the EDMA driver for user generated interrupts events, and not used for data transfers.

Only the POLLIN mask is supported and is used to notify that an event has occuer.

Refer to [User-defined interrupts events README](./user_defined_interrupts_README.md)


<a name="concurrency"></a>
## Concurrency and Multi-Threading

EDMA support concurrent multiple access from multiple processes and multiple threads within one process.  Multiple processes can call `open()/close()` to the same file descriptor.

It is the developer's responsibility to make sure write to same memory region from different threads/processes is coordinated and not overlapping.

Worth re-iterating the recommended use of `pread()/pwrite()` over a sequency of `lseek()` + `read()/write()`.

<a name="error"></a>
## Error Handling

The driver handles some error cases and passes other errors to the user.

The EDMA and its driver is designed to try to recover gracefully from errors, specifically application crashes or bugs in the Custom Logic portion of the FPGA. While the design tries to cover all known cases, there may be corner cases that are not recovered. The EDMA will print errors and logic to Linux `dmesg` service indicating a unrecoverable error.


#### Error: Application Process Crash 

In case a crash in the developer's user-space application, the operating system kernel takes care of all open file descriptors (EDMA queues) associated with the process. Release (equivalent of `close()`) is called for every open file descriptor. When the kernel closes them, the driver frees and releases all the transient read data and interrupt events from the FPGA to the application. The driver will also try to drain all outstanding write data to the FPGA.  If either of these tasks don’t finish after a timeout process, an error is reported in Linux `dmesg` and the FPGA itself and EDMA driver may be in unknown.

#### Error: API Time-out

Timeout errors can occur in few place including:

1. Application stuck on `write()/pwrite()`, or its data that is stuck in transient buffer for too long because the CL is not accepting the data.

2. A read() from CL portion of the FPGA that is stuck, causing the read() to block forever.

The EDMA queue have a timeout mechanism (3 seconds)for this cases, and will automatically trigger tear-down process, and following the same procedure description in “Application process crash” mentioned previously. 

<a name="stats"></a>
## Statistics Gathering

Statistics are gathered using SysFS. Each edma has a sysfs entry matching the FPGA slow (i.e. /dev/edmaX_queueY will have /sys/edma/edmaX_queueY), and all the stats will be under that sysfs entry.

To see what available stats for a specific EDMA queue, simply run:

`$ ls -l /sys/class/edma/edma0_queue0/*`
  

to read a specific start use cat utility

```
$ cat /sys/class/edma/edma0_queue0/stats

read_requests_submitted - 152
read_requests_completed - 152
write_requests_submitted - 87
write_requests_completed - 87
fsync_count - 6
no_space_left_error - 0
fsync_busy_count - 1
read_timeouts_error - 0
opened_times - 1

$ 
```


<a name="faqs"></a>
# FAQ


**Q: How do I get the Source code of the EDMA driver and compile it?**

Amazon EDMA driver is included [AWS FPGA HDK/SDK](http://github.com/aws/aws-fpga/blob/master/sdk/linux_device_driver/edma), and may be included pre-installed in some Amazon Linux distribution.

Follow the [installation guide](./edma_install.md) for more details.

**Q: How to discover the available FPGAs with EDMA?**

Once the edma driver is running, then all the available devices would be found in /dev directory as /dev/edmaX.

    `$ ls /dev/edma*`
    
Each edma would expose multiple queues under /dev/edmaX_queueN (depending how many queues are supported by the AFI) and the developer could work directly with these queues.



**Q: When my write()/pwrite() call is returned, am I guaranteed that the data reached the FPGA?** 

Not necessary, the write() function will move the data from the user process to the kernel, which uses a 4MByte transient buffer per queue to transfer to the FPGA.   To optimize performance, the write() is returned to the user process once all data copies to the write transient buffer.  This is a common practice in modern OS where writes are stored in cache/transient buffer


**Q: What happens if write()/pwrite() have a length larger than the transient buffer?**

In this case, the process calling the write() will be blocked while the EDMA is writing data to the FPGA and freeing buffer


**Q: How do i know that last write did go to the FPGA?**

For performance optimization, a write() call returns after the data has been copied to the kernel space. The only way to make sure the CL has processed the data is by calling fsync(). fsync() is a blocking call that will return only after all the data in the kernel transient buffers is written.


**Q: What will happen if the CL is not able to accept all write data? **

In this case, the EDMA will stop writing and drain the transient buffer, eventually causing the process that uses this particular queue to stall on a future write()/pwrite() command.  Paramount to note that this will not block the PCIe and other instance MMIO access to the CL through PCIe BAR will go through, as well EDMA for other queues.



**Q: Will EDMA drop data?**

During normal operations, the EDMA will NOT drop data, even when the CL is not able to accept data or running out of the transient buffer.  Both these scenarios are considered transient, and EDMA will not drop any data.

The only two cases the EDMA will drop data area:
1. Abrupt crash of the user process managing this queue
2. A close() function that times-out (could happen if the CL is not willing to accept data from EDMA)
  
  
**Q: Will my read()/pread() time out?**

If the read() function return -1, an error has occurred, and this error is reported in errno pseudo variable.
Please refer to the API read description for a list of supported errno values


**Q: How would I check if EDMA encountered errors?**

EDMA would output its log through the standard Linux dmesg service.

` $ dmesg | grep “edma” `

**Q: Will EDMA use interrupts during data transfers?**

EDMA in kernel driver uses MSI-X interrupts,  one interrupt pair of EDMA read/write queues.
To know what IRQ number is used for EDMA, the user can 

` $ cat /proc/interrupts`


**Q: Would EDMA support transfer of Scatter-gather list?**

AWS is considering this for future versions of EDMA to include scatter-gather-list (SGL) based transfers using IOCTL API. 

