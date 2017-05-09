
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

Amazon EDMA driver objectives: <br />
1. Open-source driver <br />
2. Easy to install and use, and does not require driver development expertise to use <br />
3. High-performance multi-queue interface, to lower CPU overhead. <br />
4. Support multiple FPGAs per instance, and multiple queues per FPGA <br />
5. Expandable by developers <br />

EDMA driver source code is distributed with AWS FPGA HDK and SDK.

[EDMA Installation Guide](./edma_install.md) provides detailed guidelines on how to compile, install and troubleshoot EDMA installation.

** NOTE: Usage of EDMA is not mandatory. AWS provides memory-mapped PCIe address space for direct communication between CPU and FPGA. **

For a complete description of the different CPU to FPGA communication options and various options available for the programmer, please review the [Programmers' View](https://github.com/aws/aws-fpga/blob/master/hdk/docs/Programmer_View.md).

<a name="quickExample"></a>
# Quick Example

Before diving into the detail specification of the EDMA, here’s a short, intuitive example on how the developer could use the EDMA in a process:

The Program below uses standard Linux system call `open()` to create a file descriptor (fd), mapping to a pair of EDMA queues (one for `read()` and one for `write()`).


```
#include <stdlib.h>
#include <stdio.h>
#include <fcntl.h>
#include <errno.h>
#include <unistd.h>

#define BUF_SIZE              256
#define OFFSET_IN_FPGA_DRAM   0x10000000

static char *rand_str(char *str, size_t size)  // randomize a string of size <size>
{
    const char charset[] = "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRTSUVWXYZ1234567890";
    int i;

    for(i = 0; i < size; i++) {
        int key = rand() % (int) (sizeof charset - 1);
        str[i] = charset[key];
    }

    str[size-1] = '\0';
    return str;
}


int main()
{
    char* srcBuf;
    char* dstBuf;
    int fd;
    int i;
    int ret;

    srcBuf = (char*)malloc(BUF_SIZE * sizeof(char));
    dstBuf = (char*)malloc(BUF_SIZE * sizeof(char));

    /* Initialize srcBuf */
    rand_str(srcBuf, BUF_SIZE);

    /* Open an EDMA queue for read/write */
    if((fd = open("/dev/edma0_queue_0",O_RDWR)) == -1) {
        perror("open failed with errno");
    }

    /* Write the entire source buffer to offset OFFSET_IN_FPGA_DRAM */

    ret = pwrite(fd , srcBuf, BUF_SIZE, OFFSET_IN_FPGA_DRAM);
    if(ret < 0) {
        perror("write failed with errno");
    }
    
    printf("Tried to write %u bytes, succeeded in writing %u bytes\n", BUF_SIZE, ret);

    /* ensure the write made it to the Shell/CL interface */
    fsync(fd);

    ret = pread(fd, dstBuf, BUF_SIZE, OFFSET_IN_FPGA_DRAM);

    if(ret < 0) {
        perror("read failed with errno");
    }
    
    printf("Tried reading %u byte, succeeded in read %u bytes\n", BUF_SIZE,ret);

    if(close(fd) < 0) {
        perror("close failed with errno");
    }

    printf("Data read is %s\n", dstBuf);
    
    return 0;
} 
```

<a name="detailed"></a>
# Detailed Description

<a name="fd"></a>
## Using file operations to perform DMA

The EDMA can be used in any user-space developer program, using simple device operations following standard Linux/POSIX system calls.  Each EDMA queue has a `/dev/edmaX_queueY` filename, hence it supports Linux character device APIs.

EDMA data movement commands (like `read()` and `write()`) use a buffer pointers `void*` to the instance CPU memory, while using file offset `off_t` to present the write-to/read-from address in the FPGA.

**NOTE: ** In EC2 F1 instances, the file offset represent the write-to/read-from address in the FPGA relative to AppPF BAR4 128GB address space. The DMA can not access any other PCIe BAR space. Refer to [FPGA PCIe Memory Address Map](aws-fpga/hdk/docs/AWS_Fpga_Pcie_Memory_Map.md).  


<a name="openclose"></a>
## Initialization and Tear Down API

Initialization is done using the standard file-open API:
`int open(const char *pathname, int flags);`

Where file name is one of the `/dev/edmaX_queueY` (X is the FPGA slot, Y is the specific queue), with the only flags recommended is `O_RDWR`, and all other flags are ignored.

Multiple threads or processes can open the same file, and it is the developer's responsibility to ensure coordination/serialization.

A corresponding `close()` is used to release the DMA queue.  The `close()` call blocks until all other pending calls (like read or write) finish, any call to the file-descriptor following `close()` returns an error. 
If `close()` waits for more than 3 seconds and all other pending calls did not finish, it panics, and the FPGA is left in undefined state. Linux `dmesg` log service would include more debug information.

<a name="write"></a>
## Write APIs

The two standard Linux/POSIX APIs for write are listed below:

***ssize_t write(int fd, void\* buf, size_t count)*** 

***ssize_t pwrite(int fd, void\* buf, size_t count, off_t offset)***   (Recommended, see [explaination](#seek))

The file-descriptor (fd) must have been opened successfully before calling `write()/pwrite()`.

`buf`, the pointer to the source buffer to write to FPGA can have arbitrary size and alignment.

EDMA driver is responsible for mapping the `buf` memory range to list of physical addresses that the hardware DMA can use. 

EDMA driver takes care of copying and/or pinning the user-space `buf` memory, and the developer doesn't need to worry about it.

### Writes are Semi-asynchronous

To improve write performance, and allow the application to write small messages and increase concurrency, the `write()`/`pwrite()` **may** copy the write data to an intermediate transmit buffer in the kernel, that is later drained to the FPGA.

Developers' who want to guarantee that the writen data has reached the CL (Custom Logic) portion of the FPGA, must call `fsync()` after `write()`/`pwrite()`. See [Fsync description](#fsync).


<a name="read"></a>
## Read APIs 

***ssize_t read(int fd, void\* buf, size_t count)*** 

***ssize_t pread(int fd, void\* buf, size_t count, off_t offset)***   (Recommended, see [explaination](#seek))

Both `read()` and `pread()` are blocking calls, and the call waits until data is returned.

Read returns the number of successful bytes, and it is the user responsibility to call `read()` with the correct offset again if the return value is not equal to count. In a case of DMA timeout (3 seconds), EIO is returned. 

Possible errors:<br />
EIO - DMA timeout or transaction failure.<br />
ENOMEM - System is out of memory.<br />

**NOTE:** In case of any of the before mentioned errors, the FPGA and EDMA is left in unknown state, with linux `dmesg` log potentially providing more insight on the error.

<a name="fsync"></a>
## Write Synchronization, Read-after-Write (lack of) Ordering and `fsync()`

To improve write performance and minimize blocking the userspace application calling `write()/pwrite()` system call, EDMA implement an intermediate write buffer before data is written to the FPGA Shell/CL interface.

If the developer wants to issue `read()/pread()` from an address range that was previously written, the developer should issue `fsync()` to ensure the intermediate write buffer is flushed to the FPGA before the read is executed.

`fsync()` waits between 1-4 seconds for all pending DMA write transaction to complete, and returns EIO if not all transactions are completed. In EIO is returned, the FPGA and EDMA driver are left in unknown state, linux `dmesg` log service could have additional debug infromation.


<a name="seek"></a>
## Seek API

The EDMA driver implements the standard `lseek()` Linux/POSIX system call, which modifies the chararcter device file position. The porition is used in `read()`/`write()` to point the FPGA memory space. 

**WARNING: ** Calling `lseek()` without proper locking is prone to errors, as concurrent/multi-threaded design could call `lseek()` concurrently and without an atomic follow up with `read()/write()`.

The file_pos is a file attribute; therefore, it is incremented by both `write()` and `read()` operations by the number of bytes that were successfully written or read.

**Developers are encouraged to use `pwrite()` and `pread()`, which performs lseek and write/read in an atomic way**

<a name="poll"></a>
## Poll API

The `poll()` function provides applications with a mechanism for multiplexing input over a set of file descriptors for matching user events. This is used by the EDMA driver for user generated interrupts events, and not used for data transfers.

Only the POLLIN mask is supported and is used to notify that an event has occuer.

Refer to [User-defined interrupts events README](./user_defined_interrupts_README.md)


<a name="concurrency"></a>
## Concurrency and Multi-Threading

EDMA support concurrent multiple access from multiple processes and multiple threads within one process.  Multiple processes can call `open()/close()` to the same file descriptor.

It is the developer's responsibility to make sure write to same memory region from different threads/processes is coordinated and not overlapping.

To re-iterate, use of `pread()/pwrite()` is recommended over a sequency of `lseek()` + `read()/write()`.

<a name="error"></a>
## Error Handling

The driver handles some error cases and passes other errors to the user.

The EDMA and its' driver are designed to attempt a graceful recovery from errors, specifically application crashes or bugs in the Custom Logic portion of the FPGA. While the design attempts to cover all known cases, there may be corner cases that are not recoverable. The EDMA prints errors and logic to Linux `dmesg` service indicating an unrecoverable error.


#### Error: Application Process Crash 

In case of a crash in the developer's user-space application, the operating system kernel tears down of all open file descriptors (EDMA queues) associated with the process. Release (equivalent of `close()`) is called for every open file descriptor. When the kernel closes them, the driver frees and releases all the transient read-data and interrupt events. The driver also trys to drain all outstanding writes towards the FPGA.  If either of these tasks don’t finish after a timeout, an error is reported in Linux `dmesg` and the FPGA itself and EDMA driver may be left in an unknown state.

#### Error: API Time-out

Timeout errors can occur in few places including:

1. Application stuck on `write()/pwrite()`, or its data that is stuck in transient buffer for too long because the CL is not accepting the data.

2. A `read()` from CL portion of the FPGA that is stuck, causing the read() to block forever.

The EDMA queue have a timeout mechanism for this cases (3 seconds), and automatically triggers tear-down process, and following the same procedure description in “Application process crash” mentioned previously. 

3. `Fsync()` is stuck on completing all outstanding `write()` transactions.

`Fsync()` returns and error in case of a timeout on completion.

4. `Release()` is waiting for other syscalls (`read()`, `write()`, `fsync()`) to finish.

Release waits for 3 seconds and if any of the syscalls is not done - it dumps an error to the `dmesg` and panics the kernel.

<a name="stats"></a>
## Statistics Gathering

Statistics are gathered using sysfs. Each EDMA queue has a sysfs entry (i.e. /dev/edmaX_queueY has /sys/edma/edmaX_queueY), and all the stats are under that sysfs entry.

To see what stats are available for a specific EDMA queue, simply run:

`$ ls -l /sys/class/edma/edma0_queue_0/*`
  

to read a specific statistic use cat utility

```
$ cat /sys/class/edma/edma0_queue_0/stats

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

Once the EDMA driver is running, all the available devices would be found in /dev directory as /dev/edmaX.

    `$ ls /dev/edma*`
    
Each EDMA exposes multiple queues under /dev/edmaX_queueN (depending how many queues are supported by the AFI) and the developer could work directly with these queues.



**Q: When my `write()`/`pwrite()` call is returned, am I guaranteed that the data reached the FPGA?** 

Not necessarily, the `write()` function moves the data from the user process to the kernel, which uses a 4MByte transient buffer per queue to transfer to the FPGA. To optimize performance, the `write()` is returned to the user process once all data is copied to the write transient buffer. This is a common practice in modern OS where writes are stored in cache / transient buffer


**Q: What happens if `write()`/`pwrite()` have a length larger than the transient buffer?**

In this case, the process calling the `write()` is blocked while the EDMA is writing data to the FPGA and freeing the transient-buffer. `write()` returns when *all* data is copied to the transient buffer.


**Q: How do i know that last write did reach the FPGA?**

For performance optimization, a `write()` call returns after the data has been copied to the kernel space. The only way to make sure the CL has processed the data is by calling `fsync()`. `fsync()` is a blocking call that returns only after all the data in the kernel transient buffers is written to the FPGA.


**Q: What happens if the CL is not able to accept all write data? **

In this case, the EDMA stops writing and drain the transient buffer, eventually causing the process that uses this particular queue to stall on a future `write()`/`pwrite()` command.  It is paramount to note that this does not block the PCIe, and other instance MMIO accesses to the CL through PCIe BAR will go through, as well as EDMA transfers intiated by other queues.



**Q: Does EDMA drop data?**

During normal operations, the EDMA does NOT drop data, even when the CL is not able to accept data or running out of the transient buffer. Both these scenarios are considered transient, and EDMA does not drop any data.

The only two cases the EDMA does drop data area:
1. Abrupt crash of the user process managing this queue
2. A `close()` function that times-out (could happen if the CL is not willing to accept data from EDMA)
  
  
**Q: Does my `read()`/`pread()` time out?**

If the `read()` function return -1, an error has occurred, and this error is reported in errno pseudo variable.
Please refer to the API read description for a list of supported errno values


**Q: How would I check if EDMA encountered errors?**

EDMA would output its log through the standard Linux dmesg service.

` $ dmesg | grep “edma” `

**Q: Does EDMA use interrupts during data transfers?**

EDMA in kernel driver uses MSI-X interrupts, one interrupt pair of EDMA read/write queues.
To know what IRQ number is used for EDMA, the user can 

` $ cat /proc/interrupts`


**Q: Would EDMA support transfer of Scatter-gather list?**

AWS is considering to include scatter-gather-list (SGL) based transfers for future versions of EDMA, using IOCTL API. 


