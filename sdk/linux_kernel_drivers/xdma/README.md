
# Using AWS XDMA in C/C++ application

## Table of Content

1. [Overview](#overview)
2. [Quick Example](#quickExample)
3. [Detailed Description](#detailed)
  - [File Descriptors](#fd)
  - [Setup and tear down](#openclose)
  - [Write calls](#write)
  - [Read calls](#read)
  - [Poll call](#poll)
  - [Concurrency, multi-threading](#concurrency)
  - [Error handling](#error)
4. [Frequently Asked Questions](#faqs)

<a name="overview"></a>
# Overview

The XDMA Driver is provided as an option to transfer data between the FPGA and the Instance's CPU memory.

XDMA driver objectives: <br />
1. Open-source driver <br />
2. Easy to install and use, and does not require driver development expertise to use <br />
3. Multi-channel interface for high performance. <br />
4. Support multiple FPGAs per instance, and multiple channels per FPGA <br />

XDMA driver source code is distributed with AWS FPGA HDK and SDK.

[XDMA Installation Guide](./xdma_install.md) provides detailed guidelines on how to compile, install and troubleshoot a XDMA installation.

** NOTE: Usage of XDMA is not mandatory. AWS provides memory-mapped PCIe address space for direct communication between CPU and FPGA. **

For a complete description of the different CPU to FPGA communication options and various options available, please review the [Programmers' View](../../../hdk/docs/Programmer_View.md).

<a name="quickExample"></a>
# Quick Example

Before diving into the detail specification of the XDMA, here’s a short, intuitive example on how the developer could use XDMA:

The Program below uses standard Linux system call `open()` to create a file descriptor (fd), mapping to a pair of XDMA channels (one for `read()` and one for `write()`).  The XDMA hardware engine is named the `XDMA Core`.  The XDMA write channel is called H2C (Host to Core).  The XDMA read channel is called C2H (Core to Host). The Core refers to the FPGA and the Host refers to the instance CPU.


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
    int read_fd;
    int write_fd;
    int i;
    int ret;

    srcBuf = (char*)malloc(BUF_SIZE * sizeof(char));
    dstBuf = (char*)malloc(BUF_SIZE * sizeof(char));

    /* Initialize srcBuf */
    rand_str(srcBuf, BUF_SIZE);

    /* Open a XDMA write channel (Host to Core) */
    if ((write_fd = open("/dev/xdma0_h2c_0",O_WRONLY)) == -1) {
        perror("open failed with errno");
    }
    
    /* Open a XDMA read channel (Core to Host) */
    if ((read_fd = open("/dev/xdma0_c2h_0",O_RDONLY)) == -1) {
        perror("open failed with errno");
    }

    /* Write the entire source buffer to offset OFFSET_IN_FPGA_DRAM */
    ret = pwrite(write_fd , srcBuf, BUF_SIZE, OFFSET_IN_FPGA_DRAM);
    if (ret < 0) {
        perror("write failed with errno");
    }
    
    printf("Tried to write %u bytes, succeeded in writing %u bytes\n", BUF_SIZE, ret);

    ret = pread(read_fd, dstBuf, BUF_SIZE, OFFSET_IN_FPGA_DRAM);
    if (ret < 0) {
        perror("read failed with errno");
    }
    
    printf("Tried reading %u byte, succeeded in read %u bytes\n", BUF_SIZE, ret);

    if (close(write_fd) < 0) {
        perror("write_fd close failed with errno");
    }
    if (close(read_fd) < 0) {
        perror("read_fd close failed with errno");
    }

    printf("Data read is %s\n", dstBuf);
    
    return 0;
} 
```

<a name="detailed"></a>
# Detailed Description

<a name="fd"></a>
## Using file operations to perform DMA

The XDMA driver can be used in any user-space program, using simple device operations following standard Linux/POSIX system calls.  Each XDMA channel has a H2C and C2H device filename (e.g. `/dev/xdma0_h2c_0` and `/dev/xdma0_c2h_0`), and supports the Linux character device APIs.

XDMA data movement commands (like `pread()` and `pwrite()`) use a buffer pointers `void*` to the instance CPU memory, while using file offset `off_t` to present the write-to/read-from address in the FPGA.

**NOTE: ** In EC2 F1 instances, the file offset represents the write-to/read-from address in the FPGA relative to AppPF BAR4 128GB address space. The DMA cannot access any other PCIe BAR space. Refer to [FPGA PCIe Memory Address Map](../../../hdk/docs/AWS_Fpga_Pcie_Memory_Map.md).


<a name="openclose"></a>
## Initialization and Tear Down API

Initialization is done using the standard file-open API:
`int open(const char *pathname, int flags);`

Where file name is one of the H2C or C2H device files (e.g. `/dev/xdmaX_h2c_Y` or `/dev/xdmaX_c2h_Y`). (X is the FPGA slot, Y is the specific channel), with the only flags recommended are `O_WRONLY` or `O_RDONLY` for the corresponding H2C or C2H channel direction.  All other flags are ignored.

Multiple threads or processes can open the same file, and it is the developer's responsibility to ensure coordination/serialization.

A corresponding `close()` is used to release the DMA channel.

<a name="write"></a>
## Write APIs

The two standard Linux/POSIX APIs for write are listed below:

***ssize_t write(int fd, void\* buf, size_t count)*** 

***ssize_t pwrite(int fd, void\* buf, size_t count, off_t offset)***   (Recommended, see [explanation](#seek))

The file-descriptor (fd) must have been opened successfully before calling `write()/pwrite()`.

`buf`, the pointer to the source buffer to write to FPGA can have arbitrary size and alignment.

The XDMA driver is responsible for mapping the `buf` memory range to list of physical addresses that the hardware DMA can use. 

The XDMA driver takes care of pinning the user-space `buf` memory so that it cannot be swapped out during the DMA transfer.

<a name="read"></a>
## Read APIs 

***ssize_t read(int fd, void\* buf, size_t count)*** 

***ssize_t pread(int fd, void\* buf, size_t count, off_t offset)***   (Recommended, see [explaination](#seek))

Both `read()` and `pread()` are blocking calls, and the call waits until data is returned.

Read returns the number of successful bytes, and it is the user responsibility to call `read()` with the correct offset again if the return value is not equal to count. In a case of DMA timeout (10 seconds), EIO is returned. 

Possible errors:<br />
EIO - DMA timeout or transaction failure.<br />
ENOMEM - System is out of memory.<br />

**NOTE:** In case of any of the aforementioned errors, the FPGA and XDMA is left in unknown state, with Linux `dmesg` log potentially providing more insight on the error (see FAQ: How would I check if XDMA encountered errors?).

<a name="seek"></a>
## Seek API

The XDMA driver implements the standard `lseek()` Linux/POSIX system call, which modifies the character device file position. The position is used in `read()`/`write()` to point the FPGA memory space. 

**WARNING: ** Calling `lseek()` without proper locking is prone to errors, as concurrent/multi-threaded design could call `lseek()` concurrently and without an atomic follow up with `read()/write()`.

The file_pos is a file attribute; therefore, it is incremented by both `write()` and `read()` operations by the number of bytes that were successfully written or read.

**Developers are encouraged to use `pwrite()` and `pread()`, which performs lseek and write/read in an atomic way**

<a name="poll"></a>
## Poll API

The `poll()` function provides applications with a mechanism for multiplexing input over a set of file descriptors for matching user events. This is used by the XDMA driver for user generated interrupts events, and not used for data transfers.

Only the POLLIN mask is supported and is used to notify that an event has occurred.

Refer to [User-defined interrupts events README](./user_defined_interrupts_README.md) for more details.

The application MUST issue a `pread` of the ready file descriptor to return and clear the `events_irq` variable within the XDMA driver in order to be notified of future user interrupts.  An example of using `poll` and `pread` for user defined interrupts is provided within the test_dram_dma.c `interrupt_example()`.

<a name="concurrency"></a>
## Concurrency and Multi-Threading

XDMA supports concurrent multiple access from multiple processes and multiple threads within one process.  Multiple processes can call `open()/close()` to the same file descriptor.

It is the developer's responsibility to make sure write to same memory region from different threads/processes is coordinated and not overlapping.

To re-iterate, use of `pread()/pwrite()` is recommended over a sequence of `lseek()` + `read()/write()`.

<a name="error"></a>
## Error Handling

The driver handles some error cases and passes other errors to the user.

XDMA is designed to attempt a graceful recovery from errors, specifically application crashes or bugs in the Custom Logic portion of the FPGA. While the design attempts to cover all known cases, there may be corner cases that are not recoverable. The XDMA driver prints errors to Linux `dmesg` service indicating an unrecoverable error  (see FAQ: How would I check if XDMA encountered errors?).

#### Error: Application Process Crash 

In case of a crash in the userspace application, the operating system kernel tears down of all open file descriptors (XDMA channels) associated with the process. Release (equivalent of `close()`) is called for every open file descriptor.  In-flight DMA reads or writes are aborted and an error is reported in Linux `dmesg`. The FPGA itself and the XDMA driver may be left in an unknown state (see FAQ: How would I check if XDMA encountered errors?).

#### Error: API Time-out

Timeout errors can occur in few places including:

1. Application stuck on `write()/pwrite()`.

2. A `read()` from CL portion of the FPGA that is stuck, causing the read() to block forever.

The XDMA driver has a timeout mechanism for this case (10 seconds), automatically triggers DMA transfer abort processing, and follows the same procedure description in “Application process crash” mentioned previously.

<a name="faqs"></a>
# FAQ

**Q: How do I get the Source code of the XDMA driver and compile it?**

The XDMA driver is included [AWS FPGA HDK/SDK](.), and may be included pre-installed in some Amazon Linux distributions.

Follow the [installation guide](./xdma_install.md) for more details.

**Q: How to discover the available FPGAs with the XDMA driver?**

Once the XDMA driver is running, all the available devices will be listed in /dev directory as /dev/xdmaX.

    `$ ls /dev/xdma*`
    
Each XDMA device exposes multiple channels under `/dev/xdmaX_h2c_Y` and `/dev/xdmaX_c2h_Y` and the developer can work directly with these character devices.

**Q: When my `write()`/`pwrite()` call is returned, am I guaranteed that the data reached the FPGA?** 

No. System calls to `write()`/`pwrite()` return the number of bytes which were written or read. It is up to the caller to make the call again if the operation did not complete.

**Q: Can XDMA drop data?**

During normal operations, XDMA does NOT drop data.

Two cases in which XDMA does drop data are:
1. Abrupt crash of the user process managing this channel
2. Timeout on the XDMA transfer.
  
  
**Q: Does my `read()`/`pread()` or `write()`/`pwrite()` time out?**

If the `read()` or `write` function returns -1, an error has occurred, and this error is reported in errno pseudo variable.

**Q: How would I check if XDMA encountered errors?**

XDMA would output its log through the standard Linux dmesg service.

` $ dmesg | grep “xdma” `

**Q: Does XDMA use interrupts during data transfers?**

The XDMA kernel driver can use MSI-X interrupts, one interrupt pair is used for a XDMA read/write channel.
To know what IRQ number is used for XDMA, the user can 

` $ cat /proc/interrupts | grep xdma`

**Q: Does XDMA support polled DMA descriptor completion mode for data transfers?**
 
XDMA supports both interrupt and polled DMA descriptor completion modes.  

Abbreviated interrupt vs polled mode processing steps to show the differences:

Interupt mode:

1.) Submit the DMA descriptor to the FPGA HW, 2.) put the calling thread to sleep via wait_event_interruptible_timeout, 3.) context switch and processs the DMA completion interrupt within the XDMA interrupt service routine and wake up the thread from 2, 4.) context switch back to the thread from 2. so it can cleanup the DMA IO.

Polled mode:

1.) Submit the DMA descriptor to the FPGA HW, 2.) efficiently poll a DMA coherent writeback buffer that the FPGA HW updates to indicate descriptor completion, then cleanup the DMA IO.  Note that the thread that is polling the writeback buffer releases control back to the Linux scheduler every 100 iterations to avoid hogging the vCPU and also includes a timeout feature. 
  
Due to the reduction in processing steps and thread context switches, polled DMA descriptor completion mode may have significant performance advantages over interrupt mode in certain application use cases that use smaller IO sizes (e.g. < 1MB).  Developers are encouraged to experiment with both interrupt and polled DMA descriptor completion modes and use the mode that best suits your application.

XDMA polled DMA descriptor completion mode is enabled at XDMA driver load time:

` $ insmod xdma.ko poll_mode=1`

XDMA interrupt DMA descriptor completion mode is also enabled at XDMA driver load time (default):

` $ insmod xdma.ko`
