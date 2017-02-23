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
int main(){
    char *srcBuf[12] = “Hello World”;
    char *dstBug[12] ;

    int fd;
    if((fd = open("/dev/edma0_queue0",O_RDWR)) == -1)
    {
              perror("open failed with errno %d\n",errno);
    }
        //Write the size of the string first for the CL.
    if(write(fd , strlen(srcBuf), 4) != 4)
    {
              perror("write failed with errno %d\n",errno);
    }
    if(write(fd, srcBuf, 12) != 12)
    {
              perror("write failed with errno %d\n",errno);
    }

    fsync(fd);
    if(read(fd, dstBuf, 12) < 0)
    {
              perror("read failed with errno %d\n",errno);
    }

    if(close(fd) < 0)
    {
              perror("close failed with errno %d\n",errno);
    }

    printf("Data read is %s\n", dstBuf);

} 
```

# Detailed Description

## Userspace API

The EDMA can be used in any developer program (running in user space) using simple device operations following standard linux/posix system calls.  Each EDMA queue is has a `/dev/edmaX_queueN` filename, hence it support linux character device APIs.

Here are all the supported functions:

_int (\*open) (struct inode \*, struct file \*) - opens an FD of a queue to interact with._

_int (\*release) (struct inode \*, struct file \*) - Called when a close() is called. This function is in charge of graceful queue cleanup._

ssize_t(*read) (struct file *, char __user *, size_t, loff_t *) - Read is an S2M (Stream to Memory) transaction from the FPGA CL to DRAM memory.

 ssize_t(*write) (struct file *, const char __user *, size_t, loff_t *) - Write is an M2S (Memory to Stream) transaction to the FPGA  from the DRAM memory to the FPGA CL.

int (*fsync) (struct file *, struct dentry *, int datasync) – Flush the driver data to the CL. Only after calling this function it is safe to assume that the CL processed write() transaction.


Unsupported features/apiAPI that are under future consideration:
 ssize_t(*aio_read) (struct kiocb *, char __user *, size_t, loff_t) – Same as read only non-blocking

 ssize_t(*aio_write) (struct kiocb *, const char __user *, size_t, loff_t) -  Same as write only non-blocking

unsigned int (*poll) (struct file *, struct poll_table_struct *) - Poll function is used for interrupts. An application will poll on an FD until it becomes ready. An FD is changed to ready when interrupt triggers.

int (*ioctl) (struct inode *, struct file *, unsigned int, unsigned long) – IOCTL could be used for scatter-gather operation and potentially for registering a user-specific interrupt (which is different from the the dedicated interrupts for EDMA). 


## Error Handling

The driver handles some error cases and passes other errors to the user.

Error Type
Behavior
Application process crashes
OS takes care of all open FD (EDMA queues) associated with the process. Release is called for every open file descriptor when OS closes them. The driver release function would free and release all in transient data from the CL to the application. The driver will also try to drain all outstanding write data to the CL.  If either of these tasks don’t finish after a timeout process, an error is reported in linux dmesg() and the EDMA should be reseted by the user.OS takes care of all open FD (EDMA queues) associated with the process. The release is called for every open file descriptor when OS closes them. The driver release function would free and release all the data in the transient buffer data from the CL to the application. The driver will also try to drain all outstanding write data to the CL.  If either of these tasks doesn't finish after a timeout process, an error is reported in Linux dmesg() and the EDMA should be reset by the user.
Timeout Errors in one of two cases:
1. Write() data that is stuck in transient buffer for too long because the CL is not accepting the data
2. A data from CL to Application that is stuck in transient while the application is not calling read() fast enough or with right size buffers
The EDMA queue will be automatically get into release() process, and following the same procedure description in “Application process crashes.” 
Statistics Gathering

Stattistics are gathered using SysFS. Each edma has a sysfs entry matching the device (i.e. /dev/edma4 will have /sys/edma/edma4), and all the stats will be under that sysfs entry.
To see what available stats are there simply run 

[ec2 user~$]  ls -l /sys/edma/edma4/*
to read a specific start use cat utility

[ec2 user~$]  cat /sys/edma/edma4/queue0/s2m_count



# FAQ


**Q: How do I get the Source code of the EDMA driver and compile it?**

Amazon EDMA driver is included [AWS FPGA HDK/SDK](http://github.com/aws/aws-fpga/blob/master/sdk/linux_device_driver/edma), and may be included pre-installed in some Amazon Linux distribution.

Follow the [installation guide](./edma_install.md) for more details.

**Q: How to Discover the Available FPGAs with EDMA?**

Once the edma driver is running, then all the available devices would be found in /dev directory as /dev/edmaX.

    `$ ls /dev/edma*`
    
Each edma would expose multiple queues under /dev/edmaX_queueN (depending how many queues are supported by the AFI) and the developer could work directly with these queues.



Internal FAQ

Why did we pick this approach?
We wanted to offer a solution with the following tenants:
1. Max compatibility with all OSes and no dependencies on external packages.
2. Use commonly known (userspace system-call) APIs like read/write.  Familiar and  (userspace system-call) which are intuitive and widely adopted by for developers.
3. Robust against process/application crash (Ctrl^C,  segmentation fault, etc.). which expected to happen often
4. Robust against address violations.
5. Developers would not need to change or worry about kernel driversAllow developers to focus on custom and application core logic, and avoid the need to develop or modify the kernel driver.


When my write() call is return, am I guaranteed that the data reached the FPGA?
Not necessary, the write() function will move the data from the user process to the kernel, which uses a 4MByte transient buffer per queue to transfer to the FPGA.   To optimize performance, the write() is returned to the user process once all data copies to the write transient buffer.  This is a common practice in modern OS where writes are stored in cache/transient buffer


What happens if write() have a length larger than the transient buffer?
In this case, the process calling the write() will be blocked while the EDMA is writing data to the FPGA and freeing buffer


How do i know that last write did go to the FPGA?
For performance optimization a write() call returns after the data has been copied to the kernel space. The only way to make sure the CL has processed the data is by calling fsync(). fsync() is a blocking call that will return only after all the data in the kernel transient buffers is written.


Could I get an interrupt once a specific transfer is done?
We are considering to add a poll() (or select()) support or alternative support (e.g. sigevent) to
notify the userspace on specific events. This will be available in future releases.


Will read() the dataHow will read() get data from the CL?
The CL EDMA will pass the S2M data to transient buffers in the kernel, and read() will read the data from the transient buffer.  If there is no data in the transient buffer the read() call will return with an error after a timeout will occur.


What will happen if the CL is not able to accept all write data?
In this case, the EDMA will stop fetching from the transient buffer, eventually causing the process that uses this particular queue to stall on a future write() command.  Paramount to note that this will not block the PCIe and other OS MMIO access to the CL through PCIe BAR will go through, as well EDMA for other queues.


What will happen if the user process can’t read the data?
This scenario could occur if a process doesn’t call read(), or the process is abruptly stopped, or calling read() with a buffer that is smaller than the expected data from the CL, or if the OS has scheduled out the process. In all these cases, the EDMA driver will accommodate some of the read data in the transient buffer until the transient buffer is ALMOST_FULL.
When the transient buffer is almost full, the EDMA will send out-of-band per-queue indicating there is no room for Data, and the CL is expected to step sending data on S2M for this particular queue.

What will happen if the CL doesn’t obey the ALMOST_FULL indication from the EDMA?
This could cause the EDMA AXI-stream bus to pause and push back on all the other queues, causing head-of-line blocking.  Hence AWS highly recommend the CL developers to use the ALMOST_FULL interface


Will EDMA drop data?
During normal operations, the EDMA will NOT drop data, even when the CL is not able to accept data or running out of the transient buffer.  Both these scenarios are considered transient, and EDMA will not drop any data.
The only two cases the EDMA will drop data area:
1. Abrupt crash of the user process managing this queue
2. A close() function that times-out (could happen if the CL is willing to accept data from EDMA)


Will my read() time out?
If the read() function return -1, an error has occurred, and this error is reported in errno pseudo variable.
please refer to the README file for a list of supported errno values


How would I check if EDMA encountered errors?
EDMA would output its log through the standard Linux dmesg service

[ec2 user~$] dmesg | grep “edma”

Will EDMA use interrupts?
EDMA in kernel driver uses MSI-X interrupts,  one interrupt per M2S queue and one per S2M queue.
To know what IRQ number is used for EDMA, the user can 

[ec2 user~$] cat /proc/interrupts

Would interrupts be issued on every byte sent/received?
EDMA has an adaptive interrupt implementation, where if there are a continuous stream of data coming from AFI to the user, an interrupt is only issued on the first transfer.  For lightly loaded system or infrequency access, the interrupt is issued almost on every access to minimize latency


Would EDMA support transfer of Scatter-gather list?
Future versions of EDMA may include scatter-gather-list (SGL) based transfers using IOCTL API. 

Appendix B

How to install the driver in CentOS/REHL and survive kernel updates?

1. Connect to your instance.
2. Update the package cache and packages.
centOS:~$ yum update
3. Install gcc and kernel-devel
centOS:~$ yum install kernel-devel
4. Get DKMS
centOS:~$ wget http://linux.dell.com/dkms/permalink/dkms-2.2.0.3-1.noarch.rpm
5. Get DKMS
centOS:~$ rpm -i dkms-2.2.0.3-1.noarch.rpm
6. Follow step 4 – 9 in the Ubuntu instructions

How to install the driver in Ubuntu and survive kernel updates?

1. Connect to your instance.
2. Update the package cache and packages.
ubuntu:~$ sudo apt-get update && sudo apt-get upgrade -y
Important
If during the update process you are prompted to install grub, use /dev/xvda to install grub onto, and then choose to keep the current version of /boot/grub/menu.lst.
3. Install the build-essential packages to compile the kernel module and the dkms package so that your edmamodule is rebuilt every time your kernel is updated.
ubuntu:~$ sudo apt-get install -y build-essential dkms
4. Clone the source code for the edma module on your instance from GitHub at http://github.com/amzn/amzn-drivers/fpga/hdk/driver/edma.
ubuntu:~$ git clone http://github.com/amzn/amzn-drivers/fpga/hdk/driver/edma
5. Move the edma package to the /usr/src/ directory so dkms can find it and build it for each kernel update. 
Append the version number (you can find the current version number in the release notes) of the source code to the directory name. For example, version 1.0.0 is shown in the example below.
ubuntu:~$ sudo mv amzn-drivers /usr/src/edma-1.0.0
6. Create the dkms configuration file with the following values, substituting your version of edma.
a. Create the file.
ubuntu:~$ sudo touch /usr/src/edma-1.0.0/dkms.conf
b. Edit the file and add the following values.
ubuntu:~$ sudo vim /usr/src/edma-1.0.0/dkms.conf
PACKAGE_NAME="edma"
PACKAGE_VERSION="1.0.0"
CLEAN="make -C kernel/linux/edma clean"
MAKE="make -C kernel/linux/edma/ BUILD_KERNEL=${kernelver}"
BUILT_MODULE_NAME[0]="edma"
BUILT_MODULE_LOCATION="kernel/linux/edma"
DEST_MODULE_LOCATION[0]="/updates"
DEST_MODULE_NAME[0]="edma"
AUTOINSTALL="yes"
7. Add, build, and install the edma module on your instance with dkms.
a. Add the module to dkms.
ubuntu:~$ sudo dkms add -m edma -v 1.0.0
b. Build the module with dkms.
ubuntu:~$ sudo dkms build -m edma -v 1.0.0
c. Install the module with dkms.
ubuntu:~$ sudo dkms install -m edma -v 1.0.0
8. Rebuild the initramfs so the correct module is loaded at boot time.
ubuntu:~$ sudo update-initramfs -c -k all
9. Verify that the edma module is installed using the modinfo edma.
ubuntu:~$ modinfo edma
filename:       /lib/modules/3.13.0-74-generic/updates/dkms/edma.ko
version:        1.0.0
license:        GPL
description:    Elastic Direct Memory Access
author:         Amazon.com, Inc. or its affiliates
srcversion:     9693C876C54CA64AE48F0CA
alias:          pci:v00001D0Fd0000EC21sv*sd*bc*sc*i*
alias:          pci:v00001D0Fd0000EC20sv*sd*bc*sc*i*
alias:          pci:v00001D0Fd00001EC2sv*sd*bc*sc*i*
alias:          pci:v00001D0Fd00000EC2sv*sd*bc*sc*i*
depends:
vermagic:       3.13.0-74-generic SMP mod_unload modversions
parm:           debug:Debug level (0=none,...,16=all) (int)

