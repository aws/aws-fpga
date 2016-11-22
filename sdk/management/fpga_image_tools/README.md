# AWS FPGA Image Management Tools

AWS provides the following set of tools for AWS FPGA Image (AFI) managment.   

* **fpga-describe-local-image-slots**
   * Returns the FPGA image slot numbers and device mappings to use for the fpga-load-local-image, fpga-clear-local-image, and fpga-describe-local-image commands.
* **fpga-describe-local-image**
   * Returns the status of the FPGA image for a specified FPGA image slot number. The fpga-image-slot parameter is a logical index that represents a given FPGA within an instance.  Use fpga-describe-local-image-slots to return the available FPGA image slots for the instance.
* **fpga-load-local-image**
   * Loads the specified FPGA image to the specified slot number, and returns the status of the command.  The fpga-image-slot parameter is a logical index that represents a given FPGA within an instance.  Use fpga-describe-local-image to return the FPGA image status, and fpga-describe-local-image-slots to return the available FPGA image slots for the instance.
* **fpga-clear-local-image**
   * Clears the specified FPGA image slot, including FPGA internal and external memories that are used by the slot. The fpga-image-slot parameter is a logical index that represents a given FPGA within an instance.  Use fpga-describe-local-image to return the FPGA image status, and fpga-describe-local-image-slots to return the available FPGA image slots for the instance.

## Versions
* Amazon Linux 2016.09

## Installs
* Pre-installed in /usr/bin for Amazon Linux.
* AWS SDK/HDK available from the github repository [aws-fpga](https://github.com/aws/aws-fpga).

## Prerequisites
* Linux based F1 instance.

## Quickstart

Display the logical FPGA slot numbers and device mappings for driver attachment (e.g. PCI Domain:Bus:Device:Function).

```

fpga-describe-local-image-slots -H

Type    FpgaImageSlot    VendorId    DeviceId    DBDF
AFIDEVICE     0    0x1d0f    0x1042    0000:00:17.0
AFIDEVICE     1    0x1d0f    0x1042    0000:00:18.0
AFIDEVICE     2    0x1d0f    0x1042    0000:00:19.0
AFIDEVICE     3    0x1d0f    0x1042    0000:00:1a.0
AFIDEVICE     4    0x1d0f    0x1042    0000:00:1b.0
AFIDEVICE     5    0x1d0f    0x1042    0000:00:1c.0
AFIDEVICE     6    0x1d0f    0x1042    0000:00:1d.0
AFIDEVICE     7    0x1d0f    0x1042    0000:00:1e.0


```

Display the current state for the given FPGA logical slot number.  Shows the FPGA in the “cleared” state on instance create.

```

fpga-describe-local-image -S 0 -H

Type    FpgaImageSlot    FpgaImageId    StatusName    StatusCode
AFI           0        cleared    1
Type    VendorId    DeviceId    DBDF
AFIDEVICE     0x1d0f    0x1042    0000:00:17.0

```

Load a FPGA image. Uses the FPGA logical slot number and Amazon Global FPGA Image parameters (see FAQ for AGFI).

```

fpga-load-local-image -S 0 -I agfi-004f34c45ed4e9603

```

Display the current state for the given FPGA logical slot number.  Shows the FPGA in the “loaded” state after the FPGA image "load" operation.

```

fpga-describe-local-image -S 0 -H

Type    FpgaImageSlot    FpgaImageId    StatusName    StatusCode
AFI           0    agfi-004f34c45ed4e9603    loaded    0
Type    VendorId    DeviceId    DBDF
AFIDEVICE     0x1d0f    0x1042    0000:00:17.0

```

Clear the FPGA image, including internal and external memories.

```

fpga-clear-local-image -S 0

```

Display the current state for the given FPGA logical slot number. Will show the FPGA in the “cleared” state after the FPGA image "clear" operation.

```

fpga-describe-local-image -S 0 -H

Type    FpgaImageSlot    FpgaImageId    StatusName    StatusCode
AFI           0        cleared    1
Type    VendorId    DeviceId    DBDF
AFIDEVICE     0x1d0f    0x1042    0000:00:17.0

```

The fpga-describe-local-image **metrics** option may be used to display FPGA image hardware metrics.
Examples: FPGA PCI and DDR ECC Metrics.

Additionally, the fpga-describe-local-image **clear-metrics** option may be used to display and clear FPGA image hardware metrics (clear on read).

All of the FPGA Image Management Tools support a **help** option that may be used to display the full set of options.
 
## fpga-describe-local-image **metrics** option
The following FPGA image hardware metrics are provided:
* pci-slave-timeout 
   * AFI did not respond to cycle from host
* pci-range-error 
   * PCI master cycle from AFI out of range
* pci-len-error 
   * PCI master AXI protocol/length error from AFI
* ps-timeout-addr 
   * PCI slave timeout address
* ps-timeout-count 
   * PCI slave timeout count
* pm-range-error-addr 
   * PCI master range error address
* pm-range-error-count 
   * PCI master range error count
* pm-len-error-addr 
   * PCI master length error address
* pm-len-error-count 
   * PCI master length error count
* pci-write-count 
* pci-read-count 
* DDR0
   * write-count
   * read-count
   * ecc-status
   * ecc-correctable-error-count
   * ecc-correctable-error-first-failing-data[4]
   * ecc-correctable-error-first-failing-ecc
   * ecc-correctable-error-first-failing-address
   * ecc-uncorrectable-error-first-failing-data[4]
   * ecc-uncorrectable-error-first-failing-ecc
   * ecc-uncorrectable-error-first-failing-address
* Repeated for DDR1,2,3

## Installing or updating the AWS FPGA Image Management Tools:
* AWS will release new versions of the AWS FPGA Image Management Tools from time to time.
* Amazon Linux will have the tools pre-installed in /usr/bin.
* The tools may be installed (non-Amazon Linux) or updated from [aws-fpga](https://github.com/aws/aws-fpga). 

## FAQ
* What is the Amazon Global FPGA Image Id (AGFI)?
   * The AGFI is an AWS globally unique identifier that is used to reference a specific AWS FPGA Image (AFI).
   * In the examples, `agfi-004f34c45ed4e9603` is specified in the `fpga-load-local-image` command in order to load a specific AFI
into the given fpga-image-slot.   
* What is a PF?
   * A PF refers to a PCI Physical Function that is exposed by the FPGA hardware.  For example, it is accessable by user-space programs via the sysfs filesystem in the path '/sys/bus/pci/devices/Domain:Bus:Device.Function'.  The 'Domain:Bus:Device.Function' syntax is the same as returned from 'lspci' program output.  Examples: **FPGA application PF** `0000:00:17.0`, **FPGA management PF** `0000:00:17.1`.  
* What is a DBDF?
   * A DBDF is simply an acronym for Domain:Bus:Device.Function. 
* What is a BAR?
   * A Base Address Register (BAR) specifies the memory region where device registers may be accessed.  Multiple BARs may be supported by a PCI device.  In this FAQ section (see PF), BAR0 from a device may be accessed (for example) by opening and memory mapping the resource0 sysfs file in the path '/sys/bus/pci/devices/Domain:Bus:Device.Function/resource0'.  Once BAR0 has been memory mapped, the BAR0 registers may be accessed through a pointer to the memory mapped region (refer to the open and mmap system calls).
* What is the AFIDEVICE and how is it used?
   * Within the `fpga-describe-local-image-slots` and `fpga-describe-local-image` commands the AFIDEVICE represents the PCI PF that is used to communicate with the AFI.  The AFIDEVICE functionality exposed through the PF is dependent on the AFI that is loaded via the `fpga-load-local-image` command.  For example, DMA and/or memory-mapped IO (MMIO) may be supported depending on the loaded AFI, which is then used to communicate with the AFI in order to perform an accelerated application-dependent task within the FPGA.  User-space applications may access the AFIDEVICE PF through sysfs as is noted above in this FAQ section (see PF).
* How do the AWS FPGA Image Management Tools work? 
   * Though most customers are not expected to understand the internals of the tools, a short overview is provided here:
   * Within the F1 instance, the FPGAs expose a management PF (e.g. 0000:00:17.1) that is used for communication between the instance and AWS.
   * The FPGA management PF BAR0 is **reserved** for this communication path.
   * The FPGA application drivers **should not** access the FPGA management PF BAR0.
   * The AWS FPGA Image Management Tools memory map the FPGA management PF BAR0 and communicate with AWS using internally defined messages and hardware registers.
   * For more information on the FPGA Image Mangement Tool software and FPGA hardware see [aws-fpga](https://github.com/aws/aws-fpga).
* Can the AWS FPGA Image Management Tools work concurently on multiple FPGA Image slots?
   * The tools can be executed on multiple FPGAs concurrently.  This may be done without synchronization between processes that are using the tools.
* Can the AWS FPGA Image Management Tools work concurrently from multiple processes on the same FPGA?
   * Without synchronization between processes, the tools should only be executed as one worker process per FPGA (highest level of concurrency), or one worker process accross all FPGAs (least level of concurrency).
   * Multiple concurrent process access to the tools using the same FPGA without proper synchronization between processes will cause response timeouts, and other indeterminate results. 

## References
* AWS FPGA SDK/HDK on github [aws-fpga](https://github.com/aws/aws-fpga)

### AWS EC2 References
* [AWS EC2 Getting Started](https://aws.amazon.com/ec2/getting-started/)
* [AWS EC2 Instance Types](https://aws.amazon.com/ec2/instance-types/)
* [AWS EC2 User Guide](http://docs.aws.amazon.com/AWSEC2/latest/UserGuide/concepts.html)
* [AWS EC2 Networking and Security](http://docs.aws.amazon.com/AWSEC2/latest/UserGuide/EC2_Network_and_Security.html)
* [AWS EC2 Key Pairs](http://docs.aws.amazon.com/AWSEC2/latest/UserGuide/ec2-key-pairs.html)
* [AWS EC2 Attach EBS Volume](http://docs.aws.amazon.com/AWSEC2/latest/UserGuide/ebs-attaching-volume.html)
* [AWS EC2 Troubleshooting](http://docs.aws.amazon.com/AWSEC2/latest/UserGuide/ec2-instance-troubleshoot.html)
