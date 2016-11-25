# Amazon FPGA Image (AFI) Management Tools

AWS provides the following a set of commands(tools) for Amazon FPGA Image (AFI) managment while running on an FPGA-enabled EC2 instance like EC2 F1. **The tools support Linux Instances only**

* **fpga-describe-local-image-slots**
   * Returns the FPGA image slot numbers and device mappings to use for the `fpga-load-local-image`, `fpga-clear-local-image`, and `fpga-describe-local-image` commands.
   
* **fpga-describe-local-image**
   * Returns the status of the FPGA image for a specified FPGA image slot number. The *fpga-image-slot* parameter is a logical index that represents a given FPGA within an instance.  Use `fpga-describe-local-image-slots` to return the available FPGA image slots for the instance.
   
* **fpga-load-local-image**
   * Loads the specified FPGA image to the specified slot number, and returns the status of the command.  The *fpga-image-slot* parameter is a logical index that represents a given FPGA within an instance.  Use `fpga-describe-local-image` to return the FPGA image status, and `fpga-describe-local-image-slots` to return the available FPGA image slots for the instance.
   
* **fpga-clear-local-image**
   * Clears the specified FPGA image slot, including FPGA internal and external memories that are used by the slot. The *fpga-image-slot* parameter is a logical index that represents a given FPGA within an instance.  Use `fpga-describe-local-image` to return the FPGA image status, and `fpga-describe-local-image-slots` to return the available FPGA image slots for the instance.

**All of the Amazon FPGA Image Management Tools support a *`-help`* option that may be used to display the full set of options.**

## Installs or updates to the Amazon FPGA Image Management Tools

The tools come pre-installed in `/usr/bin` for Amazon Linux, version 2016.09 or later.

Alternatively, the tools can be downloaded and installed from AWS SDK/HDK github repository [aws-fpga](https://github.com/aws/aws-fpga)

    $ git clone https://github.com/aws/aws-fpga
    $ cd aws-fpga
    $ source sdk_setup.sh
	$ cd sdk
	$ sdk_install.sh
    
The `sdk_install.sh` script will build the AFI management tools and install them in `/usr/bin`.

## Quickstart

Once you have the AFI Management Tools in your F1 instance, you can display the logical FPGA slot numbers and PCIe mappings for driver attachment (e.g. PCI Domain:Bus:Device:Function).

#### Getting inventory of the available FPGA
```
fpga-describe-local-image-slots -H

Type  FpgaImageSlot VendorId    DeviceId     DBDF
AFIDEVICE     0     0x1d0f      0x1042    0000:00:17.0
AFIDEVICE     1     0x1d0f      0x1042    0000:00:18.0
AFIDEVICE     2     0x1d0f      0x1042    0000:00:19.0
AFIDEVICE     3     0x1d0f      0x1042    0000:00:1a.0
AFIDEVICE     4     0x1d0f      0x1042    0000:00:1b.0
AFIDEVICE     5     0x1d0f      0x1042    0000:00:1c.0
AFIDEVICE     6     0x1d0f      0x1042    0000:00:1d.0
AFIDEVICE     7     0x1d0f      0x1042    0000:00:1e.0
```

* *The list displayed above is for F1.16xl instance that have 8 FPGAs on slot 0 through 7*

*  *The VendorId is the PCIe Configuration space Vendor ID, with 0x1d0f representing the Amazon registered PCIe Vendor ID. The developer can choose the Vendor ID for his/her own AFIs*

*  *The DeviceId is the PCIe Configuration space Device ID, with 0x1042 being the default*

*  *The DBDF is the common PCIe bus topology representation representation the Domain:Bus#:Device#:Function#*

** NOTE: ** *While each FPGA has more than one PCIe Physical Function, the AFI management tools will present the VendorId and DeviceId of the first PF only*

#### Describing the AFI content loaded on a specific FPGA slot

The next command displays the current state for the given FPGA logical slot number.  Shows the FPGA in the “cleared” state right after instance create.

```
fpga-describe-local-image -S 0 -H

Type    FpgaImageSlot    FpgaImageId    StatusName    StatusCode
AFI           0             none          cleared         1
Type        VendorId    DeviceId      DBDF
AFIDEVICE    0x1d0f      0x1042    0000:00:17.0
```

#### Loading an AFI to a specific FPGA slot

To load the AFI, use the FPGA logical slot number and Amazon Global FPGA Image parameters (see FAQ for AGFI).

```
fpga-load-local-image -S 0 -I agfi-004f34c45ed4e9603
```

#### Describing the AFI content loaded on a specific FPGA slot after load

Displays the current state for the given FPGA logical slot number.  Shows the FPGA in the “loaded” state after the FPGA image "load" operation.

```
fpga-describe-local-image -S 0 -H

Type    FpgaImageSlot    FpgaImageId          StatusName    StatusCode
AFI           0       agfi-004f34c45ed4e9603    loaded          0
Type        VendorId    DeviceId      DBDF
AFIDEVICE    0x1d0f      0x1042    0000:00:17.0
```

#### Clearing the FPGA image on specific slot

The next command will clear the FPGA image, including internal and external memories.

```
fpga-clear-local-image -S 0
```

#### Describing the AFI content loaded on a specific FPGA slot after clear

Displays the current state for the given FPGA logical slot number. It shows the FPGA in the “cleared” state after the FPGA image "clear" operation.

```
fpga-describe-local-image -S 0 -H

Type    FpgaImageSlot    FpgaImageId    StatusName    StatusCode
AFI           0              none         cleared         1
Type        VendorId    DeviceId      DBDF
AFIDEVICE    0x1d0f      0x1042    0000:00:17.0
```

#### Looking at metrics

The `fpga-describe-local-image` **`metrics`** option may be used to display FPGA image hardware metrics including FPGA PCI and DDR ECC Metrics.

Additionally, the `fpga-describe-local-image` **`clear-metrics`** option may be used to display and clear FPGA image hardware metrics (clear on read).

 
## fpga-describe-local-image **metrics** option

The following FPGA image hardware metrics are provided. PCIe related counters have `ps` or `pm` prefix indicated a PCIe slave access (Instance CPU or other FPGAs accessing this FPGA) or PCIe master access (The FPGA is mastering and outbound transaction toward the instance memory or other FPGAs).

* ps-timeout-count (32-bit)
  * The CustomLogic (CL) did not respond to memory-mapped I/O (MMIO) read access from the instance. In most cases this indicated a design flaw in the AFI.

* ps-timeout-addr (64-bit)
  * The first address that triggered a `ps-timeout-count` event. This is a relative address as the upper bits of the address matching the PCIe BAR are set to zero.

* pm-range-error-count (32-bit)
   * The CustomLogic (CL) trying to initiate outbound Read/Write (PCI master) to instance memory space or other FPGAs on the PCIe fabric, but has illegal address  
   
* pm-range-error-addr (64-bit)
   * The first address that triggered a `pm-range-error-count` event. 

* pm-len-error-count (32-bit)
   * The CustomLogic violated AXI-4 protocol/length (Refer to [AWS Shell Interface Specification](https://github.com/aws/aws-fpga/hdk/docs/AWS_Shell_Interface_Specifications.md))
   
* pm-len-error-addr (64-bit)
   * The first address that triggered a `pm-len-error-count` event.

* pm-write-count (64-bit)
    * The number of Doublewords/DW (4 Bytes) data written by the AFI toward the instance memory or other FPGAs. DW with partial byte-enable bit-vector is still counted as whole DW in this counter. This counter will not increment when any of the `pm-???-error-count` events happen.
    
* pm-read-count (64-bit)
    * The number of Doublewords/DW (4 Bytes) data read by the AFI from the instance memory or other FPGAs. DW with partial byte-enable bit-vector is still counted as whole DW in this counter. This counter will not increment when any of the `pm-???-error-count` events happen.
    
* DDR-A
   * write-count (64-bit), counting the number of bus-beats (512-bit or 64Bytes) on the DRAM controller interface.
   * read-count (64-bit), counting the number of bus-beats (512-bit or 64Bytes) on the DRAM controller interface.

* Repeated for DDR B,C,D

## FAQ

* **Q: What is the Amazon Global FPGA Image Id (AGFI)?**
   * The AGFI is an AWS globally unique identifier that is used to reference a specific Amazon FPGA Image (AFI).
   * In the examples, `agfi-004f34c45ed4e9603` is specified in the `fpga-load-local-image` command in order to load a specific AFI
into the given fpga-image-slot.   

* **Q: What is a fpga-image-slot?**
   * The fpga-image-slot is a logical index that represents a given FPGA within an instance.  Use `fpga-describe-local-image-slots` to return the available FPGA image slots for the instance.

* **Q: What are the Vendor and Device IDs listed in the `fpga-describe-local-image-slots` and `fpga-describe-local-image` output?**
   * The VendorId and DeviceId represent the unique identifiers for a PCI device as seen in the PCI Configureation Header Space.  These identifiers are typically used by device drivers to know which devices to attach to.  The identifiers are assigned by PCI-SIG. You can use Amazon's default DeviceId, or use your own during the `createFpgaImage` EC2 call.

* **Q: What is a DBDF?**
   * A DBDF is simply an acronym for Domain:Bus:Device.Function (also see PF). 

* **Q: What is a PF?**
   * A PF refers to a PCI Physical Function that is exposed by the FPGA hardware.  For example, it is accessable by user-space programs via the sysfs filesystem in the path `/sys/bus/pci/devices/Domain:Bus:Device.Function`.  The `Domain:Bus:Device.Function` syntax is the same as returned from `lspci` program output.  Examples: **FPGA application PF** `0000:00:17.0`, **FPGA management PF** `0000:00:17.1`.  

* **Q: What is a BAR?**
   * A PCI Base Address Register (BAR) specifies the memory region where FPGA memory space may be accessed by an external entity (like the instance CPU or other FPGAs).  Multiple BARs may be supported by a given PCI device.  In this FAQ section (also see PF), BAR0 from a device may be accessed (for example) by opening and memory mapping the resource0 sysfs file in the path `/sys/bus/pci/devices/Domain:Bus:Device.Function/resource0`.  Once BAR0 has been memory mapped, the BAR0 registers may be accessed through a pointer to the memory mapped region (refer to the open and mmap system calls).
   
* **Q: What is the AFIDEVICE and how is it used?**
   * Within the `fpga-describe-local-image-slots` and `fpga-describe-local-image` commands the AFIDEVICE represents the PCI PF that is used to communicate with the AFI.  The AFIDEVICE functionality exposed through the PF is dependent on the AFI that is loaded via the `fpga-load-local-image` command.  For example, DMA and/or memory-mapped IO (MMIO) may be supported depending on the loaded AFI, which is then used to communicate with the AFI in order to perform an accelerated application-dependent task within the FPGA.  User-space applications may access the AFIDEVICE PF through sysfs as is noted above in this FAQ section (also see PF).

* **Q: How do the AFI Management Tools work?**
   * Though most customers dont have to understand the internals of the tools, a short overview is provided here:
   * Within the F1 instance, the FPGAs expose a management PF (e.g. `0000:00:17.1`) that is used for control channel communication between the instance and AWS.
   * The FPGA management PF BAR0 is **reserved** for this communication path.
   * The FPGA application drivers **should not** access the FPGA management PF BAR0.
   * The Amazon FPGA Image Management Tools memory map the FPGA management PF BAR0 and communicate with AWS using internally defined messages and hardware registers.
   * For more information on the Amazon FPGA Image Mangement Tool software and FPGA hardware see [aws-fpga](https://github.com/aws/aws-fpga).

* **Q: Can the AFI Management Tools work concurently on multiple FPGA image slots?**
   * The tools can be executed on multiple FPGAs concurrently.  This may be done without synchronization between processes that are using the tools.
   
* **Q: Can the AFI Management Tools work concurrently from multiple processes on the same FPGA?**
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
