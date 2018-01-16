# Amazon FPGA Image (AFI) Management Tools

AWS provides the following set of command-line tools for Amazon FPGA Image (AFI) management while running on an FPGA-enabled EC2 instance (e.g., F1). **The tools currently support Linux Instances only.**

* **`fpga-describe-local-image-slots`**
   * Returns the FPGA image slot numbers and device mappings to use for the `fpga-load-local-image`, `fpga-clear-local-image`, and `fpga-describe-local-image` commands.
   
* **`fpga-describe-local-image`**
   * Returns the status of the FPGA image for a specified FPGA image slot number. The *fpga-image-slot* parameter is an index that represents a given FPGA within an instance.  Use `fpga-describe-local-image-slots` to return the available FPGA image slots for the instance.
   
* **`fpga-load-local-image`**
   * Loads the specified FPGA image to the specified slot number, and returns the status of the command. The *fpga-image-slot* parameter is an index that represents a given FPGA within an instance.  Use `fpga-describe-local-image` to return the FPGA image status, and `fpga-describe-local-image-slots` to return the available FPGA image slots for the instance.
   
* **`fpga-clear-local-image`**
   * Clears the specified FPGA image slot, including FPGA internal and external memories that are used by the slot. The *fpga-image-slot* parameter is an index that represents a given FPGA within an instance.  Use `fpga-describe-local-image` to return the FPGA image status, and `fpga-describe-local-image-slots` to return the available FPGA image slots for the instance.
   
* **`fpga-start-virtual-jtag`**
   * Starts a Virtual JTAG XVC server, to debug tools like Vivado Lab Edition Hardware Manager to access debug cores inside the AFI. Please refer to [Virtual JTAG userguide](../../../hdk/docs/Virtual_JTAG_XVC.md).
   
* **`fpga-get-virtual-led`**
   * Returns a bit-map representating the state (1/0) the Virtual LEDs exposed by the Custom Logic (CL) part of the AFI.

* **`fpga-get-virtual-dip-switch`**
   * Returns a bit-map representing the current setting for the Virtual DIP Switches that drives the Custom Logic (CL) part of the AFI.
   
* **`fpga-set-virtual-dip-switch`**
   * Takes bit-map (in binary representation) to set for the  Virtual DIP Switches that drives the Custom Logic (CL) part of the AFI.
   

All of the AFI Management Tools support a `-help` option that may be used to display the full set of options.

### `sudo` or `root` Privileges

The tools require sudo or root access rights since AFI loads and clears modify the underlying system hardware (also see the FAQ section "Q: How do the AFI Management Tools work?".

## Installs or Updates to the AFI Management Tools

The tools come pre-installed in `/usr/bin` for Amazon Linux, version 2016.09 or later.

Alternatively, the tools can be downloaded and installed from AWS SDK/HDK GitHub repository [aws-fpga](https://github.com/aws/aws-fpga), as follows:

    $ git clone https://github.com/aws/aws-fpga
    $ cd aws-fpga
    $ source sdk_setup.sh
    
The `sdk_setup.sh` script will build the AFI Management Tools and install them in `/usr/bin`.

## Quickstart

Once you have the AFI Management Tools installed on your F1 instance, you can display the FPGA slot numbers and PCIe mappings for driver attachment (e.g., PCI Domain:Bus:Device:Function).

### Getting Inventory of the Available FPGA Slots

    $ sudo fpga-describe-local-image-slots -H

    Type  FpgaImageSlot  VendorId    DeviceId    DBDF
    AFIDEVICE    0       0x1d0f      0x1042      0000:00:0f.0
    AFIDEVICE    1       0x1d0f      0x1042      0000:00:11.0
    AFIDEVICE    2       0x1d0f      0x1042      0000:00:13.0
    AFIDEVICE    3       0x1d0f      0x1042      0000:00:15.0
    AFIDEVICE    4       0x1d0f      0x1042      0000:00:17.0
    AFIDEVICE    5       0x1d0f      0x1042      0000:00:19.0
    AFIDEVICE    6       0x1d0f      0x1042      0000:00:1b.0
    AFIDEVICE    7       0x1d0f      0x1042      0000:00:1d.0

* The above list displayed the slots in an F1.16xl instance that has 8 FPGAs on slot 0 through 7.

* The VendorId is the PCIe Configuration space Vendor ID, with 0x1d0f representing the Amazon registered PCIe Vendor ID. The developer can choose the Vendor ID for their own AFIs.

* The DeviceId is the PCIe Configuration space Device ID, with 0x1042 being the default.

* The DBDF is the common PCIe bus topology representating the Domain:Bus#:Device#:Function#.

** NOTE: ** *While each FPGA has more than one PCIe Physical Function, the AFI Management Tools will present the VendorId and DeviceId of the first PF only*.

### Describing the AFI Content Loaded on a Specific FPGA Slot

The following command displays the current state for the given FPGA slot number.  The output shows that the FPGA in the “cleared” state right after instance create.

    $ sudo fpga-describe-local-image -S 0 -H

    Type  FpgaImageSlot  FpgaImageId             StatusName    StatusCode   ErrorName    ErrorCode   ShVersion
    AFI          0       none                    cleared           1        ok               0       <shell version> 
    Type  FpgaImageSlot  VendorId    DeviceId    DBDF
    AFIDEVICE    0       0x1d0f      0x1042      0000:00:0f.0

### Synchronous AFI Load and Clear Operations
#### Synchronously Loading an AFI to a Specific FPGA Slot

To load the AFI, use the FPGA slot number and Amazon Global FPGA Image ID parameters (see FAQ for AGFI).  In synchronous mode, this command will wait for the AFI to transition to the "loaded" state, perform a PCI device remove and recan in order to expose the unique AFI Vendor and Device Id, and display the final state for the given FPGA slot number.

    $ sudo fpga-load-local-image -S 0 -I agfi-0123456789abcdefg -H
    
    Type  FpgaImageSlot  FpgaImageId             StatusName    StatusCode   ErrorName    ErrorCode   ShVersion
    AFI          0       agfi-0123456789abcdefg  loaded            0        ok               0       <shell version> 
    Type  FpgaImageSlot  VendorId    DeviceId    DBDF
    AFIDEVICE    0       0x6789      0x1d50      0000:00:0f.0
    
#### Synchronously Clearing the FPGA Image on Specific Slot

The following command will clear the FPGA image, including internal and external memories.  In synchronous mode, this command will wait for the AFI to transition to the "cleared" state, perform a PCI device remove and recan in order to expose the default AFI Vendor and Device Id, and display the final state for the given FPGA slot number.

    $ sudo fpga-clear-local-image -S 0 -H
    
    Type  FpgaImageSlot  FpgaImageId             StatusName    StatusCode   ErrorName    ErrorCode   ShVersion
    AFI          0       none                    cleared           1        ok               0       <shell version> 
    Type  FpgaImageSlot  VendorId    DeviceId    DBDF
    AFIDEVICE    0       0x1d0f      0x1042      0000:00:0f.0

### Asynchronous AFI Load and Clear Operations
#### Asynchronously Loading an AFI to a Specific FPGA Slot

To load the AFI, use the FPGA slot number and Amazon Global FPGA Image ID parameters (see FAQ for AGFI). The "-A" is used for asynchronous AFI load operations.

    $ sudo fpga-load-local-image -S 0 -I agfi-0123456789abcdefg -A

#### Describing the AFI content loaded on a specific FPGA slot after an asynchronous AFI load

Displays the current state for the given FPGA slot number.  The output shows the FPGA in the “loaded” state after the FPGA image "load" operation.  **_The "-R" option performs a PCI device remove and recan in order to expose the unique AFI Vendor and Device Id._**

    $ sudo fpga-describe-local-image -S 0 -R -H 
    
    Type  FpgaImageSlot  FpgaImageId             StatusName    StatusCode   ErrorName    ErrorCode   ShVersion
    AFI          0       agfi-0123456789abcdefg  loaded            0        ok               0       <shell version> 
    Type  FpgaImageSlot  VendorId    DeviceId    DBDF
    AFIDEVICE    0       0x6789      0x1d50      0000:00:0f.0

#### Asynchronously Clearing the FPGA Image on Specific Slot

The following command will clear the FPGA image, including internal and external memories. The "-A" is used for asynchronous AFI clear operations.

    $ sudo fpga-clear-local-image -S 0 -A

#### Describing the AFI content loaded on a specific FPGA slot after an asynchronous AFI clear

The following command displays the current state for the given FPGA slot number. It shows that the FPGA is in the “cleared” state after the FPGA image "clear" operation.  **_The "-R" option performs a PCI device remove and recan in order to expose the default AFI Vendor and Device Id._**

    $ sudo fpga-describe-local-image -S 0 -R -H
    
    Type  FpgaImageSlot  FpgaImageId             StatusName    StatusCode   ErrorName    ErrorCode   ShVersion
    AFI          0       none                    cleared           1        ok               0       <shell version> 
    Type  FpgaImageSlot  VendorId    DeviceId    DBDF
    AFIDEVICE    0       0x1d0f      0x1042      0000:00:0f.0

### Looking at Metrics

The `fpga-describe-local-image` **`metrics`** option may be used to display FPGA image hardware metrics including FPGA PCI and DDR ECC metrics.

Additionally, the `fpga-describe-local-image` **`clear-metrics`** option may be used to display and clear FPGA image hardware metrics (clear on read).

#### Supported Metrics

The following FPGA image hardware metrics are provided. PCIe related counters contain the `pcis` or `pcim` prefix which indicates a PCIe slave access (the instance CPU or other FPGAs accessing this FPGA) or PCIe master access (the FPGA is mastering an outbound transaction toward the instance memory or other FPGAs).

* `sdacl-slave-timeout-count` (32-bit)
  * The CustomLogic (CL) did not respond to SDACL read access from the instance. In most cases this indicated a design flaw in the AFI.

* `sdacl-slave-timeout-addr` (32-bit)
  * The first address that triggered a `sdacl-slave-timeout-count` event. This is a relative address as the upper bits of the address matching the PCIe BAR are set to zero.

* `virtual-jtag-slave-timeout-count` (32-bit)
  * The CustomLogic (CL) did not respond to Virtual JTAG read access from the instance. In most cases this indicated a design flaw in the AFI.

* `virtual-jtag-slave-timeout-addr` (32-bit)
  * The first address that triggered a `virtual-jtag-slave-timeout-count` event. This is a relative address as the upper bits of the address matching the PCIe BAR are set to zero.

* `ocl-slave-timeout-count` (32-bit)
  * The CustomLogic (CL) did not respond to OCL read access from the instance. In most cases this indicated a design flaw in the AFI.

* `ocl-slave-timeout-addr` (64-bit)
  * The first address that triggered a `ocl-slave-timeout-count` event. This is a relative address as the upper bits of the address matching the PCIe BAR are set to zero.

* `bar1-slave-timeout-count` (32-bit)
  * The CustomLogic (CL) did not respond to BAR1 read access from the instance. In most cases this indicated a design flaw in the AFI.

* `bar1-slave-timeout-addr` (64-bit)
  * The first address that triggered a `bar1-slave-timeout-count` event. This is a relative address as the upper bits of the address matching the PCIe BAR are set to zero.

* `dma-pcis-timeout-count` (32-bit)
  * The CustomLogic (CL) did not respond to DMA read access from the instance. In most cases this indicated a design flaw in the AFI.

* `dma-pcis-timeout-addr` (64-bit)
  * The first address that triggered a `dma-pcis-timeout-count` event. This is a relative address as the upper bits of the address matching the PCIe BAR are set to zero.

* `pcim-axi-protocol-error-count` (32-bit)
   * The CustomLogic violated the AXI-4 protocol.  (Refer to [AWS Shell Interface Specifications](https://github.com/aws/aws-fpga/tree/master/hdk/docs))
   * Specific AXI-4 protocol violation status indicators are listed below: 
     * pcim-axi-protocol-4K-cross-error
       * AXI Requests on PCIM AXI bus crosses 4K boundary
     * pcim-axi-protocol-bus-master-enable-error
       * AXI Requests on PCIM AXI bus are initiated when PCIE bus-master-enable is not enabled
     * pcim-axi-protocol-request-size-error
       * PCIE Core request violates PCIE max-payload-size (writes) or max-read-req-size (reads). This error cannot be triggered by errors on the PCIM AXI bus
     * pcim-axi-protocol-write-incomplete-error
       * For AXI Write Requests on PCIM AXI bus, WLAST was asserted pre-maturely or WLAST was not asserted for the last wdata beat 
     * pcim-axi-protocol-first-byte-enable-error
       * AXI Requests on PCIM AXI bus has illegal first-byte-enable.
     * pcim-axi-protocol-last-byte-enable-error
       * AXI Requests on PCIM AXI bus has illegal last-byte-enable
     * pcim-axi-protocol-bready-error
       * For AXI Requests on PCIM AXI bus, timeout waiting for BREADY to be asserted by master (CL) after BVALID is asserted by the slave (SH)
     * pcim-axi-protocol-rready-error
       * For AXI Requests on PCIM AXI bus, timeout waiting for RREADY to be asserted by master (CL) after RVALID is asserted by the slave (SH)
     * pcim-axi-protocol-wchannel-error
       * For AXI Write Requests on PCIM AXI bus, timeout waiting for WVALID to be asserted by master (CL) 
   
* `pcim-axi-protocol-error-addr` (64-bit)
   * The first address that triggered a `pm-axi-protocol-error-count` event.

* `pcim-range-error-count` (32-bit)
   * The CustomLogic (CL) trying to initiate outbound Read/Write (PCI master) to instance memory space or other FPGAs on the PCIe fabric, but has illegal address  
   
* `pcim-range-error-addr` (64-bit)
   * The first address that triggered a `pcim-range-error-count` event. 

* `pcim-write-count` (64-bit)
    * The number of Doublewords/DW (4 Bytes) data written by the AFI toward the instance memory or other FPGAs. DW with partial byte-enable bit-vector is still counted as whole DW in this counter. This counter will not increment when any of the `pm-???-error-count` events happen.
    
* `pcim-read-count` (64-bit)
    * The number of Doublewords/DW (4 Bytes) data read by the AFI from the instance memory or other FPGAs. DW with partial byte-enable bit-vector is still counted as whole DW in this counter. This counter will not increment when any of the `pm-???-error-count` events happen.
    
* `DDR-A write-count` or `DDR-A read-count` (64-bit) (same for `DDR-B`, `DDR-C` or `DDR-D`)
   * Counting the number of bus-beats (512-bit or 64Bytes) on the DRAM controller interface.

* `Clock Group A Frequency ` (32-bit) (same for `Clock Group B` or `Clock Group C`)
   * The programmed frequency of each output clock, in Mhz rounded down. Programmed frequency in hz is available via the SDK. 

* `Power consumption (Vccint) - Last measured` (32-bit)
   * The measured power value of the Vccint power supply to the AFI in watts, updated every minute. Used to determine how close the AFI is to the maximum power draw.

* `Power consumption (Vccint) - Average` (32-bit)
   * The average measured power value of the Vccint power supply to the AFI in watts over the lifetime of the current AFI load. Updated every minute. Used to determine how close the AFI is to the maximum power draw.

* `Power consumption (Vccint) - Max measured` (32-bit)
   * The maximum sampled power value of the Vccint power supply to the AFI in watts, sampled frequently but updated every minute. The maximum is computed over the time the current AFI has been loaded, except that samples up to a minute after the AFI is first loaded are ignored. Max measured therefore does not include short term, on load power usage. Used to determine how close the AFI is to the maximum power draw.

## FAQ

* **Q: What is the Amazon Global FPGA Image ID (AGFI)?**
   * The AGFI is an AWS **globally** unique identifier that is used to reference a specific Amazon FPGA Image (AFI). 
   * It is used to refer to a specific AFI when using the FPGA Management tools from within an EC2 instance.
   * In the examples, `agfi-0123456789abcdefg` is specified in the `fpga-load-local-image` command in order to load a specific AFI
into the given `fpga-image-slot`.
   * AGFI IDs should not be confused with AFI IDs. The latter are **regional** IDs that are used to refer to a specific AFI when using the AWS EC2 APIs to create or manage and AFI. For example, when copying an AFI across regions, it will preserve the same AGFI ID, but get a new regional AFI ID.

* **Q: What is a `fpga-image-slot`?**
   * The fpga-image-slot is an index that represents a given FPGA within an instance.  Use `fpga-describe-local-image-slots` to return the available FPGA image slots for the instance.

* **Q: What are the Vendor and Device IDs listed in the `fpga-describe-local-image-slots` and `fpga-describe-local-image` output?**
   * The VendorId and DeviceId represent the unique identifiers for a PCI device as seen in the PCI Configuration Header Space.  These identifiers are typically used by device drivers to know which devices to attach to.  The identifiers are assigned by PCI-SIG. You can use Amazon's default DeviceId, or use your own during the `CreateFpgaImage` EC2 API.

* **Q: What is a DBDF?**
   * A DBDF is simply an acronym for Domain:Bus:Device.Function (also see PF). 

* **Q: What is a PF?**
   * A PF refers to a PCI Physical Function that is exposed by the FPGA hardware.  For example, it is accessible by a user-space programs via the sysfs filesystem in the path `/sys/bus/pci/devices/Domain:Bus:Device.Function`.  The `Domain:Bus:Device.Function` syntax is the same as returned from `lspci` program output.  Examples: **FPGA application PF** `0000:00:0f.0`, **FPGA management PF** `0000:00:10.0`.  

* **Q: What is a BAR?**
   * A PCI Base Address Register (BAR) specifies the memory region where FPGA memory space may be accessed by an external entity (like the instance CPU or other FPGAs).  Multiple BARs may be supported by a given PCI device.  In this FAQ section (also see PF), BAR0 from a device may be accessed (for example) by opening and memory mapping the resource0 sysfs file in the path `/sys/bus/pci/devices/Domain:Bus:Device.Function/resource0`.  Once BAR0 has been memory mapped, the BAR0 registers may be accessed through a pointer to the memory mapped region (refer to the open and mmap system calls).
   
* **Q: What is the AFIDEVICE and how is it used?**
   * Within the `fpga-describe-local-image-slots` and `fpga-describe-local-image` commands the AFIDEVICE represents the PCI PF that is used to communicate with the AFI.  The AFIDEVICE functionality exposed through the PF is dependent on the AFI that is loaded via the `fpga-load-local-image` command.  For example, DMA and/or memory-mapped IO (MMIO) may be supported depending on the loaded AFI, which is then used to communicate with the AFI in order to perform an accelerated application-dependent task within the FPGA.  User-space applications may access the AFIDEVICE PF through sysfs as is noted above in this FAQ section (also see PF).

* **Q: How do the AFI Management Tools work?**
   * Within the F1 instance, the FPGAs expose a management PF (e.g. `0000:00:10.0`) that is used for control channel communication between the instance and AWS.
   * The FPGA management PF BAR0 is **reserved** for this communication path.
   * The FPGA application drivers **should not** access the FPGA management PF BAR0.
   * The AFI Management Tools memory map the FPGA management PF BAR0 and communicate with AWS using internally defined messages and hardware registers.
   * The Amazon FPGA Image Tools require `sudo` or `root` access level since AFI loads and clears are modifying the underlying system hardware.
   * `sudo` or `root` privilege is also required since the tools access the sysfs PCI subsystem and `/dev/kmsg` for `dmesg` logging.

* **Q: Can the AFI Management Tools work concurently on multiple FPGA image slots?**
   * The tools can be executed on multiple FPGAs concurrently.  This may be done without synchronization between processes that are using the tools.
   
* **Q: Can the AFI Management Tools work concurrently from multiple processes on the same FPGA?**
   * Without synchronization between processes, the tools should only be executed as one worker process per FPGA (highest level of concurrency), or one worker process across all FPGAs (least level of concurrency).
   * Multiple concurrent process access to the tools using the same FPGA without proper synchronization between processes will cause response timeouts, and other indeterminate results. 
   
* **Q: What is an afi-power-violation?**
   * The F1 system can only reliably provide a certain amount of power to the FPGA. If an AFI consumes more than this amount of power, the F1 system will disable the input clocks to the AFI. For more information on preventing, detecting, and recovering from this state, see [F1 power guide](../../../hdk/docs/afi_power.md)

* **Q: How can I reset the AFI?**
   * The AFI may be reset (reloaded) via fpga-load-local-image, and/or reset back to a fully clean slate via `fpga-clear-local-image` and `fpga-load-local-image`.

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
