# Amazon FPGA Image (AFI) Management Tools

AWS provides the following set of command-line tools for managing Amazon FPGA Images (AFIs) on FPGA-enabled EC2 instances (e.g., F2). **The tools currently support Linux Instances only and require `sudo` privileges.**

## Quick Reference

The FPGA management tools are automatically installed when you source the SDK.

```bash
git clone https://github.com/aws/aws-fpga.git
cd aws-fpga
source sdk_setup.sh  # Installs tools to /usr/bin
```

### Essential Commands

```bash
# List available FPGA slots
sudo fpga-describe-local-image-slots

# Load AFI to slot 0
sudo fpga-load-local-image -S 0 -I agfi-0123456789abcdef0

# Check AFI status
sudo fpga-describe-local-image -S 0

# Clear AFI from slot 0
sudo fpga-clear-local-image -S 0
```

### Command Reference Table

| Command | Purpose | Key Parameters |
|---------|---------|----------------|
| `fpga-describe-local-image-slots` | List FPGA slots and PCIe mappings | `-H` (human readable) |
| `fpga-load-local-image` | Load AFI to specified slot and returns slot status | `-S <slot>` `-I <agfi-id>` `-A` (async) |
| `fpga-describe-local-image` | Get AFI status for a slot | `-S <slot>` `-R` (rescan) `-H` (human readable) |
| `fpga-clear-local-image` | Clear AFI from slot (includes internal & external FPGA memories) | `-S <slot>` `-A` (async) |
| `fpga-start-virtual-jtag` | Start JTAG debug server described in [Virtual JTAG Guide](../../../hdk/docs/Virtual_JTAG_XVC.md) | `-S <slot>` `-P <port>` |
| `fpga-get-virtual-led` | Read virtual LED states in binary bit-map | `-S <slot>` |
| `fpga-set-virtual-dip-switch` | Set virtual DIP switches in binary bit-map | `-S <slot>` `-D <value>` |
| `fpga-get-virtual-dip-switch` | Read virtual DIP switches in binary bit-map | `-S <slot>` |

### Clock Management Commands

If the design loaded onto the FPGA does not have the clkgen IP, error clkgen-ip-not-found will be returned. MMCMs that are not specified in `load` commands will be set to the default recipes.

| Command | Purpose | Key Parameters |
|---------|---------|----------------|
| `fpga-describe-clkgen` | Returns the currently loaded frequencies in MHz for each clock in each MMCM | `-S <slot>` |
| `fpga-load-clkgen-dynamic` | Loads a frequency into the first clock of each specified MMCMs and returns the current frequencies in MHz  | `-S <slot>` `-A <freq>` `-B <freq>` `-C <freq>` |
| `fpga-load-clkgen-recipe` | Loads a clkgen recipe into the specified clocking groups and returns the current frequencies in MHz  | `-S <slot>` `-A <recipe>` `-B <recipe>` `-C <recipe>` |

**Note:** Clock commands require AFI with clkgen IP. Returns `clkgen-ip-not-found` error if not available.

## Key Concepts

### FPGA Image Slots - Getting Inventory of the Available FPGA Slots

- Index representing a specific FPGA within an instance to pass to the `-S` argument to various commands
- Use `fpga-describe-local-image-slots` to see available slots
- F2.6xlarge has 1 slot (0), F2.48xlarge has 8 slots (0-7 shown in the example below)

```bash
sudo fpga-describe-local-image-slots -H

   ...

   Type  FpgaImageSlot  VendorId    DeviceId    DBDF
   AFIDEVICE    0       0x1d0f      0x9048      0000:9f:00.0
   Type  FpgaImageSlot  VendorId    DeviceId    DBDF
   AFIDEVICE    1       0x1d0f      0x9048      0000:a1:00.0
   Type  FpgaImageSlot  VendorId    DeviceId    DBDF
   AFIDEVICE    2       0x1d0f      0x9048      0000:a3:00.0
   Type  FpgaImageSlot  VendorId    DeviceId    DBDF
   AFIDEVICE    3       0x1d0f      0x9048      0000:a5:00.0
   Type  FpgaImageSlot  VendorId    DeviceId    DBDF
   AFIDEVICE    4       0x1d0f      0x9048      0000:ae:00.0
   Type  FpgaImageSlot  VendorId    DeviceId    DBDF
   AFIDEVICE    5       0x1d0f      0x9048      0000:b0:00.0
   Type  FpgaImageSlot  VendorId    DeviceId    DBDF
   AFIDEVICE    6       0x1d0f      0x9048      0000:b2:00.0
   Type  FpgaImageSlot  VendorId    DeviceId    DBDF
   AFIDEVICE    7       0x1d0f      0x9048      0000:b4:00.0
```

**NOTE:** *While each FPGA has more than one PCIe Physical Function, the AFI Management Tools will present the VendorId and DeviceId of the first PF only*.

### Describing the AFI Content Loaded on a Specific FPGA Slot

The output shows that the FPGA in the “cleared” state right after instance launch or after `fpga-clear-local-image`.

```bash
sudo fpga-describe-local-image -S 0 -H

   ...

   Type  FpgaImageSlot  FpgaImageId             StatusName    StatusCode   ErrorName    ErrorCode   ShVersion
   AFI          0       No AFI                  cleared           1        ok               0       <shell version>
   Type  FpgaImageSlot  VendorId    DeviceId    DBDF
   AFIDEVICE    0       0x1d0f      0x9048      0000:34:00.0
```

### Amazon Global FPGA Image ID (AGFI)

- Globally unique identifier for AFIs (e.g., `agfi-0123456789abcdef0`)
- Different from regional AFI IDs used in AWS APIs
- Same AGFI works across all AWS regions

### PCIe Device Information

The developer can choose the Vendor and Device IDs for their own AFIs by following the [HDK section on AFI PCIe IDs](../../../hdk/README.md#afi-pcie-ids).

- **VendorId**: The PCIe Configuration space Vendor ID, with 0x1d0f representing the Amazon registered PCIe Vendor ID
- **DeviceId**: The PCIe Configuration space Device ID, with 0x9048 being the default
- **DBDF**: The common PCIe bus topology representing the Domain:Bus:Device.Function PCIe address
- **BAR**: Base Address Register for memory-mapped access

## Usage Patterns

### Synchronous Operations (Default)

Commands wait for completion and perform automatic PCIe rescan:

```bash
# Waits for AFI to load, then rescans PCIe bus
$ sudo fpga-load-local-image -S 0 -I agfi-0123456789abcdef0 -H
Type  FpgaImageSlot  FpgaImageId             StatusName    StatusCode   ErrorName    ErrorCode   ShVersion
AFI          0       agfi-0123456789abcdef0  loaded            0        ok               0       <shell version>
Type  FpgaImageSlot  VendorId    DeviceId    DBDF
AFIDEVICE    0       0x6789      0x1d50      0000:34:00.0
```

### Asynchronous Operations

Use `-A` flag for non-blocking operations:

```bash
sudo fpga-load-local-image -S 0 -I agfi-0123456789abcdef0 -A
# Returns immediately, check status separately
sudo fpga-describe-local-image -S 0 -R  # -R rescans PCIe bus
```

### Multi-FPGA Operations

Commands can target different slots simultaneously:

```bash
# Load same AFI to multiple slots
sudo fpga-load-local-image -S 0 -I agfi-0123456789abcdef0 &
sudo fpga-load-local-image -S 1 -I agfi-0123456789abcdef0 &
wait
```

## FAQ

### What do I do if my AFI fails to load, hangs, or my commands time out?

- Verify your AGFI ID is correct with `aws ec2 describe-fpga-images`
- Ensure AFI is compatible with current shell version
- Check instance has F2 FPGA slots: `sudo fpga-describe-local-image-slots`
- Wait 15-30 seconds and retry
- Check `dmesg` for kernel messages (`sudo dmesg | tail -20`)
- All commands require `sudo` privileges
- Tools access `/dev/kmsg` and PCIe sysfs files

### What do I do if my PCIe device is not visible?

- Use `-R` flag with `fpga-describe-local-image` to rescan
- Verify AFI loaded successfully before accessing device
- Check for Amazon PCIe devices with `lspci | grep -i amazon`

### What is the Amazon Global FPGA Image ID (AGFI)?

- The AGFI is an AWS **globally** unique identifier that is used to reference a specific Amazon FPGA Image (AFI). Please learn more in the [Amazon FPGA Images (AFIs) Guide](./../../../hdk/docs/Amazon_FPGA_Images_Afis_Guide.md)

### What is an `fpga-image-slot`?

- The fpga-image-slot is an index that represents a given FPGA within an instance.  Use `fpga-describe-local-image-slots` to return the available FPGA image slots for the instance.

### What are the Vendor and Device IDs listed in the `fpga-describe-local-image-slots` and `fpga-describe-local-image` output?

- The VendorId and DeviceId represent the unique identifiers for a PCI device as seen in the PCI Configuration Header Space.  These identifiers are typically used by device drivers to know which devices to attach to.  The identifiers are assigned by PCI-SIG. You can use Amazon's default DeviceId, or use your own during the `CreateFpgaImage` EC2 API.

### What is a PF?

- A PF refers to a PCI Physical Function that is exposed by the FPGA hardware.  For example, it is accessible by a user-space programs via the sysfs filesystem in the path `/sys/bus/pci/devices/Domain:Bus:Device.Function`.  The `Domain:Bus:Device.Function` syntax is the same as returned from `lspci` program output.  Examples: **FPGA application PF** `0000:34:00.0`, **FPGA management PF** `0000:34:00.1`.

### What is a BAR?

- A PCI Base Address Register (BAR) specifies the memory region where FPGA memory space may be accessed by an external entity (like the instance CPU or other FPGAs).  Multiple BARs may be supported by a given PCI device.  In this FAQ section (also see PF), BAR0 from a device may be accessed (for example) by opening and memory mapping the resource0 sysfs file in the path `/sys/bus/pci/devices/Domain:Bus:Device.Function/resource0`.  Once BAR0 has been memory mapped, the BAR0 registers may be accessed through a pointer to the memory mapped region (refer to the open and mmap system calls).

### What is the AFIDEVICE and how is it used?

- Within the `fpga-describe-local-image-slots` and `fpga-describe-local-image` commands the AFIDEVICE represents the PCI PF that is used to communicate with the AFI.  The AFIDEVICE functionality exposed through the PF is dependent on the AFI that is loaded via the `fpga-load-local-image` command.  For example, DMA and/or memory-mapped IO (MMIO) may be supported depending on the loaded AFI, which is then used to communicate with the AFI in order to perform an accelerated application-dependent task within the FPGA.  User-space applications may access the AFIDEVICE PF through sysfs as is noted above in this FAQ section (also see PF).

### How do the AFI Management Tools work?

- Within the F2 instance, the FPGAs expose a management PF (e.g. `0000:34:00.1`) that is used for control channel communication between the instance and AWS.
- The FPGA management PF BAR0 is **reserved** for this communication path.
- The FPGA application drivers **should not** access the FPGA management PF BAR0.
- The AFI Management Tools memory map the FPGA management PF BAR0 and communicate with AWS using internally defined messages and hardware registers.
- The Amazon FPGA Image Tools require `sudo` or `root` access level since AFI loads and clears are modifying the underlying system hardware.
- `sudo` or `root` privilege is also required since the tools access the sysfs PCI subsystem and `/dev/kmsg` for `dmesg` logging.

### Can the AFI Management Tools work concurently on multiple FPGA image slots?

- The tools can be executed on multiple FPGAs concurrently.  This may be done without synchronization between processes that are using the tools.

### Can the AFI Management Tools work concurrently from multiple processes on the same FPGA?

- Without synchronization between processes, the tools should only be executed as one worker process per FPGA (highest level of concurrency), or one worker process across all FPGAs (least level of concurrency).
- Multiple concurrent process access to the tools using the same FPGA without proper synchronization between processes will cause response timeouts, and other indeterminate results.

### What is an afi-power-violation?

- The F2 system can only reliably provide a certain amount of power to the FPGA. If an AFI consumes more than this amount of power, the F2 system will disable the input clocks to the AFI. For more information on preventing, detecting, and recovering from this state, see AFI power guide (COMING SOON)

### How can I reset the AFI?

- The AFI may be reset (reloaded) via fpga-load-local-image, and/or reset back to a fully clean slate via `fpga-clear-local-image` and `fpga-load-local-image`.

### Where can I reach out for additional help?

- For any issues with the devkit documentation or code, please open a [GitHub issue](https://github.com/aws/aws-fpga/issues) with all steps to reproduce.
- For questions about F2 instances, please open a [re:Post issue with the 'FPGA Development' tag](https://repost.aws/tags/TAc7ofO5tbQRO57aX1lBYbjA/fpga-development).

## Related Documentation

- AWS FPGA SDK/HDK on [aws-fpga GitHub](https://github.com/aws/aws-fpga)
- [C API Examples](../fpga_mgmt_examples/README.md) - Programmatic AFI management
- [Python Bindings](../cython_bindings/README.md) - Python interface
- [Virtual JTAG Guide](../../../hdk/docs/Virtual_JTAG_XVC.md) - Debug setup
- [Clock Recipes Guide](../../../hdk/docs/Clock_Recipes_User_Guide.md) - Clock configuration

### AWS EC2 References

- [AWS EC2 Getting Started](https://aws.amazon.com/ec2/getting-started/)
- [AWS EC2 Instance Types](https://aws.amazon.com/ec2/instance-types/)
- [AWS EC2 User Guide](http://docs.aws.amazon.com/AWSEC2/latest/UserGuide/concepts.html)
- [AWS EC2 Networking and Security](http://docs.aws.amazon.com/AWSEC2/latest/UserGuide/EC2_Network_and_Security.html)
- [AWS EC2 Key Pairs](http://docs.aws.amazon.com/AWSEC2/latest/UserGuide/ec2-key-pairs.html)
- [AWS EC2 Attach EBS Volume](http://docs.aws.amazon.com/AWSEC2/latest/UserGuide/ebs-attaching-volume.html)
- [AWS EC2 Troubleshooting](http://docs.aws.amazon.com/AWSEC2/latest/UserGuide/ec2-instance-troubleshoot.html)
