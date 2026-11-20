# XDMA Driver Installation Instructions

The XDMA kernel driver enables customers to interact with the optional high-performance DMA engine in the [XDMA Shell](./../../User_Guide_AWS_EC2_FPGA_Development_Kit.md#aws-shells) as well as user-defined interrupts on AWS EC2 F2 instances.
For more details about the driver, refer to the [XDMA driver page in Xilinx's DMA IP driver repository](https://github.com/Xilinx/dma_ip_drivers/tree/master/XDMA/linux-kernel).

## Prerequisites

- An AFI built with the XDMA Shell. Use `--mode xdma_shell` when building the CL, as described in the [HDK README](./../README.md). Designs built with the Small Shell have no DMA engine and do not use this driver.
- An Ubuntu or Rocky Linux F2 instance with `sudo` access and internet access. The install script downloads the driver source from GitHub and installs the kernel headers if they are missing.
- The XRT `xocl` driver must not be loaded. The XDMA and XOCL drivers cannot be installed on the same instance, so the script stops if `xocl` is loaded.

## Step 1: Find the Device ID of Your AFI

The driver only binds to FPGAs whose PCIe device ID it knows. Pass the device ID of your CL to the install script with `-d`. The device ID is the upper 16 bits of `CL_SH_ID0` in the CL's `cl_id_defines.vh`, written with a `0x` prefix:

| CL | `CL_SH_ID0` | Device ID |
|---|---|---|
| [cl_dram_hbm_dma](./../cl/examples/cl_dram_hbm_dma/README.md) | `32'hF001_1D0F` | `0xf001` |
| [cl_mem_perf](./../cl/examples/cl_mem_perf/README.md) | `32'hF004_1D0F` | `0xf004` |
| Your own CL | `32'hXXXX_1D0F` | `0xXXXX` |

You can also read the device ID from an FPGA after loading your AFI. It is the fourth field of the `AFIDEVICE` line:

```bash
$ sudo fpga-describe-local-image -S 0 -H
...
Type  FpgaImageSlot  VendorId    DeviceId    DBDF
AFIDEVICE    0       0x1d0f      0xf001      0000:35:00.0
```

## Step 2: Load the AFI

[Load your XDMA shell AFI onto the FPGAs](./Amazon_FPGA_Images_Afis_Guide.md). The driver creates its devices when it binds to an FPGA running a matching AFI, so load the AFI before verifying the install.

## Step 3: Install the Driver

Run [install_xdma_driver.sh](./../../developer_resources/runtime_ami_builder/scripts/install_xdma_driver.sh) with the device ID from Step 1:

```bash
$AWS_FPGA_REPO_DIR/developer_resources/runtime_ami_builder/scripts/install_xdma_driver.sh -d 0xf001
```

The script:

- Downloads the latest Xilinx driver source, from the `master` branch, to a temporary directory. The script never uses or changes an existing `~/dma_ip_drivers`. If the `master` source can't be used, because its device table layout changed or it fails to build, the script tries once more with commit `a918c5196a09f95756af244a607d543d9dce5bfb`, the last upstream commit known to work.
- Adds your device ID to the driver's PCIe device table, unless it's already there. The table already includes the AWS device IDs `0xf000` and `0xf001`, so the driver always binds to those.
- Builds and installs the driver for the running kernel, loads it with `modprobe xdma`, and removes the temporary directory. If an older XDMA driver is already loaded, the script unloads it first, and stops if something is still using it.

The `-d` option is required, and the device ID must be a 4-digit hex value with the `0x` prefix, such as `0xf001`. The script stops with an error otherwise. Passing `-d 0x0000` only prepares the source in `~/dma_ip_drivers/XDMA/linux-kernel/xdma/` without building it, and prints the manual steps to finish the install. If `~/dma_ip_drivers` already exists from an earlier `-d 0x0000` run, the script updates it to the latest source and discards any changes in it. The [Runtime AMI Builder](./../../developer_resources/runtime_ami_builder/README.md#xdma-driver-installation) uses this to build AMIs before the device ID is known.

## Step 4: Verify the Install

Check that the driver is loaded:

```bash
$ lsmod | grep xdma
xdma                   86016  0
```

Check that the driver is bound to the FPGA:

```bash
$  lspci -vvs 35:00.0
35:00.0 Memory controller: Amazon.com, Inc. Device f001
Subsystem: Device fedc:1d51
Physical Slot: 3-1
Control: I/O- Mem+ BusMaster+ SpecCycle- MemWINV- VGASnoop- ParErr- Stepping- SERR- FastB2B- DisINTx-
Status: Cap+ 66MHz- UDF- FastB2B- ParErr- DEVSEL=fast >TAbort- <TAbort- <MAbort- >SERR- <PERR- INTx-
Latency: 0
NUMA node: 0
Region 0: Memory at 5004c000000 (64-bit, prefetchable) [size=64M]
Region 2: Memory at 50048200000 (64-bit, prefetchable) [size=64K]
Region 4: Memory at 52000000000 (64-bit, prefetchable) [size=128G]
Capabilities: <access denied>
Kernel driver in use: xdma    <--- The XDMA driver has been correctly bound to the card
```

When the driver is bound, it creates its devices in `/sys/class/xdma/`, with matching device files in `/dev/`:

```bash
$ ls /sys/class/xdma
xdma0_bypass        xdma0_c2h_0     xdma0_events_1   xdma0_events_12  xdma0_events_15  xdma0_events_4  xdma0_events_7  xdma0_h2c_0
xdma0_bypass_c2h_0  xdma0_control   xdma0_events_10  xdma0_events_13  xdma0_events_2   xdma0_events_5  xdma0_events_8  xdma0_user
xdma0_bypass_h2c_0  xdma0_events_0  xdma0_events_11  xdma0_events_14  xdma0_events_3   xdma0_events_6  xdma0_events_9  xdma0_xvc
```

If `/sys/class/xdma/` is empty, no FPGA is running an AFI with a device ID the driver knows. Check the AFI is loaded and that its device ID matches the one passed to `-d`.

Applications transfer data through `/dev/xdma<N>_h2c_<channel>` (host to card) and `/dev/xdma<N>_c2h_<channel>` (card to host), and wait for user interrupts on `/dev/xdma<N>_events_<interrupt>`. `<N>` is the driver's device number, which is not always the FPGA slot number. Use `fpga_pci_get_dma_device_num()` from [fpga_dma.h](./../../sdk/userspace/include/fpga_dma.h) to look up the device number for a slot.

## Notes

- The driver is built for the kernel that is running when the script runs. After a kernel update, run the script again to rebuild it.
- To bind the driver to a different device ID, unload the running driver with `sudo modprobe -r xdma`, then run the script again with the new ID. Each run builds the driver from fresh source, so it only knows `0xf000`, `0xf001`, and the ID from the latest run.
