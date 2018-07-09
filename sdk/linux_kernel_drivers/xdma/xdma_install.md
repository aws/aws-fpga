
# XDMA Driver Installation and Frequently Asked Questions

XDMA is a Linux kernel driver for using DMA and/or User-defined interrupts for AWS FPGAs. Please see [XDMA README](README.md) for details.

# Table of Contents

1. [Q: How do I know if the XDMA driver is available and installed?](#howIKnow)
2. [Q: How do I get the source code of the `xdma` driver and compile it?](#howToCompile)
3. [Q: How can I make sure the installed driver will be preserved following a kernel update?](#howToUpdateKernel) 
4. [Q: What PCIe Vendor-ID and Device-ID does XDMA driver support](#howToDIDnVID)

<a name="howIKnow"></a>
**Q: How do I know if the XDMA driver is available and installed?** 

The XDMA driver could be already installed in the latest releases of various Linux distributions and in [AWS FPGA Development AMI available at AWS Marketplace](https://aws.amazon.com/marketplace/pp/B06VVYBLZZ)

To make sure the driver is installed run next command from your linux shell:
  `$ lsmod | grep xdma`
  
Running this will return XDMA only if the driver is installed and running.

If running, the XDMA driver exposes multiple device channels.  Each XDMA channel has a write and read device filename (e.g. `/dev/xdmaX_h2c_Y` and `/dev/xdmaX_c2h_Y`), and supports the Linux character device APIs.  User-defined interrupts/events are accessed through the `/dev/xdmaX_event_Y` device files.  Where `X` is a number from 0-7 to represent different FPGAs in the system, and `Y` is used to represent the available DMA channels and event interfaces for a given FPGA.

The developer can use these DMA channel and interrupt device files directly from Linux userspace application.

<a name="howToCompile"></a>
**Q: How do I get the source code of the `xdma` driver and compile it?** 

Amazon `xdma` driver is included in [AWS FPGA SDK](.) for integration with other Linux distributions, please follow the next set of steps:

__**Step 1**__: Make sure you have `gcc` and `linux kernel source code` installed in your machine:

__*For AmazonLinux,RedHat,Centos*__

```
  $ sudo yum groupinstall "Development tools"
  $ sudo yum install kernel-devel
```  

__*For Ubuntu*__  


```
  $ sudo apt-get install make
  $ sudo apt-get install gcc
```

__*For Suse*__  

```
  $ sudo zypper install make
  $ sudo zypper install gcc
  $ sudo zypper update
  $ sudo zypper install kernel-devel

```

__**Step 2**__: Clone the git repo locally under my_fpga_dir for example:  

```
  $ mkdir -p <my_fgpa_repo>
  $ cd <my_fpga_repo>
  $ git clone https://github.com/aws/aws-fpga
```

*Note: the above mentioned git call would fail if the local git repository already exists.*

__**Step 3**__: Enter the directory and compile the code:  

```
  $ cd <my_fpga_repo>
  $ cd aws-fpga/sdk/linux_kernel_drivers/xdma
  $ make
```

If the `make` command was successful, you would find xdma.ko.

__**Step 4**__: Copy the driver to the modules directory:  

__*For AmazonLinux, RedHat, Open Suse, and Centos*__:

The next set of steps will install the kernel driver so it gets loaded everytime the machine boots/reboots: 

 `$ sudo make install`
  
To load the driver without rebooting:
 
 `$ sudo modprobe xdma`
  
To unload the driver:
  
 `$ sudo rmmod xdma`
  
To uninstall the driver so it no-longer gets loaded everytime the machine boots/reboots:
  
 `$ sudo make uninstall`

***NOTE:*** *steps 3 and 4 would need to be repeated for every kernel update*.  
  
<a name="howToUpdateKernel"></a>  
**Q: How can I make sure the installed driver will be preserved following a kernel update?**   

__*Step A*__ **Get DKMS**  

For  CentOS7 :  `sudo yum install dkms.noarch`  


__*Step B:*__	**Move the `xdma` source package to the `/usr/src/` directory**  

so dkms can find it and build it for each kernel update: Append the version number (you can find the current version number in the release notes) of the source code to the directory name. For example, version 1.0.0 is shown in the example below:  

  `$ sudo cp -R <my_fpga_repo/aws-fpga/sdk/linux_kernel_drivers/xdma /usr/src/xdma-1.0.0`

__*Step C:*__	**Create the dkms configuration file with the following values, substituting your version of xdma.**  

```
  $ sudo vim /usr/src/xdma-1.0.0/dkms.conf
  PACKAGE_NAME="xdma-drv"
  PACKAGE_VERSION="1.0.0"
  CLEAN="make -C ./ clean"
  MAKE="make -C ./ BUILD_KERNEL=${kernelver}"
  BUILT_MODULE_NAME[0]="xdma"
  BUILT_MODULE_LOCATION="."
  DEST_MODULE_LOCATION[0]="/updates"
  DEST_MODULE_NAME[0]="xdma"
  AUTOINSTALL="yes"
  ```  
  
__*Step D:*__	 **Add, build, and install the xdma module on your instance with dkms.**  

```
  $ sudo dkms add -m xdma -v 1.0.0
  $ sudo dkms build -m xdma -v 1.0.0
  $ sudo dkms install -m xdma -v 1.0.0
```

__*Step E:*__	**Rebuild the initramfs so the correct module is loaded at boot time.**
  `$ TBD`
  
__*Step F:*__ **Verify that the xdma module is installed using the modinfo xdma.**
```
  $ modinfo xdma
  filename:       /home/centos/aws-fpga-staging/sdk/linux_kernel_drivers/xdma/xdma.ko
  license:        GPL v2
  version:        2017.1.47
  description:    Xilinx XDMA Classic Driver
  author:         Xilinx, Inc.
  rhelversion:    7.3
  srcversion:     0498A67CF8B4F126703BA5D
  vermagic:       3.10.0-514.10.2.el7.x86_64 SMP mod_unload modversions 
  parm:           sgdma_timeout:timeout in seconds for sgdma, default is 10 sec. (uint)
  parm:           poll_mode:Set 1 for hw polling, default is 0 (interrupts) (uint)
```

<a name="howToDIDnVID"></a>  
**Q: What PCIe Vendor-ID and Device-ID does XDMA driver support?** 

Initially, XDMA supports PCIe VendorID:DeviceID 1d0f:f001 (the ID's of the DMA example).
To use the device driver on another CL, please add the Vendor ID and Device to the device table in [xdma_mod.c](./xdma_mod.c)

For example:

```
static const struct pci_device_id pci_ids[] = {
        ...
        { PCI_DEVICE(0x1d0f, 0xf001), },
        ...
        { 0, }
};
```
where 0x1d0f is the vendor ID for Amazon and 0xf001 is the device ID for the cl-dram-dma example CL.


Be sure to remake and re-install the XDMA driver after modifying the device table.

Amazon encourages pull requests to this github to add CL ID's to the driver, so there is no need to fork the driver or SDK.
