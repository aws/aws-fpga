
# Elastic DMA (EDMA) Installation and Frequently Asked Questions

EDMA is a Linux kernel driver provided by AWS for using DMA and/or User-defined interrupts for AWS FPGAs. Please see [EDMA README](README.md) for details.

# Table of Contents

1. [Q: How do I know if the EDMA driver is available and installed?](#howIKnow)
2. [Q: How do I get the source code of the `edma` driver and compile it?](#howToCompile)
3. [Q: How can I make sure the installed driver will be preserved following a kernel update?](#howToUpdateKernel) 
4. [Q: What PCIe Vendor-ID and Device-ID does EDMA driver support](#howToDIDnVID)


############

<a name="howIKnow"></a>
**Q: How do I know if the EDMA driver is available and installed?** 

Amazon EDMA driver could be already installed in latest releases of various Linux distributions and in [AWS FPGA Development AMI available at AWS Marketplace](https://aws.amazon.com/marketplace/pp/B06VVYBLZZ)

To make sure the driver is installed run next command from your linux shell:
  `$ lsmod | grep edma`
  
Running this will return EDMA only if the driver is installed and running.

If running, the EDMA driver exposes multiple device queues as `/dev/edma_X_queue_Y`, and user-defined interrupts/events under `/dev/fpga_X_eventY`.  Where `X` is a number from 0-7 to represent different FPGAs in the system, and `Y` is used to represent the available DMA queues and event interfaces for a given FPGA.

The developer can operate these DMA queues and interrupts directly from Linux userspace application.

<a name="howToCompile"></a>
**Q: How do I get the source code of the `edma` driver and compile it?** 

Amazon `edma` driver is included in [AWS FPGA SDK](.) for integration with other Linux distributions, please follow the next set of steps:

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
  $ cd aws-fpga/sdk/linux_kernel_drivers/edma
  $ make
```

If the `make` command was successful, you would find edma-drv.ko.

__**Step 4**__: Copy the driver to the modules directory:  

__*For AmazonLinux, RedHat, Open Suse, and Centos*__:

The next set of steps will install the kernel driver so it gets loaded everytime the machine boots/reboots: 

 `$ sudo make install`
  
To load the driver without rebooting:
 
 `$ sudo modprobe edma-drv`
  
To unload the driver:
  
 `$ sudo rmmod edma-drv`
  
To uninstall the driver so it no-longer gets loaded everytime the machine boots/reboots:
  
 `$ sudo make uninstall`

***NOTE:*** *steps 3 and 4 would need to be repeated for every kernel update*.  
  
<a name="howToUpdateKernel"></a>  
**Q: How can I make sure the installed driver will be preserved following a kernel update?**   

__*Step A*__ **Get DKMS**  

For  CentOS7 :  `sudo yum install dkms.noarch`  


__*Step B:*__	**Move the `edma` source package to the `/usr/src/` directory**  

so dkms can find it and build it for each kernel update: Append the version number (you can find the current version number in the release notes) of the source code to the directory name. For example, version 1.0.0 is shown in the example below:  

  `$ sudo cp -R <my_fpga_repo/aws-fpga/sdk/linux_kernel_drivers/edma /usr/src/edma-1.0.0`

__*Step C:*__	**Create the dkms configuration file with the following values, substituting your version of edma.**  

```
  $ sudo vim /usr/src/edma-1.0.0/dkms.conf
  PACKAGE_NAME="edma-drv"
  PACKAGE_VERSION="1.0.0"
  CLEAN="make -C ./ clean"
  MAKE="make -C ./ BUILD_KERNEL=${kernelver}"
  BUILT_MODULE_NAME[0]="edma-drv"
  BUILT_MODULE_LOCATION="."
  DEST_MODULE_LOCATION[0]="/updates"
  DEST_MODULE_NAME[0]="edma-drv"
  AUTOINSTALL="yes"
  ```  
  
__*Step D:*__	 **Add, build, and install the edma module on your instance with dkms.**  

```
  $ sudo dkms add -m edma-drv -v 1.0.0
  $ sudo dkms build -m edma-drv -v 1.0.0
  $ sudo dkms install -m edma-drv -v 1.0.0
```

__*Step E:*__	**Rebuild the initramfs so the correct module is loaded at boot time.**
  `$ TBD`
  
__*Step F:*__ **Verify that the edma module is installed using the modinfo edma-drv.**
```
  $ modinfo edma-drv
  filename:       /lib/modules/3.10.0-514.10.2.el7.x86_64/edma-drv.ko
  version:        1.0.0
  license:        GPL
  description:    Elastic Direct Memory Access
  author:         Amazon.com, Inc. or its affiliates
  rhelversion:    7.3
  srcversion:     F01AF35203139A075B6C6B0
  alias:          pci:v00001D0Fd0000F001sv*sd*bc*sc*i*
  depends:        
  vermagic:       3.10.0-514.10.2.el7.x86_64 SMP mod_unload modversions 
  parm:           poll_mode:Set 1 for hw polling, default is 0 (interrupts) (uint)
  parm:           desc_blen_max:per descriptor max. buffer length, default is (1 << 28) - 1 (uint)
  parm:           transient_buffer_size:Transient buffer size. (default=32MB) (uint)
  parm:           single_transaction_size:The size of a single transaction over the DMA. (default=32KB) (uint)
  parm:           edma_queue_depth:EDMA queue depth. (default=1024) (uint)
  parm:           fsync_timeout_sec:fsync timeout sec. (default=9) (uint)
```

<a name="howToDIDnVID"></a>  
**Q: What PCIe Vendor-ID and Device-ID does EDMA driver support?** 

Initial, EDMA supports PCIe VendorID:DeviceID 1d0f:f001 (the ID's of the DMA example).
To use the device driver on another CL, please add the Vendor ID and Device to the device table in [edma_backend_xdma.c](./edma_backend_xdma.c)

For example:

```
static DEFINE_PCI_DEVICE_TABLE(edma_pci_tbl) = {
        { PCI_VENDOR_ID_AMAZON, PCI_DEVICE_ID_FPGA,
          PCI_ANY_ID, PCI_ANY_ID, 0, 0, PCI_ANY_ID},
        { 0x1d0f, 0xf000,
          PCI_ANY_ID, PCI_ANY_ID, 0, 0, PCI_ANY_ID},
        { 0, }
};
```
where 0x1d0f is the vendor ID for Amazon and 0xf000 is the device ID for the Hello World example CL (which does not actually support DMA).

Be sure to remake and re-install the EDMA driver after modifying the device table.

Amazon encourages pull requests to this github to add CL ID's to the driver, so there is no need to fork the driver or SDK.
