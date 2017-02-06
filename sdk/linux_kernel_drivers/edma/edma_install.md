
# EDMA Installation and Frequently Asked Questions

EDMA is a Linux kernel driver provided by AWS for using DMA and/or User-defined interrupts for AWS FPGAs. Please see [EDMA README](./edma_README.md) for details.

# Table of Contents

1. [Q: How do I know if the EDMA driver is available and installed?](#howIKnow)
2. [Q: How do I get the source code of the `edma` driver and compile it?](#howToCompile)
3. [Q: How can I make sure the installed driver will be preserved following a kernel update?](#howToUpgradeKernel) 
4. [Q: What PCIe Vendor-ID and Device-ID does EDMA driver support](#howToDIDnVID)
5. [Q: How to troubleshoot EDMA compilation or installing?](#howToTroubleshoot)


############


**Q: How do I know if the EDMA driver is available and installed?** <a name="howIKnow"></a>

Amazon EDMA driver could be already installed in latest releases of various Linux distributions and in [AWS FPGA Development AMI available at AWS Marketplace](./TBD)

To make sure the driver is installed run next command from your linux shell:
  `$ lsmod | grep edma`
  
Running this will return EDMA only if the driver is installed and running.

If running, the device /dev/fpgaX(X=0..7) represents an FPGA device in slot X, and with each FPGA exposing multiple queues under /dev/fpgaX/dma_queueN, and multiple user-defined interrupts/events under /dev/fpgaX/eventK.

The developer can operate these DMA queues and interrupts directly from Linux userspace application.


**Q: How do I get the source code of the `edma` driver and compile it?** <a name="howToCompile"></a>

Amazon `edma` driver is included in [AWS FPGA SDK](https://github.com/aws/aws-fpga/master/blob/sdk/kernel_drivers/edma) for integration with other Linux distributions, please follow the next set of steps:

__**Step 1**__: Make sure you have `gcc` and `linux kernel source code` installed in your machine:

__*For AmazonLinux,RedHat,Centos*__

```
  $ sudo yum groupinstall "Development tools"
  $ sudo yum install kernel-devel
```  

__*For Ubunto*__  

```
  $ sudo apt-get install make
  $ sudo apt-get install gcc
```

__*For Suse*__  

```
  $ sudo zypper install make
  $ sudo zypper install gcc
  $ sudo zypper update
  $  sudo zypper install kernel-devel
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

If the `make` command was successful, you would find edma.ko.

__**Step 4**__: Copy the driver to the modules directory:  

__*For AmazonLinux, RedHat, Open Suse, Centos, and Ubuntu*__:

The next set of steps will installing the kernel driver so it get called everytime the machine boots/reboots  

```
  $ sudo vi /etc/modules-load.d/edma.conf
        // insert "edma" to the file and save it
  $ cp edma.ko /lib/modules/(uname -r)/
  $ sudo depmod
```  

***NOTE:*** *steps 3 and 4 would need to be repeated for every kernel update*.  
  
  
** Q: How can I make sure the installed driver will be preserved following a kernel update?** <a name="howToUpdateKernel"></a>  

__*Step A*__ **Get DKMS**  

For  CentOS7 :  `sudo yum install dkms.noarch`  


__*Step B:*__	**Move the `edma` source package to the `/usr/src/` directory**  

so dkms can find it and build it for each kernel update: Append the version number (you can find the current version number in the release notes) of the source code to the directory name. For example, version 1.0.0 is shown in the example below:  

  `$ sudo mv <my_fpga_repo/aws-fpga/sdk/linux_kernel_drivers/edma /usr/src/edma-1.0.0`

__*Step C:*__	**Create the dkms configuration file with the following values, substituting your version of edma.**  

```
  $ sudo vim /usr/src/edma-1.0.0/dkms.conf
  PACKAGE_NAME="edma"
  PACKAGE_VERSION="1.0.0"
  CLEAN="make -C ./ clean"
  MAKE="make -C ./ BUILD_KERNEL=${kernelver}"
  BUILT_MODULE_NAME[0]="edma"
  BUILT_MODULE_LOCATION="."
  DEST_MODULE_LOCATION[0]="/updates"
  DEST_MODULE_NAME[0]="edma"
  AUTOINSTALL="yes"
  ```  
  
__*Step D:*__	 **Add, build, and install the edma module on your instance with dkms.**  

```
  $ sudo dkms add -m edma -v 1.0.0
  $ sudo dkms build -m edma -v 1.0.0
  $ sudo dkms install -m edma -v 1.0.0
```

__*Step E:*__	**Rebuild the initramfs so the correct module is loaded at boot time.**
  `$ TBD`
  
__*Step F:*__ **Verify that the edma module is installed using the modinfo edma.**
```
  $ modinfo edma
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
```

**Q: What PCIe Vendor-ID and Device-ID does EDMA driver support?** <a name="howToDIDnVID"></a>  

TBD


**Q: How to troubleshoot EDMA compilation or installing?** <a name="howToTroubleshoot"></a>


