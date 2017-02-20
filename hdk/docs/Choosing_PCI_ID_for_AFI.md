# Choosing PCI ID for Amazon FPGA Image

As AWS FPGA is a PCIe device, it is required to have a PCI Vendor ID and PCI Device ID.

The combination of Vendor ID and Device ID are used by the instance operating system to identify the device, and load any kernel drivers if required.

The PCI Vendor ID is assigned by PCI SIG, and requires registeration and paying certain fees.

AWS Customers who don't have a registered PCI Vendor ID can use Amazon's vendor ID (0x1D0F) **as long as they comply with all the following requirements**
1) The Vendor ID (0x1D0F) is used only for designs intended to run on AWS and not to be used or assign to any PCI/PCIe device outside FPGA on AWS
2) The Device ID is within the range 0xF000 to 0xFFFF

