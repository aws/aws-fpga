XDMA Driver Installation Instructions
=====================================

XDMA kernel driver enables the customers to interact with the optional
high-performance DMA engine and/or user-defined interrupts in AWS EC2 F2
instances. The driver is only applicable to instances with the `XDMA
Shell <./../../README.md#aws-shells>`__ loaded. For more details about
the driver, refer to the `XDMA driver page in Xilinx DMA IP driver
repository <https://github.com/Xilinx/dma_ip_drivers/tree/master/XDMA/linux-kernel>`__.

Please follow the steps below to install the XDMA driver on AWS EC2 FPGA
instances:

1. Clone the XDMA driver from AMD/Xilinx Github repository:

   .. code:: bash

      git clone https://github.com/Xilinx/dma_ip_drivers

2. Add F2 PCIe Vendor ID and Device ID to
   ``dma_ip_drivers/XDMA/linux-kernel/xdma/xdma_mod.c`` by inserting the
   commented line below to the ``pci_ids`` variable definition:

   .. code:: C

      static const struct pci_device_id pci_ids[] = {
          { PCI_DEVICE(0x1D0F, 0x9048), },  // AWS F2 PCIe Vendor and Device IDs
          { PCI_DEVICE(0x10ee, 0x9048), },
          { PCI_DEVICE(0x10ee, 0x9044), },
          { PCI_DEVICE(0x10ee, 0x9042), },
          ...
      };

3. Compile the XDMA driver:

   .. code:: bash

      cd dma_ip_drivers/XDMA/linux-kernel/xdma/
      make

4. Insert the module into the kernel: ⚠️ Only the polling mode is
   supported for the XDMA driver. Refer to the
   `errata <./../../ERRATA.md>`__ for details.

   .. code:: bash

      sudo insmod xdma.ko poll_mode=1

5. Verify the module is successfully loaded:

   .. code:: bash

      lsmod | grep xdma

          xdma                   86016  0

6. Also verify that files are populated to the XDMA paths in
   ``/sys/class/xdma/``

   .. code:: bash

      ls /sys/class/xdma

          ...

          xdma0_bypass        xdma0_c2h_0     xdma0_events_1   xdma0_events_12  xdma0_events_15  xdma0_events_4  xdma0_events_7  xdma0_h2c_0
          xdma0_bypass_c2h_0  xdma0_control   xdma0_events_10  xdma0_events_13  xdma0_events_2   xdma0_events_5  xdma0_events_8  xdma0_user
          xdma0_bypass_h2c_0  xdma0_events_0  xdma0_events_11  xdma0_events_14  xdma0_events_3   xdma0_events_6  xdma0_events_9  xdma0_xvc
