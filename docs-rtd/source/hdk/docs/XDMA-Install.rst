XDMA Driver Installation Instructions
=====================================

XDMA kernel driver enables the customers to interact with the optional
high-performance DMA engine in the `XDMA Shell
<./../../User-Guide-AWS-EC2-FPGA-Development-Kit.html#aws-shells>`__
and/or user-defined interrupts in AWS EC2 F2 instances. For more details about
the driver, refer to the `XDMA driver page in Xilinx DMA IP driver
repository <https://github.com/Xilinx/dma_ip_drivers/tree/master/XDMA/linux-kernel>`__.

Please follow the steps below to install the XDMA driver on AWS EC2 FPGA
instances:

1. Clone the XDMA driver from AMD/Xilinx GitHub repository:

   .. code:: Bash

      $ git clone https://github.com/Xilinx/dma_ip_drivers

2. Add F2 PCIe Vendor ID and Device ID to
   ``XDMA/linux-kernel/xdma/xdma_mod.c`` by inserting the commented line
   below to the ``pci_ids`` variable definition. For information on locating
   these PCIe IDs, refer to the `HDK development guide <../README.html#afi-pcie-ids>`__.

   .. code:: C

      static const struct pci_device_id pci_ids[] = {
          { PCI_DEVICE(0x1D0F, 0xF001), },  // Customer defined PCIe Vendor and Device IDs for F2 instance
          { PCI_DEVICE(0x10ee, 0x9048), },
          { PCI_DEVICE(0x10ee, 0x9044), },
          { PCI_DEVICE(0x10ee, 0x9042), },
          ...
      };

3. Compile the XDMA driver:

   .. code:: Bash

      $ cd <DMA_DRIVER_ROOT>/dma_ip_drivers/XDMA/linux-kernel/xdma/
      $ make

4. Insert the module into the kernel:

   .. code:: Bash

      $ sudo insmod xdma.ko

5. Verify the module is successfully loaded:

   .. code:: Bash

      $ lsmod | grep xdma
      xdma                   86016  0

6. Also verify that files are populated to the XDMA paths in
   ``/sys/class/xdma/``

   .. code:: Bash

      $ ls /sys/class/xdma
      xdma0_bypass        xdma0_c2h_0     xdma0_events_1   xdma0_events_12  xdma0_events_15  xdma0_events_4  xdma0_events_7  xdma0_h2c_0
      xdma0_bypass_c2h_0  xdma0_control   xdma0_events_10  xdma0_events_13  xdma0_events_2   xdma0_events_5  xdma0_events_8  xdma0_user
      xdma0_bypass_h2c_0  xdma0_events_0  xdma0_events_11  xdma0_events_14  xdma0_events_3   xdma0_events_6  xdma0_events_9  xdma0_xvc

7. Verify that the XDMA driver is bound to the correct device using `lspci`

   .. code:: Bash

      $ lspci -vvs 35:00.0
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

`Back to HDK README <../README.html>`__
