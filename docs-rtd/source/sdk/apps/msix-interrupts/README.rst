MSI-X Interrupts Implementation Guide
=====================================

This guide describes how to implement PCIe Message Signaled Interrupts
Extended (MSI-X) with F2. It demonstrates the implementation of a custom
interrupt service routine (ISR) and provides working examples of both
kernel and user space code.

Table of Contents
-----------------

- `Key Concepts <#key-concepts>`__
- `Implementation Steps <#implementation-steps>`__
- `Generating Interrupts <#generating-interrupts>`__
- `Additional Resources <#additional-resources>`__

Key Concepts
------------

- F2 Shell uses MSI-X protocol to support up to 16 user-defined
  interrupts
- Each interrupt can trigger a unique ISR or share an ISR with
  parameters
- ISRs execute in kernel space, where errors can cause system
  instability

Implementation Steps
--------------------

- `PCIe Configuration Space
  Setup <#enabling-interrupts-in-pcie-configuration-space>`__
- `Kernel Interrupt
  Registration <#registering-interrupts-with-the-kernel>`__
- `PCIe DMA Subsystem
  Configuration <#configuring-interrupts-in-the-pcie-dma-subsystem>`__.

Enabling Interrupts in PCIe Configuration Space
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

MSI-X functionality is enabled using the ``pci_enable_msix_exact``
function which requires the following:

- Pointer to the device’s PCI data structure
- Table to map kernel vector numbers to device interrupts
- Number of interrupts that are being allocated in the kernel

This code runs during kernel module insertion when the driver is loaded.

.. code-block:: c

   #define NUM_OF_USER_INTS 16
   struct msix_entry f2_ints[] = {
     {.vector = 0, .entry = 0},
     {.vector = 0, .entry = 1},
     ...
     {.vector = 0, .entry = 15}
   };
   # f2_dev is a pointer to the PCI device structure, representing your device
   pci_enable_msix_exact(f2_dev, f2_ints, NUM_OF_USER_INTS);

Registering Interrupts with the Kernel
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Once interrupts are allocated in the kernel, the kernel function
``request_irq`` is needed to connect each interrupt vector to a specific
ISR. In this example all 16 interrupt sources point to the same ISR,
``f2_isr``. To differentiate between the interrupt sources, a unique
structure (a pointer to an integer) is registered with the vector. The
ISR retrieves this structure when it is called. This code also runs
during kernel module insertion, immediately after enabling MSI-X.

.. code-block:: c

   for (int i = 0; i < NUM_OF_USER_INTS; i++) {
     f2_dev_id[i] = kmalloc(sizeof(int), GFP_DMA | GFP_USER);
     *f2_dev_id[i] = i;
     status =
         request_irq(f2_ints[i].vector, f2_isr, 0, "F2 Driver", f2_dev_id[i]);
   }

Configuring Interrupts in the PCIe DMA Subsystem
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

The snippet of code shown below runs from user space and programs the
PCIe block to handle interrupts. This code is executed during
application runtime, typically when initializing the device for use.

Each MSI-X entry needs its interrupt vector number programmed in the IRQ
block. By default, all vectors point to index 0. For this example, each
user interrupt is programmed to point to a different interrupt vector to
illustrate using all 16 entries. The vector numbers are aligned on byte
boundaries, and four 32-bit addresses (0x80-0x8f) are used to assign
interrupt vectors.

.. code-block:: c

   rc |= fpga_pci_poke(dma_bar_handle, dma_reg_addr(IRQ_TGT, 0, 0x080), 0x03020100);
   rc |= fpga_pci_poke(dma_bar_handle, dma_reg_addr(IRQ_TGT, 0, 0x084), 0x07060504);
   rc |= fpga_pci_poke(dma_bar_handle, dma_reg_addr(IRQ_TGT, 0, 0x088), 0x0b0a0908);
   rc |= fpga_pci_poke(dma_bar_handle, dma_reg_addr(IRQ_TGT, 0, 0x08c), 0x0f0e0d0c);

The final step is to enable interrupts by writing the interrupt enable
mask bits. In the example, all the interrupts are enabled at once with a
single write of 0xffff to the IRQ Block User Interrupt Enable Mask
register (0x004).

.. code-block:: c

   rc = fpga_pci_poke(dma_bar_handle, dma_reg_addr(IRQ_TGT, 0, 0x004), 0xffff);

Generating Interrupts
---------------------

The CL_DRAM_HBM_DMA example design does not generate interrupts
independently. It instead contains a register which when written will
produce one or more interrupts. The test program writes this register to
generate interrupts. When the interrupt is received by the ISR, it will
read a DDR location in CL and increment it by one. The test program
monitors the interrupt status register in the CL and and waits for the
acknowledge bit to be asserted.

Instructions to run example
~~~~~~~~~~~~~~~~~~~~~~~~~~~

.. code-block:: bash

   git clone https://github.com/aws/aws-fpga.git
   cd aws-fpga
   source sdk_setup.sh

Note:

- Replace ``<slot_number>`` with the appropriate FPGA slot number you’re
  using
- To find the ``<bus:device.function>`` of your FPGA slot, use
  ``sudo fpga-describe-local-image -S <slot_number>``
- The `XDMA driver <./../../../hdk/docs/XDMA-Install.html>`__ must not be
  bound to the FPGA. It binds to device ID ``0xf001`` and claims the
  BARs and MSI-X vectors this guide’s driver needs, so ``make install``
  fails. If it is installed, run ``sudo modprobe -r xdma`` before
  ``make install``.

Use the ``fpga-load-local-image`` command to load the FPGA with the
pre-generated CL_DRAM_HBM_DMA AFI

.. code-block:: bash

   sudo fpga-load-local-image -S <slot_number> -I agfi-09d63a981b83fa3ea

Run the following command with the verbose flag to see if interrupts are
enabled

.. code-block:: bash

   sudo lspci -v -s <bus:device.function>

Notice that the Capabilities Register [60] indicates that MSI-X
functionality is currently disabled (shown by the ‘Enable-’ status)

.. code-block:: bash

   <bus:device.function> Memory controller: Amazon.com, Inc. Device f001
           Subsystem: Device fedc:1d51
           Physical Slot: 3-1
           Flags: fast devsel, NUMA node 0
           Memory at 5004c000000 (64-bit, prefetchable) [size=64M]
           Memory at 50048100000 (64-bit, prefetchable) [size=64K]
           Memory at 52000000000 (64-bit, prefetchable) [size=128G]
           Capabilities: [40] Power Management version 3
           Capabilities: [60] MSI-X: Enable- Count=33 Masked-
           Capabilities: [70] Express Endpoint, MSI 00

Next, navigate to the ``aws-fpga/sdk/apps/msix-interrupts`` directory
and run the following commands

.. code-block:: bash

   make                             # compiles the kernel module
   make test                        # compiles the test program
   make install SLOT=<slot_number>  # install the device driver

To check to see if the driver loaded, run:

.. code-block:: bash

   sudo dmesg

This command will print the message buffer from the kernel. Since the
device driver is a kernel module, special prints are used to place
messages in this buffer.

Rerun ``sudo lspci -v -s <bus:device.function>`` and you should see that
MSI-X was enabled by the driver.

.. code-block:: bash

   <bus:device.function> Memory controller: Amazon.com, Inc. Device f001
           Subsystem: Device fedc:1d51
           Physical Slot: 3-1
           Flags: bus master, fast devsel, latency 0, NUMA node 0
           Memory at 5004c000000 (64-bit, prefetchable) [size=64M]
           Memory at 50048100000 (64-bit, prefetchable) [size=64K]
           Memory at 52000000000 (64-bit, prefetchable) [size=128G]
           Capabilities: [40] Power Management version 3
           Capabilities: [60] MSI-X: Enable+ Count=33 Masked-
           Capabilities: [70] Express Endpoint, MSI 00

To see the interrupts in use, run the following command

.. code-block:: bash

   sudo ./f2_test <slot_number>

Running the example on a 12xlarge instance will show the following on
the terminal:

::

   Starting MSI-X Interrupt test
   Initial DDR value: 0
   IRQ Block Identifier read_data: 1fc20006
   IRQ Block User Interrupt Enable Mask read_data: 0, Addr: 2004
   IRQ Block User Vector Number read_data: 3020100, Addr: 2080

   Triggering single interrupt (interrupt 0)...
   Initial DDR value: 0
   Current DDR value: 1

   Triggering each of the MSI-X interrupts...
   Triggering interrupt 0 (bit 0)
   Triggering interrupt 1 (bit 1)
   ...
   Triggering interrupt 15 (bit 15)
   CL interrupt status read_data: ffff0000
   CL read_data: 00000000

Run ``sudo dmesg`` to see the kernel log which shows each interrupt that
is triggered and its corresponding DDR counter value.

Other Useful MakeFile Targets
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

``make remove``

- Removes the F2 kernel module from the system using ``rmmod``
- Use this command when you want to unload the driver

``make clean``

- Removes all compiled files and build artifacts
- Cleans the kernel module build directory
- Removes the compiled test program (f2_test)
- Use this before rebuilding the driver from scratch

Additional Resources
--------------------

- `AWS F2 Shell Interface
  Specification <./../../../hdk/docs/AWS-Shell-Interface-Specification.html>`__
- `The MSI Driver Guide
  HOWTO <https://www.kernel.org/doc/Documentation/PCI/MSI-HOWTO.txt>`__
- `How To Write Linux PCI
  Drivers <https://www.kernel.org/doc/Documentation/PCI/pci.txt>`__
- `PCI Express Product Guide
  PG195 <https://docs.amd.com/r/en-US/pg195-pcie-dma>`__

`Back to Home <../../../index.html>`__
