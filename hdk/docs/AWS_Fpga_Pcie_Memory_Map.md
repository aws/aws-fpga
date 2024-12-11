# AWS FPGA PCIe Memory Map

FPGAs are PCIe-attached to an AWS EC2 instance. Each FPGA slot presents a single FPGA with two PCIe Physical Functions (PFs), each with multiple PCIe Base Address Registers (BARs) as defined in the [AWS Shell Specification](./AWS_Shell_Interface_Specification.md).

This document describes the size and attributes of each BAR. Even though all of these PCIe BARs are mapped to the EC2 Instance memory-mapped I/O (MMIO) space, they need to be mapped to the Linux kernel or a userspace application before accessing them.

## Memory Map per Slot

```text
--- FPGA Slot X
  |--- Application PF (AppPF)
  |  |-- BAR0
  |  |     * 64-bit, prefetchable
  |  |     * 64MiB (0x000_0000 to 0x3FF_FFFF)
  |  |     * Mapped to the OCL AXI-lite interface of CL
  |  |     * Typically used for CL application registers or OpenCL kernels
  |  |
  |  |-- BAR2
  |  |     * 64-bit, prefetchable
  |  |     * 64KiB (0x0000 to 0xFFFF)
  |  |     * Not mapped to CL.
  |  |     * Used by internal DMA inside the Shell
  |  |
  |  |-- BAR4
  |        * 64-bit, prefetchable
  |        * 128GiB (0x00_0000_0000 to 0x1F_FFFF_FFFF)
  |        * Mapped to the PCIS AXI4 interface of CL
  |        * Typically used for DMA traffic bewteen the host and HBM/DDR memories on the card
  |
  |--- Management PF (MgmtPF)
     |-- BAR0
     |     * 64-bit, prefetchable
     |     * 16KiB (0x0000 to 0x3FFF)
     |     * Not mapped to CL
     |     * Used by the FPGA management tools
     |
     |-- BAR2
     |     * 64-bit, prefetchable
     |     * 16KiB (0x0000 to 0x3FFF)
     |     * Not mapped to CL
     |     * Used by the FPGA management tools
     |
     |-- BAR4
           * 64-bit BAR, prefetchable
           * 4MiB (0x00_0000 to 0x3F_FFFF)
           * Mapped to the SDA AXI-lite interface of CL
           * Could be used by developer applications, AWS CL clock generator , or if using the AWS Runtime Environment (like SDAccel case), it will be used for performance monitoring.
```

## Prefetchable BAR Setting

The F2 shell is configured with all the Base Address Registers (BARs) in the host PCIe endpoint as prefetchable. Prefetchable BARs allow the use of optimization techniques like prefetching, write-combining (also referred to as write-merging) to improve the BAR-access performance. To take advantage of that, customers must ensure the logic mapped to a prefetchable BAR complies with the PCIe specification (see section 7.5.1.2.1 for details). This design choice was carefully considered to allow F2, a general-purpose accelerator platform, to be easily integrated with a wide range of customer acceleration applications. Customers who do not require these optimizations can still access prefetchable BARs in a non-prefetchable way without penalty or side effect.

Marking a PCIe BAR as prefetchable or non-prefetchable is a hardware design decision driven by providing maximum flexibility to the software because the configuration cannot be modified by the customer. AWS offers this flexibility to F2 customers by advertising all the BARs in the shell as prefetchable. Customer applications must access BARs in a way supported by the customer logic (CL). For example, enabling write-combining on a prefetchable BAR requires a custom kernel driver or application to map and mark the target memory space as [write-combining (WC) memory](https://docs.kernel.org/driver-api/device-io.html#device-memory-mapping-modes). Additionally, applications enabling prefetching should avoid caching data from a memory space that contains any clear-on-read registers or FIFOs.

The PCIe specification encourages the use of prefetchable BAR memory space whenever possible, even if a BAR might contain non-prefetchable logic. As stated in the "Additional Guidance on the Prefetchable Bit in Memory Space BARs" under the PCIe specification, section 7.5.1.2.1, there are system configurations where having the Prefetchable bit set can still allow correct operation, even if the conditions for prefetchability are not met.

Third-party accelerator cards [[1](https://docs.amd.com/v/u/en-US/ug1468-alveo-u55c), [2](https://docs.amd.com/v/u/en-US/ug1370-u50-installation)] that are compatible with the F2 card (with multi-SLR, HBM FPGA) also only carry prefetchable BARs. Aligning the F2 BAR settings with these cards provides our customers flexibility to migrate between on-premise and cloud without having to change software/hardware.
