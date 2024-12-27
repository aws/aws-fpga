AWS EC2 F2 Shell Errata
=======================

Implementation Restrictions
---------------------------

- PCIE AXI4 interfaces between Custom Logic(CL) and Shell(SH) have
  following restrictions:

  - All PCIe transactions must adhere to the PCIe base spec
  - 4-KByte address boundary for all transactions (PCIe restriction)
  - Multiple outstanding outbound PCIe read transactions with same ID is
    not supported
  - PCIe extended tag not supported. Read-request is limited to 32
    outstanding
  - Address must match DoubleWord(DW) address of the transaction
  - WSTRB (write strobe) must reflect appropriate valid bytes for AXI
    write beats
  - Only increment burst type is supported
  - AXI lock, memory type, protection type, quality of service (QoS) and
    region identifier are not supported
  - Transactions from the Shell to CL must complete within the timeout
    period to avoid transaction termination by the Shell
  - DMA transactions from the Shell to CL must complete within the
    timeout period to avoid transaction termination and invalid data
    returned for the DMA transaction
  - PCIM and DMA-PCIS AXI4 interfaces do not support AxSIZE other than
    3'b110 (64B)

Unsupported Features
--------------------

- HBM metrics not yet supported

Known Bugs/Issues
-----------------
