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
    3’b110 (64B)

Unsupported Features
--------------------

- HBM metrics not yet supported

Known Bugs/Issues
-----------------

- HBM ECC Scrubbing is not supported in Small Shell ``0x10212415``:

  - DO NOT enable the “Enable ECC Scrubbing” or the “Initialize Memory
    Using ECC” option in the HBM IP. ECC scrubbing takes too long to
    finish, so enabling either option causes an HBM monitor interface
    timeout during AFI loading, making the HBM inaccessible. Refer to
    `AWS Shell Interface
    Specification <./AWS-Shell-Interface-Specification.html#hbm-monitor-interface>`__
    for details.
  - ECC protection remains available. Developers can enable only the
    “Enable ECC Correction” option in the IP configuration to use it.
    **Note: Reading from uninitialized memory locations will result in
    ECC errors**.

- Function Level Reset (FLR) is currently unavailable on F2 instances.
  AWS has confirmed an issue with FLR on F2 instances and a fix is in
  progress. See `aws-fpga issue
  #811 <https://github.com/aws/aws-fpga/issues/811>`__ for status.
- The descriptions of ``sh_cl_flr_assert`` and ``cl_sh_flr_done`` in
  ``cl_ports.vh`` and in the HDK simulation BFM do not match the Shell’s
  behavior. ``sh_cl_flr_assert`` is a single ``clk_main_a0`` cycle
  pulse, not a level, and the Shell does not wait for
  ``cl_sh_flr_done``, which is optional.

`Back to Home <../../index.html>`__
