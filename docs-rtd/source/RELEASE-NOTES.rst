F2 Developer Kit Release Notes
==============================

.. _v210:

v2.1.0
------

- Support for Vivado and Vitis 2024.2 tools.
- `Releasing New Developer AMI for 2024.2 tools. <http://aws.amazon.com/marketplace/pp/prodview-tcl7sjgreh6bq>`__
- Updating the asynchronous fpga_mgmt_examples to poll each FPGA once before moving to the next.

.. _v207:

v2.0.7
------

- Documentation updates to improve `ReadTheDocs <https://awsdocs-fpga-f2.readthedocs-hosted.com/latest>`__ navigation and inline snippets.
- XSIM template script update to extend the waveform dump time.
- Added section with instructions for assigning custom PCIe IDs to HDK `README <./hdk/README.html>`__.
- Added supplementary XDMA driver installation `guide <./hdk/docs/XDMA-Install.html>`__
- Updated `ERRATA <./ERRATA.html#hdk-errata>`__ with fix for XSIM when simulating HBM.
- Revised the `Vitis README <./vitis/README.html>`__ with updated code snippets, more detail about the XRT setup, and a new guided example of the Hardware Emulation workflow.
- Fixed HDK DCP Tarball path issue described in `#706 <https://github.com/aws/aws-fpga/issues/706>`__.

.. _v206:

v2.0.6
------

- Releasing `CL_SDE software examples <./hdk/cl/examples/cl-sde/software/src/README.html>`__ to demonstrate how to use the `Streaming Data Engine (SDE) <./sdk/apps/virtual-ethernet/doc/Virtual-Ethernet-Application-Guide.html>`__ DMA for `small shell <./User-Guide-AWS-EC2-FPGA-Development-Kit.html#aws-shells>`__.
- Fixing the `virtual ethernet <./sdk/apps/virtual-ethernet/doc/SDE-HW-Guide.html>`__ PacketGen Dual Instance Loopback example to forward packets back to the PacketGen instance.
- Fixing DDR backdoor access in simulation.

.. _v205:

v2.0.5
------

- Releasing instructions for using the Vivado GUI.
- Updating virtual_ethernet_install.py to no longer require sudo when run.
- Updating f2_mgmt_example, load_multiple_fpga.c, to load AFIs in parallel.
- Updated ReadTheDocs theme.
- Added the "F2 Software Performance Optimization Guide" with techniques for f2.48xlarge instances

.. _v204:

v2.0.4
------

- Release of new F2 instance size, **f2.6xlarge**:

.. list-table::
  :header-rows: 1
  :class: release-notes-instances
  :widths: 12 6 6 24 12 12 12 12

  * - Instance Name
    - FPGAs
    - vCPUs
    - FPGA Memory HBM/DDR4
    - Instance Memory (GB)
    - Local Storage (GiB)
    - Network Bandwidth (Gbps)
    - EBS Bandwidth (Gbps)
  * - **f2.6xlarge**
    - **1**
    - **24**
    - **16 GiB / 64 GiB**
    - **256**
    - **1 x 950**
    - **12.5**
    - **7.5**
  * - f2.12xlarge
    - 2
    - 48
    - 32 GiB / 128 GiB
    - 512
    - 2 x 950
    - 25
    - 15
  * - f2.48xlarge
    - 8
    - 192
    - 128 GiB / 512 GiB
    - 2048
    - 8 x 950
    - 100
    - 60

.. _v203:

v2.0.3
------

- Releasing fpga_mgmt_examples to demonstrate how the FPGA Management C API is used to perform FPGA image slot load and clear operations.
- Releasing the PacketGen Dual Instance Loopback example to the SDK Virtual Ethernet Application.
- Fixing the clkgen CLIs to prevent the configuration of clock groups that were removed from the AWS_CLK_GEN IP in customer designs.

.. _v202:

v2.0.2
------

Updates for initial release of ReadTheDocs documentation and to re-enable tests for XSIM.

.. _v201:

v2.0.1
------

Updates to HDK, SDK, and Vitis documentation.
Added check for XRT install to enable Vitis hardware emulation.
XRT install can now be performed automatically by running a
command presented during ``vitis_setup.sh``.

.. _v200:

v2.0.0
------

Initial release. F2 general-availability companion.

`Back to Home <./index.html>`__
