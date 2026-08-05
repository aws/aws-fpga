F2 Developer Kit Release Notes
==============================

v2.3.4
------

- Released the `AWS FPGA
  Workshop <https://catalog.us-east-1.prod.workshops.aws/workshops/9391f9b2-8011-460c-ab4c-ac8ff1adcf03/en-US>`__
  for getting started with FPGA development on AWS
- Added an `Operating System Support
  Matrix <./developer-resources/OS-Support-Matrix.html>`__ documenting AMD
  Vivado/Vitis operating system support alongside the FPGA Developer AMI
  combinations built and tested by AWS
- Runtime AMI Builder (RAB) and Python dependency security updates
- Removed the ``sdk_setup.sh`` step that wrote the ``allow_non_root``
  function to ``/tmp/sdk_root_env.exp``; the SDK tools now source it
  directly from ``shared/bin/set_common_functions.sh``
- Updated the Vitis `ERRATA <./vitis/ERRATA.html>`__ to reflect examples
  that do not currently support Hardware Emulation

v2.3.3
------

- Migrated FPGA Developer AMI (Ubuntu) - 1.16.2 to Ubuntu 22.04 due to
  20.04 EoL
- Added AWS Clock Gen IP toggle/deassert reset SDK API entries, Cython
  bindings, and updated documentation
- Updated devkit to support Vivado/Vitis tool versions back to 2024.1
- Updated AWS EC2 F2 RAB to use 32GiB of storage for the root volume to
  simplify building experience

v2.3.2
------

- Introducing a new beginner-friendly CL example called
  `cl_axil_reg_access <./hdk/cl/examples/cl-demo/cl-axil-reg-access/README.html>`__
  that demonstrates OCL AXI-Lite interface usage for CL register access

  - `Interactive Jupyter Notebooks <./sdk/notebooks/README.html>`__
    provide step-by-step instructions for the software runtime example,
    guiding developers through loading an AFI and performing register
    reads and writes on a live F2 instance

- Added IP warning suppression for Vitis builds with compatible XSAs
- General bug fixes

v2.3.1
------

- Released FPGA Developer AMIs - 1.19.1: Ubuntu and Rocky Linux with AMD
  patch
  `AR000039913 <https://adaptivesupport.amd.com/s/article/000039913>`__
  pre-installed. This fixes the XSIM compilation bug in Vivado 2025.2,
  and the double compilation workaround has been removed from
  ``Makefile.common.inc``
- Updated verbiage in `Amazon DCV Setup
  Guide <./developer-resources/Amazon-DCV-Setup-Guide.html>`__ to improve
  clarity
- Updated all NPM packages in
  `package-lock.json <https://github.com/aws/aws-fpga/tree/f2/developer_resources/runtime_ami_builder/package-lock.json>`__
  to address security advisories
- Added information about EC2 instance placement groups to maximize
  throughput and minimize latency when networking between instances in
  the `Virtual Ethernet Application
  Guide <./sdk/apps/virtual-ethernet/doc/Virtual-Ethernet-Application-Guide.html>`__
- Formatted all Python files for style, consistency, and compliance with
  PEP 8

v2.3.0
------

- Vivado/Vitis 2025.2 Support

  - Both the `FPGA Developer AMI (Ubuntu) -
    1.19.0 <https://aws.amazon.com/marketplace/pp/prodview-tcl7sjgreh6bq>`__
    and `FPGA Developer AMI (Rocky Linux) -
    1.19.0 <http://aws.amazon.com/marketplace/pp/prodview-7mukkbz7l2uvu>`__
    are available with 2025.2 tools installed and ready to use
  - `See what’s new in Vivado 2025.2
    here <https://www.amd.com/en/products/software/adaptive-socs-and-fpgas/vivado/vivado-whats-new.html#tabs-de9b056824-item-d69fba5dd6-tab>`__
  - `See what’s new in Vitis 2025.2
    here <https://www.amd.com/en/products/software/adaptive-socs-and-fpgas/vitis/vitis-whats-new.html>`__

- AWS EC2 F2 Runtime AMI Builder (RAB) Update

  - Added support for `Vivado Lab Edition
    2025.2 <https://docs.amd.com/r/en-US/ug908-vivado-programming-debugging/Vivado-Lab-Edition>`__

- Virtual Ethernet Driver

  - Updated to use natively-available kernel modules instead of DPDK
    ones

- HDK Devkit Updates

  - Cleaned up the legacy code in the ```power_up()`` simulation
    task <./hdk/common/verif/models/sh_bfm/sh_bfm.sv#L1218-L1253>`__ to
    align with the correct shell clock scheme.
  - Due to a XSIM bug in Vivado 2025.2, a double compilation workaround
    is added in ``Makefile.common.inc`` (see
    `ERRATA <./ERRATA.html#hdk>`__ for more details)

- AFI and AMI Creation Permission Requirements

  - Added `Setting Up IAM Roles for DevKit
    Use <./developer-resources/Setting-up-IAM-roles-for-devkit-use.html>`__
    doc that shows how to set up an IAM role and the minimum permission
    configurations needed to create each of these artifacts

v2.2.2
------

- Introducing the AWS EC2 F2 Runtime AMI Builder (RAB)

  - The RAB is a customizable and extensible tool based on `the AWS
    CDK <https://docs.aws.amazon.com/cdk/v2/guide/home.html>`__ that
    easily automates building production-ready AMIs tailored to each
    accelerator application’s needs
  - `To get started building a runtime AMI, see the README
    here <./developer-resources/runtime-ami-builder/README.html>`__
  - Default components are provided to modularly install specific
    features such as Vivado Lab Edition, the AWS CLI, the AWS FPGA SDK,
    and more
  - `To learn how to integrate the RAB into existing AWS CDK flows, see the code example here <https://github.com/aws/aws-fpga/tree/f2/developer_resources/runtime_ami_builder/lib/exampleLibraryUsage.ts>`__

- `Updated Rocky FPGA Developer
  AMI <https://aws.amazon.com/marketplace/pp/prodview-7mukkbz7l2uvu>`__
  name and description to match Marketplace info
- Added F2 `AFI Manifest specification <./hdk/docs/AFI-Manifest.html>`__
  for the version number, ID, and clock parameters
- Added new “–no-encrypt” build option to the HDK flow to facilitate
  source code debugging
- Updated
  `fpga_clkgen_util <https://github.com/aws/aws-fpga/tree/f2/sdk/userspace/fpga_libs/fpga_clkgen/fpga_clkgen_utils.c>`__
  and `sde_examples <./hdk/cl/examples/cl-sde/software/src/README.html>`__
  with better error handling procedures, addressing stability issues
  found on Rocky Linux.

v2.2.1
------

- `Release of FPGA Developer AMI 1.18.0 (Rocky Linux
  8.10) <http://aws.amazon.com/marketplace/pp/prodview-7mukkbz7l2uvu>`__
  with Vivado/Vitis 2025.1 tools pre-installed
- `Release of Vivado HLx
  flow <./User-Guide-AWS-EC2-FPGA-Development-Kit.html#development-environments>`__
- Fixed TCL glob expression to properly read both .sv and .v files.
  Credit to @pyz-creeper and @dsw for this update!
- Updated error codes in create-fpga-image for unsupported design logic
- Updated the Virtual Ethernet Application to write the DMA buffer
  descriptors using the byte alignment required by the CL_SDE example,
  preventing data alignment errors on Rocky
- `Added Amazon FPGA Image (AFI) creation Python
  script <./hdk/README.html#step-6-submit-generated-dcp-for-afi-creation>`__
- Updated XRT version which includes stability fixes for Vitis

v2.2.0
------

- Release of Vivado/Vitis 2025.1 Tools on `FPGA Developer AMI 1.18.0
  (Ubuntu) <http://aws.amazon.com/marketplace/pp/prodview-tcl7sjgreh6bq>`__
- Introduced `MSI-X PCIe Interrupts Guided
  Example <./sdk/apps/msix-interrupts/README.html>`__
- Added `Loopback performance test for
  CL_SDE <./hdk/cl/examples/cl-sde/software/src/README.html>`__
- `ReadTheDocs navigation
  improvements <https://awsdocs-fpga-f2.readthedocs-hosted.com/latest/>`__

v2.1.2
------

- Introduced Python Bindings to the SDK
- Added `documentation <./sdk/userspace/cython-bindings/README.html>`__
  for Python binding usage and setup
- `Examples <https://github.com/aws/aws-fpga/tree/f2/sdk/userspace/cython_bindings>`__ demonstrating
  Python-based FPGA control
- Added link to instructions for DCV licensing setup. Credit to @morgnza
  for this update!
- Added verbiage to DCV setup guide to show where to set virtual display
  resolution
- Fix to Bandwidth Calculation

v2.1.1
------

- Added global register offset for the SDE IP. See `CL_SDE software
  examples <./hdk/cl/examples/cl-sde/software/src/README.html>`__.
- Added `CL_SDE software example <https://github.com/aws/aws-fpga/tree/f2/hdk/cl/examples/cl_sde/software/src/sde_c2h_user_buffers.c>`__
  for a user allocated DMA buffer.
- `Documentation <./hdk/docs/List-AFI-on-Marketplace.html>`__ to assist F2
  customers with releasing AFIs and AMIs on the AWS Marketplace.
- `Documentation <./developer-resources/Amazon-DCV-Setup-Guide.html>`__ to
  assist in creating a virtual desktop based on the FPGA Developer AMI
  running graphics-intensive applications remotely on Amazon EC2
  instances.
- Fixed the BW calculation and tolerance calculation in the
  test_hbm_perf_random in the
  `cl_mem_perf <./hdk/cl/examples/cl-mem-perf/verif/README.html#system-verilog-tests>`__.

v2.1.0
------

- Support for Vivado and Vitis 2024.2 tools.
- `Releasing New Developer AMI for 2024.2
  tools. <http://aws.amazon.com/marketplace/pp/prodview-tcl7sjgreh6bq>`__
- Updating the asynchronous fpga_mgmt_examples to poll each FPGA once
  before moving to the next.

v2.0.7
------

- Documentation updates to improve
  `ReadTheDocs <https://awsdocs-fpga-f2.readthedocs-hosted.com/latest/>`__
  navigation and inline snippets.
- XSIM template script update to extend the waveform dump time.
- Added section with instructions for assigning custom PCIe IDs to HDK
  `README <./hdk/README.html>`__.
- Added supplementary XDMA driver installation
  `guide <./hdk/docs/XDMA-Install.html>`__
- Updated `ERRATA <./ERRATA.html#hdk>`__ with fix for XSIM when simulating
  HBM.
- Revised the `Vitis README <./vitis/README.html>`__ with updated code
  snippets, more detail about the XRT setup, and a new guided example of
  the Hardware Emulation workflow.
- Fixed HDK DCP Tarball path issue described in
  `#706 <https://github.com/aws/aws-fpga/issues/706>`__.

v2.0.6
------

- Releasing `CL_SDE software
  examples <./hdk/cl/examples/cl-sde/software/src/README.html>`__ to
  demonstrate how to use the `Streaming Data Engine
  (SDE) <./sdk/apps/virtual-ethernet/doc/SDE-HW-Guide.html>`__ DMA on
  `small
  shell <./User-Guide-AWS-EC2-FPGA-Development-Kit.html#aws-shells>`__.
- Fixing the `virtual
  ethernet <./sdk/apps/virtual-ethernet/doc/Virtual-Ethernet-Application-Guide.html#packetgen-dual-instance-loopback>`__
  PacketGen Dual Instance Loopback example to forward packets back to
  the PacketGen instance.
- Fixing DDR backdoor access in simulation.

v2.0.5
------

- Releasing instructions for using the Vivado GUI.
- Updating virtual_ethernet_install.py to no longer require sudo when
  run.
- Updating f2_mgmt_example, load_multiple_fpga.c, to load AFIs in
  parallel.
- Updated ReadTheDocs theme.
- Added the “F2 Software Performance Optimization Guide” with techniques
  for f2.48xlarge instances

v2.0.4
------

- Release of new F2 instance size, **f2.6xlarge**:

.. list-table::
   :header-rows: 1
   :widths: auto

   * - Instance Name
     - FPGAs
     - vCPUs
     - FPGA Memory HBM / DDR4
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
     - 25.0
     - 15
   * - f2.48xlarge
     - 8
     - 192
     - 128 GiB / 512 GiB
     - 2048
     - 8 x 950
     - 100
     - 60

v2.0.3
------

- Releasing fpga_mgmt_examples to demonstrate how the FPGA Management C
  API is used to perform FPGA image slot load and clear operations.
- Releasing the PacketGen Dual Instance Loopback example to the SDK
  Virtual Ethernet Application.
- Fixing the clkgen CLIs to prevent the configuration of clock groups
  that were removed from the AWS_CLK_GEN IP in customer designs.

v2.0.2
------

Updates for initial release of ReadTheDocs documentation and to
re-enable tests for XSIM.

v2.0.1
------

Updates to HDK, SDK, and Vitis documentation. Added check for XRT
install to enable Vitis hardware emulation. XRT install can now be
performed automatically by running a command presented during
``vitis_setup.sh``.

v2.0.0
------

Initial release. F2 general-availability companion.

`Back to Home <./index.html>`__
