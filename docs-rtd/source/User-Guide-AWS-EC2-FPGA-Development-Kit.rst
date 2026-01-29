`AWS EC2 FPGA Development Kit User Guide <https://github.com/aws/aws-fpga>`__
=============================================================================

The development kit includes example designs to get you familiar with
developing for AWS EC2 FPGA Instances.

- `AWS EC2 F2 Instance Overview <#aws-ec2-f2-instance-overview>`__

  - `Instance Types <#instance-types>`__
  - `Second Generation On-Cloud FPGA Accelerator
    Card <#second-generation-on-cloud-fpga-accelerator-card>`__
  - `Comparison to F1 <#comparison-to-f1>`__

- `AWS EC2 F2 FPGA Development
  Kit <#aws-ec2-f2-fpga-development-kit>`__

  - `Development Environments <#development-environments>`__
  - `Quick Start Links <#quick-start-links>`__
  - `AWS Shells <#aws-shells>`__
  - `Hardware Development Kit (HDK) <#hardware-development-kit-hdk>`__
  - `Software-Defined Development
    Environment <#software-defined-development-environment>`__

  - `FPGA Developer AMI <#fpga-developer-ami>`__

  - `Getting Familiar with AWS <#getting-familiar-with-aws>`__

- `Next Steps <#next-steps>`__

.. _aws-ec2-f2-instance-overview:

AWS EC2 F2 Instance Overview
----------------------------

Amazon EC2 F2 instances are Amazon’s second-generation FPGA-powered
instances, purpose-built for customers to develop and deploy
reconfigurable hardware in the cloud. With AMD UltraScale+ VU47P FPGAs
and High Bandwidth Memory (HBM), customers can achieve
orders-of-magnitude application acceleration such as 95x faster graph
database analysis and 10x faster genomics secondary analysis when
compared to CPU-only analysis. F2 instances provide up to 8 FPGAs paired
with a 3rd-generation AMD EPYC (Milan) processor. F2 instances provide
3x more processor cores (192 vCPU), 2x more system memory (2 TiB), 2x
NVMe SSDs (7.6 TiB), and 4x more networking bandwidth (100 Gbps),
compared to the previous generation FPGA-based instances. The
accompanying AWS FPGA Developer kit empowers developers to quickly start
building with their hardware accelerations and adopting advanced
technology, such as HBM, to process data at up to 460 GiB/s.

This documentation is relevant to F2 only. Therefore, it applies to all
branches on the `GitHub repo <https://github.com/aws/aws-fpga>`__
prefixed with ``f2``. Any branches not prefixed f2 in their name are not
referred to in this documentation.

.. _instance-types:

Instance Types
~~~~~~~~~~~~~~

|f2_instances|

.. _second-generation-on-cloud-fpga-accelerator-card:

Second-Generation On-Cloud FPGA Accelerator Card
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

|accel_card_specs|

.. _comparison-to-f1:

Comparison to F1
~~~~~~~~~~~~~~~~

|f2_f1_comp|

AWS EC2 F2 FPGA Development Kit
-------------------------------

.. _development-environments:

Development Environments
~~~~~~~~~~~~~~~~~~~~~~~~

This table lists the F2 development flows currently enabled and
supported in the development kit.

.. list-table::
  :header-rows: 1
  :class: user-guide-dev-envs-table
  :widths: 10 50 20 20 10 15

  * - Development Environment
    - Description
    - Accelerator Language
    - Hardware interface
    - Debug Options
    - Typical Developer
  * - Hardware accelerator development using Vivado (HDK)
    - This environment supports the Hardware Development Kit (HDK) design flow,
      which empowers FPGA developers to create accelerator designs from scratch,
      using HDL source code and IPs. The AMD Vivado tool synthesizes, implements,
      and generates the Design Check Point (DCP) file used in F2 AFI creation.
      AWS FPGA developers benefit from the suite of scripts supplied in the HDK
      that help to automate different design steps. This allows for flexibility
      in architecting, implementing, and optimizing accelerator designs while
      using the HDK.
    - Verilog/System Verilog/VHDL
    - User-implemented DMA engine or Streaming Data Engine (SDE)
    - Simulation and Virtual JTAG
    - Hardware developers with advanced FPGA experience
  * - Hardware accelerator development using Vitis
    - This environment supports the Vitis design flow,
      which enables software developers to write C++ code,
      which may then be compiled into RTL and used in
      cycle-accurate hardware simulation. After it may
      then be built into an accelerator design. This step
      is not necessary, but is encouraged. Vitis may also
      be used to implement accelerator designs from scratch,
      using HDL and IPs directly, similar to Vivado. Vitis
      offers additional analysis tools to aid in the
      refinement of designs.
    - C/C++/Verilog/System Verilog/VHDL
    - XDMA Engine (coming soon)
    - Hardware Emulation
    - Advanced software developers or hardware developers
      with intermediate to advanced FPGA experiences
  * - Hardware accelerator development using Vivado IP Integrator (IPI) and
      High Level Design (HLx)
    - This environment supports the Vivado high-level design flow using IP
      integrator in the GUI.
    - Block Design in IP Integrator
    - AWS IP for HLx
    - Simulation and Virtual JTAG
    - Hardware developers with intermediate FPGA experience

On-premise environment: Customers can set up a on-premise development
environment. See the `supported AMD tool versions here. <#hardware-development-kit-hdk>`__ Refer to
this guide `here <./hdk/docs/on-premise-licensing-help.html>`__ for
licensing requirements.

.. _quick-start-links:

Quick Start Links
~~~~~~~~~~~~~~~~~

.. list-table::
   :header-rows: 1
   :widths: 15 15 30 15 25

   * - Development Environment
     - Example
     - Description
     - Quick-Start Guide
     - Resources
   * - HDK
     - `cl_mem_perf <https://github.com/aws/aws-fpga/tree/f2/hdk/cl/examples/cl_mem_perf>`__
     - Demonstrates fine-tuned paths to memory to maximize bandwidth
     - `Guided Example <./hdk/README.html#getting-started-hdk>`__
     - `Design Spec <./hdk/cl/examples/cl-mem-perf/README.html>`__
   * -
     -
     -
     -
     - `Design Source Code <https://github.com/aws/aws-fpga/tree/f2/hdk/cl/examples/cl_mem_perf/design>`__
   * -
     -
     -
     -
     - `Testbench <https://github.com/aws/aws-fpga/tree/f2/hdk/cl/examples/cl_mem_perf/verif>`__
   * -
     -
     -
     -
     - `Runtime Software <https://github.com/aws/aws-fpga/tree/f2/hdk/cl/examples/cl_mem_perf/software>`__
   * -
     - `cl_dram_hbm_dma <https://github.com/aws/aws-fpga/tree/f2/hdk/cl/examples/cl_dram_hbm_dma>`__
     - Demonstrates connectivity to various internal interfaces from the shell
     -
     - `Design Spec <./hdk/cl/examples/cl-dram-hbm-dma/README.html>`__
   * -
     -
     -
     -
     - `Design Source Code <https://github.com/aws/aws-fpga/tree/f2/hdk/cl/examples/cl_dram_hbm_dma/design>`__
   * -
     -
     -
     -
     - `Testbench <https://github.com/aws/aws-fpga/tree/f2/hdk/cl/examples/cl_dram_hbm_dma/verif>`__
   * -
     -
     -
     -
     - `Runtime Software <https://github.com/aws/aws-fpga/tree/f2/hdk/cl/examples/cl_dram_hbm_dma/software>`__
   * -
     - `cl_sde <https://github.com/aws/aws-fpga/tree/f2/hdk/cl/examples/cl_sde>`__
     - `Demonstrates the use of the Streaming Data Engine (SDE) via the Virtual Ethernet Application <https://github.com/aws/aws-fpga/tree/f2/sdk/apps/virtual-ethernet>`__
     -
     - `Design Spec <./hdk/cl/examples/cl-sde/README.html>`__
   * -
     -
     -
     -
     - `Design Source Code <https://github.com/aws/aws-fpga/tree/f2/hdk/cl/examples/cl_sde/design>`__
   * -
     -
     -
     -
     - `Testbench <https://github.com/aws/aws-fpga/tree/f2/hdk/cl/examples/cl_sde/verif>`__
   * -
     -
     -
     -
     - `Runtime Software <https://github.com/aws/aws-fpga/tree/f2/hdk/cl/examples/cl_sde/software>`__
   * - Vitis
     - `hello_world <https://github.com/Xilinx/Vitis_Accel_Examples/tree/2024.1/hello_world>`__
     - Demonstrates streaming data to the FPGA via the XRT
     - `Guided Example <./vitis/README.html>`__
     - `Design Spec <https://github.com/Xilinx/Vitis_Accel_Examples/blob/main/hello_world/README.rst>`__
   * -
     -
     -
     -
     - `Design Source Code <https://github.com/Xilinx/Vitis_Accel_Examples/blob/main/hello_world/src/vadd.cpp>`__
   * -
     -
     -
     -
     - `Testbench <https://github.com/Xilinx/Vitis_Accel_Examples/blob/main/hello_world/src/host.cpp>`__
   * -
     -
     -
     -
     - `Runtime Software <https://github.com/Xilinx/Vitis_Accel_Examples/blob/main/hello_world/src/host.cpp>`__
   * - HLx
     - `hello_world_hlx <https://github.com/aws/aws-fpga/tree/f2/hdk/cl/examples/cl_ipi_cdma_test_hlx>`__
     - Demonstrates simple register peek and poke using GPIO and VLED
     - `Vivado IPI Setup Guide <./hdk/docs/IPI-GUI-Vivado-Setup.html>`__
     - `Design Spec <./hdk/cl/examples/hello-world-hlx/README.html>`__
   * -
     -
     -
     -
     - `Testbench <https://github.com/aws/aws-fpga-resources/tree/Hlx_1.0-hdk/common/shell_stable/hlx/hlx_examples/build/IPI/hello_world/verif>`__
   * -
     -
     -
     -
     - `Runtime Software <https://github.com/aws/aws-fpga-resources/tree/Hlx_1.0-hdk/common/shell_stable/hlx/hlx_examples/build/IPI/hello_world/software>`__
   * -
     - `hello_world_mb_hlx <https://github.com/aws/aws-fpga/tree/f2/hdk/cl/examples/hello_world_mb_hlx>`__
     - Demonstrates integrating MicroBlaze soft processor in HLx design
     -
     - `Design Spec <./hdk/cl/examples/hello-world-mb-hlx/README.html>`__
   * -
     -
     -
     -
     - `Testbench <https://github.com/aws/aws-fpga-resources/tree/Hlx_1.0-hdk/common/shell_stable/hlx/hlx_examples/build/IPI/hello_world_mb/verif>`__
   * -
     -
     -
     -
     - `Runtime Software <https://github.com/aws/aws-fpga-resources/tree/Hlx_1.0-hdk/common/shell_stable/hlx/hlx_examples/build/IPI/hello_world_mb/software>`__
   * -
     - `cl_ipi_cdma_test_hlx <https://github.com/aws/aws-fpga/tree/f2/hdk/cl/examples/cl_ipi_cdma_test_hlx>`__
     - Demonstrates direct memory access to the DDR and HBM in AWS IP
     -
     - `Design Spec <./hdk/cl/examples/cl-ipi-cdma-test-hlx/README.html>`__
   * -
     -
     -
     -
     - `Testbench <https://github.com/aws/aws-fpga-resources/tree/Hlx_1.0-hdk/common/shell_stable/hlx/hlx_examples/build/IPI/cl_ipi_cdma_test/verif>`__
   * -
     -
     -
     -
     - `Runtime Software <https://github.com/aws/aws-fpga-resources/tree/Hlx_1.0-hdk/common/shell_stable/hlx/hlx_examples/build/IPI/cl_ipi_cdma_test/software>`__

.. _aws-shells:

AWS Shells
~~~~~~~~~~

For AWS EC2 F2 FPGA instances, each FPGA is divided into two partitions:

- Shell (SH) – AWS platform logic implementing system management and
  external peripherals like PCIe and interrupts to the host.
- Custom Logic (CL) – Custom acceleration logic created by the FPGA
  developer and equipped with direct memory access (DMA) to DDR and HBM.

At the end of the development process, combining the Shell and CL
creates an Amazon FPGA Image (AFI) that is then available to load onto
all F2 FPGA cards on instances owned by the developer.

The HDK design flow currently supports the Small Shell. The Small Shell
offers 88% usable FPGA resources. The `common
interface <./hdk/docs/AWS-Shell-Interface-Specification.html>`__ (is
defined in
`cl_ports.vh <https://github.com/aws/aws-fpga/blob/f2/hdk/common/shell_stable/design/interfaces/cl_ports.vh>`__)
along with the `floorplans <./hdk/docs/shell-floorplan.html>`__ and
built-in functions. CL designs must integrate with the small shell. The
table below details the released shell version and its main features.

.. list-table::
  :header-rows: 1
  :class: user-guide-shells-table
  :widths: 20 20 60

  * - Shell Name
    - Shell Version
    - Description
  * - F2 Small Shell
    - 0x10212415
    - Shell with no built-in DMA engine (40% smaller shell footprint).


.. _hardware-development-kit-hdk:

Hardware Development Kit (HDK)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

The Hardware Development Kit (HDK) comes with an ``hdk_setup.sh`` script
to set up environment variables required for customer design development
using HDL source code.

The `HDK directory structure <./hdk/README.html>`__ contains:

- `common/shell_stable <https://github.com/aws/aws-fpga/tree/f2/hdk/common/shell_stable>`__: All build
  scripts, constraints, and other directory structures required to
  support design builds using the supported shells.
- `common/lib <https://github.com/aws/aws-fpga/tree/f2/hdk/common/lib>`__: All common IPs used in various
  examples and Tcl scripts to build IPs are available here.
- `cl/examples <https://github.com/aws/aws-fpga/tree/f2/hdk/cl/examples>`__: Multiple CL examples to
  demonstrate connectivity between CL logic, the F2 Shell, and
  accelerator resources like DDR and HBM.
- Support for 3rd party simulators

The HDK currently supports the following tool versions:

.. list-table::
  :header-rows: 1
  :class: user-guide-simulators-table
  :widths: 30 30 30

  * - AMD Vivado Design Suite
    - Synopsys VCS (Bring your own license)
    - Siemens Questa (Bring your own license)
  * - 2025.1
    - W-2024.09-SP1
    - 2024.3_3
  * - 2024.2
    - V-2023.12-SP1
    - 2024.1_2
  * - 2024.1
    - U-2023.03-SP2
    - 2023.3

Our scripts require a minimum Python version of 3.10, under
``/usr/bin/env python3``:

.. list-table::
  :header-rows: 1
  :class: user-guide-python-table
  :widths: 10 15

  * - Tool
    - Minimum Version
  * - Python
    - 3.10+

.. _software-defined-development-environment:

Software-Defined Development Environment
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

The software-defined development environment allows customers to compile
their C/C++/OpenCL code into AFIs and use C/C++/OpenCL APIs to interface
with the accelerator, running on the FPGA. Software developers with
little or no FPGA experience will be able to quickly familiarize
themselves with the development experience that accelerates cloud
applications. The optimized compiler, Vitis, allows easy F2 accelerator
development using C/C++/OpenCL and/or Verilog/VHDL.

Currently, the F2 developer kit provides development tools for Vitis hardware
emulation.

To get started, please see the `README for a hello world accelerator
example <./vitis/README.html>`__

.. _fpga-developer-ami:

FPGA Developer AMI
~~~~~~~~~~~~~~~~~~

A free-to-use FPGA developer AMI is available for on-cloud F2
development with AMD tools pre-installed on a variety of AWS EC2
instance types. Customers can use this AMI to design, simulate, and
build their designs. The table below lists the FPGA Developer AMI(s)
currently released to customers:

.. list-table::
  :header-rows: 1
  :class: user-guide-dev-ami-table
  :widths: 20 25 20 30

  * - FPGA Developer AMI Version
    - FPGA Developer AMI ID
    - Vivado/Vitis Version Supported
    - Operating System Version
  * - 1.18.0
    - `ami-04b57de2833b499b1 <http://aws.amazon.com/marketplace/pp/prodview-7mukkbz7l2uvu>`__
    - 2025.1
    - Rocky Linux 8.10 (4.18.0-553.36.1.el8_10.x86_64)
  * - 1.18.0
    - `ami-098b2ed4c92602975 <http://aws.amazon.com/marketplace/pp/prodview-tcl7sjgreh6bq>`__
    - 2025.1
    - Ubuntu 24.04 (kernel 6.8.0-1021-aws)
  * - 1.16.1
    - `ami-092fc5deb8f3c0f7d <https://aws.amazon.com/marketplace/pp/prodview-f5kjsenkfkz5u>`__
    - 2024.1
    - Ubuntu 20.04.6 (kernel 5.15)

Given the large size of the FPGA used for F2, AMD tools work best with
at least 4 vCPU’s and 32GiB Memory. We recommend `Compute Optimized and
Memory Optimized instance
types <https://aws.amazon.com/ec2/instance-types/compute-optimized/>`__ to successfully
run the synthesis of acceleration code. Developers may start coding and
run simulations on low-cost `General Purpose instances
types <https://aws.amazon.com/ec2/instance-types/general-purpose/>`__.

Note that the tools used by the HDK are only supported on x86-based EC2
instances (Graviton-based instances are not compatible with the tools).

.. _getting-familiar-with-aws:

Getting Familiar with AWS
~~~~~~~~~~~~~~~~~~~~~~~~~

If you have never used AWS before, we recommend you start with `AWS
getting started training <https://aws.amazon.com/getting-started/>`__,
focusing on the basics of the `AWS EC2 <https://aws.amazon.com/ec2/>`__
and `AWS S3 <https://aws.amazon.com/s3/>`__ services. Understanding the
fundamentals of these services will further enhance the developer
experience with AWS F2 instances and the FPGA Developer Kit.

.. _next-steps:

Next Steps
----------

Before you create your own AWS FPGA design, we recommend that you go
through the `step-by-step quickstart guide for customer hardware
development <./hdk/README.html>`__.

Once developers are familiar with the F2 development kit and the HDK
development environment, we recommend exploring the following contents
to master all the design features and examples offered in the AWS EC2
FPGA Development Kit:

- `Run RTL
  simulations <./hdk/docs/RTL-Simulation-Guide-for-HDK-Design-Flow.html>`__
  provided in CL examples to learn the design verification setup in the
  HDK development environment.
- Familiarize yourself with the `AWS F2 Shell-CL
  interfaces <./hdk/docs/AWS-Shell-Interface-Specification.html>`__, e.g. `the HBM monitor
  interface <./hdk/docs/AWS-Shell-Interface-Specification.html#hbm-monitor-interface>`__
- Examine the `shell
  floorplan <./hdk/docs/shell-floorplan.html>`__ and locations of major
  shell interfaces.
- Deep dive into `CL examples <./hdk/README.html#cl-examples>`__ to
  explore shell-to-CL connectivity, CL resources e.g. DDR and HBM, and
  features e.g. `CL clock generation
  block <./hdk/docs/AWS-CLK-GEN-spec.html>`__.
- Create a custom CL design using the
  `CL_TEMPLATE <./hdk/cl/examples/CL-TEMPLATE/README.html>`__ example.
- Connect to a custom CL design in FPGA through `Virtual
  JTAG <./hdk/docs/Virtual-JTAG-XVC.html>`__ to run hardware debug.

.. |f2_instances| image:: ./_static/instance_sizes.png
.. |accel_card_specs| image:: ./_static/accel_card_specs.png
.. |f2_f1_comp| image:: ./_static/f2_f1_comp.png

`Back to Home <./index.html>`__
