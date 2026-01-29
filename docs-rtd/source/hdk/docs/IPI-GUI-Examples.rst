AWS GUI Workflow with Vivado IP Integrator Quick Start Examples
===============================================================

Table of Contents
-----------------

- `AWS GUI Workflow with Vivado IP Integrator Quick Start
  Examples <#aws-gui-workflow-with-vivado-ip-integrator-quick-start-examples>`__

  - `Table of Contents <#table-of-contents>`__
  - `Overview <#overview>`__
  - `HLx Examples Using IP Integrator
    Flow <#hlx-examples-using-ip-integrator-flow>`__
  - `Tutorial on how to create HLx IPI hello_world example with AXI GPIO and AXI BRAM <#tutorial-on-how-to-create-hlx-ipi-hello-world-example-with-axi-gpio-and-axi-bram>`__

    - `Create Directory Structure and Vivado
      Project <#create-directory-structure-and-vivado-project>`__
    - `Configure the Block Diagram <#configure-the-block-diagram>`__

      - `Configure AWS IP <#configure-aws-ip>`__
      - `Add and Configure AXI GPIO <#add-and-configure-axi-gpio>`__
      - `Add and Configure AXI BRAM <#add-and-configure-axi-bram>`__
      - `Connect the Design <#connect-the-design>`__
      - `Address Editor Tab <#address-editor-tab>`__
      - `Save and Validate the Design <#save-and-validate-the-design>`__

    - `Add Simulation Sources from Example
      Design <#add-simulation-sources-from-example-design>`__

      - `Run Simulation <#run-simulation>`__

    - `Add Design Constraints <#add-design-constraints>`__
    - `Implement the Design Tarball
      File <#implement-the-design-tarball-file>`__
    - `CL Example Software <#cl-example-software>`__

Overview
--------

This document provides an overview of IP Integrator (IPI) examples in
the HLx environment. Before starting, complete the `Vivado Setup
Instructions <./IPI-GUI-Vivado-Setup.html>`__ to familiarize yourself with
the Vivado GUI and IP Integrator.

All examples in this document have been integrated into an automated
flow that directly generates Vivado projects.

.. _hlx-examples-using-ip-integrator-flow:

HLx Examples Using IP Integrator Flow
-------------------------------------

This section provides example designs to help you become familiar with
the automated project generation flow and IP Integrator functionality

Available examples are:

- `hello_world <./../cl/examples/hello-world-hlx/README.html>`__
- `hello_world_mb <./../cl/examples/hello-world-mb-hlx/README.html>`__
- `cl_ipi_cdma_test <./../cl/examples/cl-ipi-cdma-test-hlx/README.html>`__

Click any example link above for detailed design information and getting
started instructions.

.. _tutorial-on-how-to-create-hlx-ipi-hello-world-example-with-axi-gpio-and-axi-bram:

Tutorial on how to create HLx IPI hello_world example with AXI GPIO and AXI BRAM
--------------------------------------------------------------------------------

This tutorial demonstrates how to configure AWS IP with the OCL
interface (AXI4-Lite Master) and the PCIS interface (AXI4 Master),
similar to the ones in the
`hello_world <./../cl/examples/hello-world-hlx/README.html>`__
example.

The AXI GPIO IP controls the virtual LEDs (VLEDs). Writing ``0xAAAA`` to
the AXI GPIO (0x0) slave register drives VLEDs. The VLED value can be
read using the verilog task ``tb.get_virtual_led`` in simulation or
``fpga-get-virtual-led`` on an F2 instance.

The PCIS interface accesses the AXI BRAM, where the ASCII string 'Hello
World!' can be written to a BRAM location and read back for display in
either the simulation environment or on an F2 instance.

Create Directory Structure and Vivado Project
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Change directories to ``hdk/cl/examples``

Create a directory in examples like ``hello_world_hlx_ipi``

Change directories into ``hello_world_hlx_ipi/``

Start Vivado by typing ``vivado`` in the bash console.

Create a project any device by typing the following command in Vivado's
TCL Tab.

.. code:: Tcl

   create_project -name hello_world

Enter the following Tcl command to configure AWS project settings and
create a block diagram with AWS IP:

.. code:: Tcl

   aws::make_ipi

Configure the Block Diagram
~~~~~~~~~~~~~~~~~~~~~~~~~~~

Configure AWS IP
^^^^^^^^^^^^^^^^

Configure the AWS IP block by double-clicking it and selecting three
interfaces under 'IP Interfaces': 'Use OCL Register Interface
(M_AXI_OCL)', 'Use PCI Slave-access Interface (M_AXI_PCIS)', and 'Use
Auxiliary (non-AXI) Signal Ports'. For clock configuration, use Group-A
Clock with the default clock recipe to set a 250 MHz frequency.

Add and Configure AXI GPIO
^^^^^^^^^^^^^^^^^^^^^^^^^^

Right-click in the canvas and select 'Add IP...', then search for and
double-click 'AXI GPIO'. Once added, double-click the ``axi_gpio_0`` block
in the canvas. In the 'Re-customize IP' dialog box, select 'All Outputs'
under the GPIO section and set GPIO Width to 16, then click 'OK'.

Add and Configure AXI BRAM
^^^^^^^^^^^^^^^^^^^^^^^^^^

Right-click in the canvas and select 'Add IP...', then search for and
double-click 'AXI BRAM Controller'. Once added, double-click the
``axi_bram_ctrl_0`` block in the canvas and set the Data Width to 512 to
match the PCIS AXI4 Master Interface's data width, then click 'OK'.

Connect the Design
^^^^^^^^^^^^^^^^^^

Click 'Run Connection Automation' at the top of the Block Diagram.
Configure the AXI BRAM controller by setting both
``axi_bram_ctrl_0/BRAM_PORTA`` and ``BRAM_PORTB`` to 'Auto', then set
``axi_bram_ctrl_0/S_AXI`` Master to ``f2_inst/M_AXI_PCIS`` with
remaining options as 'Auto'. For the AXI GPIO, set ``axi_gpio_0/S_AXI``
Master to ``f2_inst/M_AXI_OCL`` with other options as 'Auto', then click
'OK'.

After completing the automation, expand ``axi_gpio_0/GPIO`` by clicking
the + symbol. Connect ``gpio_io_o[15:0]`` from the ``f2_inst`` block to
``status_vled[15:0]``, then run 'Connection Automation'.

Address Editor Tab
^^^^^^^^^^^^^^^^^^

In the 'Address Editor' tab above the block diagram, you can view the
address configurations: the AXI BRAM instance has a default 64K address
space starting at ``0xC0000000`` (adjustable by modifying the Range
value), while the AXI GPIO instance uses a 4K address space with
M_AXI_OCL starting at ``0x00000000``.

Save and Validate the Design
^^^^^^^^^^^^^^^^^^^^^^^^^^^^

Save the block diagram, then select 'Tools' -> 'Validate Design' and
click 'OK' when validation completes successfully.

Add Simulation Sources from Example Design
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

To add simulation sources, navigate to 'Project Manager' in the 'Flow
Navigator' and select 'Add Sources' -> 'Add or create simulation
sources' -> 'Select Add Files'. Add the test file
`test_cl.sv` from `hdk/common/shell_stable/hlx/hlx/hlx_examples/build/IPI/<EXAMPLE_NAME>/verif`
directory, and ensure you deselect the option to scan and add RTL include files.

Configure the following simulation settings to import source files from external
directories instead of copying them to the Vivado project:

1. Source file options:

   - Deselect 'Copy sources into project' (creates links instead)
   - Select 'Add sources from subdirectories'
   - Enable 'Include all design sources for simulation'
   - Click 'Finish'

2. Simulation settings:

   - Right-click 'SIMULATION' in Project Manager
   - Select 'Simulation Settings'
   - In Verilog options, click the '...' box
   - Verify/update the following:

     - CL_NAME=cl_top
     - TEST_NAME=test_cl

   - Click 'OK'
   - Click 'Apply'
   - Click 'OK' to return to Vivado project

Run Simulation
^^^^^^^^^^^^^^

From the 'Flow Navigator' tab, select 'Simulation' -> 'Run Simulation'
-> 'Run Behavioral Simulation', then add your required simulation
signals. In the Tcl console, enter the following command.

.. code:: Tcl

   run -all

Note: If critical warnings appear, click 'OK' and run the command twice
(this is a known issue that will be addressed in future versions).

Add Design Constraints
~~~~~~~~~~~~~~~~~~~~~~

No additional constraints are needed for this design.

Implement the Design Tarball File
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

To implement the design, launch implementation:

- Right-click 'impl_1'
- Select 'Launch Runs...'
- Click 'OK'
- Click 'OK' on the 'Missing Synthesis Results' dialog

This process will run both synthesis and implementation.

The completed tarball file is located in:

.. code:: bash

   <hlx_example_name>/example_projects/<hlx_example_name>.runs/faas_1/build/checkpoints/to_aws/<timestamp>.Developer_CL.tar

For instructions on creating an F2 AFI from the design tarball, see
`Submit Generated DCP for AFI
Creation <./../README.html#step-6-submit-generated-dcp-for-afi-creation>`__
in the HDK quick start guide.

CL Example Software
~~~~~~~~~~~~~~~~~~~

Compile the runtime software required for F2 instance execution by
copying the software directory to your target location and running these
commands:

.. code:: bash

   cp -r $HDK_COMMON_DIR/shell_stable/hlx/hlx_examples/build/IPI/hello_world/software .
   cd software
   make all
   sudo ./test_cl

HLx IPI CL Examples
-------------------
.. toctree::
  :maxdepth: 1

  ./../cl/examples/hello-world-hlx/README
  ./../cl/examples/hello-world-mb-hlx/README
  ./../cl/examples/cl-ipi-cdma-test-hlx/README

`Back to Vivado IPI GUI Setup Guide <./IPI-GUI-Vivado-Setup.html>`__
