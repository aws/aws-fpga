# HLx Flow for Hello World Example

## Table of Contents

1. [Overview](#overview)
2. [Setup HLx Environment](#env)
3. [Create Example Design (GUI)](#createbdgui)
4. [Create Example Design (Command line)](#createbd)
5. [Simulation](#sim)
6. [DPI Simulation](#dpisim)
7. [Implementing the Design](#impl)
8. [AFI Creation](#aficreation)
9. [CL Example Software and executing on F1](#swf1)

<a name="overview"></a>
### Overview

For more information about the hello\_world example, read the following information [Hello World CL Example](./../cl_hello_world/README.md)

<a name="env"></a>
### Setup HLx Environment

* Clone the github and setup the HDK environment
   ```
   $ git clone https://github.com/aws/aws-fpga.git $AWS_FPGA_REPO_DIR
   $ cd $AWS_FPGA_REPO_DIR
   $ source hdk_setup.sh
   ```
* To setup the HLx Environment, run the following commands:
   ```
   $ mkdir -p ~/.Xilinx/Vivado
   $ echo 'source $env::(HDK_SHELL_DIR)/hlx/hlx_setup.tcl' >> ~/.Xilinx/Vivado/Vivado_init.tcl
   ```
   **NOTE**: *This modifies Vivado defaults, it is recommended you remove this if you wish to run non-HLx examples.* 
   
   For more information please see: [HLx Setup Instructions](../../../../hdk/docs/IPI_GUI_Vivado_Setup.md).

* You will also need to [setup AWS CLI and S3 Bucket](../../../../SDAccel/docs/Setup_AWS_CLI_and_S3_Bucket.md) to enable AFI creation

<a name="createbdgui"></a>
### Create Example Design (GUI)

* To launch Vivado GUI
   * Change directories to the cl/examples/cl_hello_world_hlx directory
   * Invoke Vivado by typing `vivado` in the console
   * In the Vivado TCL Console, enter the following to configure the design
   ```
   set ::env(CLOCK_A_RECIPE) "0"
   set ::env(CLOCK_B_RECIPE) "0"
   set ::env(CLOCK_C_RECIPE) "0"
   set ::env(device_id) "0xF000"
   set ::env(vendor_id) "0x1D0F"
   set ::env(subsystem_id) "0x1D51"
   set ::env(subsystem_vendor_id) "0xFEDD"
   ```
   * In the Vivado TCL Console type in the following to create the cl_hello_world example. The example will be generated in cl/examples/cl_hello_world_hlx/example_projects. The vivado project is examples_projects/cl_hello_world.xpr
   ```
   aws::make_rtl -examples cl_hello_world
   ```

<a name="createbd"></a>
### Create Example Design (Command line)

* Alternatively, to run the Vivado GUI from command line (Linux only)
   * Make sure your $CL_DIR is pointing to the example directory. The following will generate the IPI Block Design (BD)
   ```
   $ cd $HDK_DIR/cl/examples/cl_hello_world_hlx
   $ export CL_DIR=$(pwd)
   $ cd $CL_DIR/build/scripts
   $ ./aws_build_dcp_from_cl.sh -gui
   ```    
   **NOTE**: *The "-gui" switch is optional. It allows you to modify the example design, you will need to have a DISPLAY setup for the GUI to launch. To run the full creation and default implementation flow without the GUI, remove this switch.*

<a name="sim"></a>
### Simulation

* To launch simulation from within the Vivado GUI, 
   * Click on Simulation->Run Simulation->Run Behavioral Simulation
   * Add signals needed in the simulation
   * Type `run -all` in the TCL console

<a name="dpisim"></a>
### DPI Simulation with test\_hello\_world.c

To launch DPI simulation from within the Vivado GUI:
* Right click on SIMULATION in the Project Manager
* Select Simulation Settings
* For Verilog options select the ... box and modify TEST\_NAME to test_null to disable sv stimulus
   ```
   `TEST_NAME = test_null`
   ```
* In the TCL console in Vivado project, copy and paste the following command to set the path for the creation of the .so with test\_hello\_world.c script. If using 3rd party simulators, modify the command to match the simulator and the path to dpi.tcl instead of dpi_xsim.tcl (see IP Integrator - Frequently Asked Questions documentation in using 3rd party simulators)
   ```
   `set_property -name {xsim.compile.tcl.pre} -value $::aws::make_faas::_nsvars::script_dir/../../hlx_examples/build/RTL/cl_hello_world/verif/scripts/dpi_xsim.tcl -objects [get_filesets sim_1]`
   ```
* Right click on SIMULATION in the Project Manager
* Select Simulation Settings
* In the Elaboration tab, for xsim.elaborate.xelab.more_options add in the following value.  Settings can be different based upon the simulator
   ```
   `-sv_lib dpi`
   ```
   **NOTE**: *Certain 3rd party simulators might need the explicit include path to the design directory for provided RTL example designs like cl\_hello\_world and cl\_dram\_dma.  For Verilog options select the ... box and click the + button under Verilog Include Files Search Paths.  Select the path to the cl/cl\_example/design directory.*

<a name="impl"></a>
### Implementing the Design

* To run implmentation from within the GUI is opened, in the Design Runs tab:
   * Right click on impl\_1 in the Design Runs tab and select Launch Runs…
   * Click OK in the Launch Runs Dialog Box.
   * Click OK in the Missing Synthesis Results Dialog Box

This will run both synthesis and implementation.

<a name="aficreation"></a>
### AFI Creation

The completed .tar file is located in: 
```
$CL_DIR/build/scripts/example\_projects/cl\_hello\_world.runs/faas\_1/build/checkpoints/to\_aws/<timestamp>.Developer\_CL.tar  
```
For information on how to create AFI from this tar file, follow the [steps outlined here](../README.md#3-submit-the-design-checkpoint-to-aws-to-create-the-afi).

<a name="swf1"></a>
### CL Example Software and executing on F1

The runtime software must be compiled for the AFI to run on F1.

Use the software in cl/examples/cl\_hello\_world
```
$ cd $HDK_DIR/cl/examples/cl_hello_world/software/runtime/
$ make all
$ sudo ./test_hello_world
```
