# HLx Flow for Hello World Ref Example

## Table of Contents

1. [Overview](#overview)
2. [Setup HLx Environment](#env)
3. [Create Example Design (GUI)](#createbdgui)
4. [Create Example Design (Command line)](#createbd)
5. [Simulation](#sim)
6. [Implementing the Design](#impl)
7. [AFI Creation](#aficreation)
8. [CL Example Software and executing on F1](#swf1)

<a name="overview"></a>
### Overview

The cl\_hello\_world\_ref example demonstrates basic Shell-to-CL connectivity, memory-mapped register instantiations and the use of the Virtual LED and DIP switches. The cl\_hello\_world\_ref example implements two registers in the FPGA AppPF BAR0 memory space connected to the OCL AXI-L interface. The two registers are:

1. Hello World Register (offset 0x500)

2. Virtual LED Register (offset 0x504)

The logic for the original cl\_hello\_world example from github is contained in one RTL module (hello\_world.v).  In hello\_world.v, the top level ports are for AXI4Lite interface, clock/reset and ports for VLED and VDIP which allows for IP packaging of the design and reuse with other flows/AXI4Lite Master interfaces.

**NOTE**: *VIO logic is not included with this example from the original cl_hello_world example.*

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
   * Change directories to the cl/examples/cl_hello_world_ref_hlx directory
   * Invoke Vivado by typing `vivado` in the console
   * In the Vivado TCL Console type in the following to create the cl_hello_world_ref_hlx example. The example will be generated in cl/examples/cl_hello_world_ref_hlx/example_projects. The vivado project is examples_projects/cl_hello_world_ref.xpr
   ```
   aws::make_ipi -examples cl_hello_world_ref
   ```
   * Click Refresh Changed Modules on the top of Block Design
   * Once the Block diagram is opened, review the different IP blocks especially the settings in the AWS IP
   
   **NOTE**: *The hello_world RTL is added to the BD and the instance name is hello_world_0. The hello_world.v source is moved in the Sources tab after validating the design under the cl_hello_world_0_0 IP source.*

<a name="createbd"></a>
### Create Example Design (Command line)

* Alternatively, to run the Vivado GUI from command line (Linux only)
   * Make sure your $CL_DIR is pointing to the example directory. The following will generate the IPI Block Design (BD)
   ```
   $ cd $HDK_DIR/cl/examples/cl_hello_world_ref_hlx
   $ export CL_DIR=$(pwd)
   $ cd $CL_DIR/build/scripts
   $ ./aws_build_dcp_from_cl.sh -gui
   ```    
   **NOTE**: *The "-gui" switch is optional. It allows you to modify the example design, you will need to have a DISPLAY setup for the GUI to launch. To run the full creation and default implementation flow without the GUI, remove this switch.*

<a name="sim"></a>
### Simulation

The simulation settings are already configured.

* To launch simulation from within the Vivado GUI, 
   * Click on Simulation->Run Simulation->Run Behavioral Simulation
   * Add signals needed in the simulation
   * Type `run -all` in the TCL console

**NOTE**: *If Critical Warnings appear click OK and that the following command needs to ran two times. This is a known issue and will be addressed in later versions of the design.*

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
$CL_DIR/build/scripts/example_projects/cl_hello_world_ref.runs/faas_1/build/checkpoints/to_aws/<timestamp>.Developer_CL.tar  
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
