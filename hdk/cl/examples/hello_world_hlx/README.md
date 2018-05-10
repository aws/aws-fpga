# HLx Flow for Hello World IP Integrator Example

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

This IP Integrator design contains the AWS IP configured for BAR1 Interface (AXI4Lite Master Interface) for AXI GPIO to control the VLED and the PCIS Interface (AXI4 Master) to write and read into the AXI BRAM located in the CL.

The VLED is set based upon writing 0xAAAA into the AXI GPIO (0x0) slave register to drive VLED. The value is read using the Verilog task tb.get_virtual_led or fpga-get-virtual-led on F1.

The PCIS Interfaces writes ASCII data into the AXI BRAM memory space and reads back from these address to print out “Hello World!” in simulation or on F1.

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
   * Change directories to the cl/examples/hello_world_hlx directory
   * Invoke Vivado by typing `vivado` in the console
   * In the Vivado TCL console type in the following to create the hello_world_hlx example. The example will be generated in cl/examples/hello_world_hlx/example_projects. The vivado project is examples_projects/hello_world.xpr
   ```
   aws::make_ipi -examples hello_world
   ```
   * Once the Block diagram is opened, review the different IP blocks especially the settings in the AWS IP

<a name="createbd"></a>
### Create Example Design (Command line)

* Alternatively, to run the Vivado GUI from command line (Linux only)
   * Make sure your $CL_DIR is pointing to the example directory. The following will generate the IPI Block Design (BD)
   ```
   $ cd $HDK_DIR/cl/examples/hello_world_hlx
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
$CL_DIR/build/scripts/example_projects/hello_world.runs/faas_1/build/checkpoints/to_aws/<timestamp>.Developer_CL.tar
```
For information on how to create AFI from this tar file, follow the [steps outlined here](../README.md#3-submit-the-design-checkpoint-to-aws-to-create-the-afi).

<a name="swf1"></a>
### CL Example Software and executing on F1

The runtime software must be compiled for the AFI to run on F1.

Copy the software directory to any directory and compile with the following commands:
```
$ cp -r $HDK_COMMON_DIR/shell_stable/hlx/hlx_examples/build/IPI/hello_world/software <any_directory>
$ cd software
$ make all
$ sudo ./test_cl
```
