# Starting your own Custom Logic

## 1. Make sure you have the FPGA HDK installed and the environment variables set up

In case you haven't cloned AWS FPGA HDK+SDK, please following the next step to download and configure the HDK to the source directory on the instance:

        $ git clone https://github.com/aws/aws-fpga
        $ cd aws-fpga
        $ source hdk_shell.sh

## 2. Create a new CL directory, environment variable, and reference directory structure

The developer has two ways to start a new Custom Logic design:

 1) Copy one of the example directory from `$(HDK_DIR)/cl/examples`, and make sure to set up `CL_DIR` environment variable to point to the new design 
 
 2) Setup a new CL directorty:
 
        $ mkdir Your_New_CL_Directory
        $ cd Your_New_CL_Directory
        $ export CL_DIR=$(pwd)
        $ source $(HDK_DIR)/cl/developer_designs/prepare_new_cl.sh 
        
Setting up the CL_DIR environment variable is crucial as the build scripts rely on that value.

The `prepare_new_cl.sh` would set up the directory structure to match what's expected by the HDK simulation and build scripts.Call `source $(HDK_DIR)/cl/developer_designs/prepare_new_cl.sh` from within the directory you want to use for your CL development

In both cases, double check that the CL_DIR is set correctly by calling and checking the result of:

        $ echo $CL_DIR

## 3. Update the build scripts

The following scripts requires update before starting the build:
        `/build/constraints/*`   to update all the timing, clock and placement constraints
        `/build/scripts/encrypt.tcl`   to update the source file names before encryption
        `/build/scripts/create_dcp_from_cl.tcl`   to update the final build scripts with right source files and IP.
        
Once your design is ready and you would like to start the build/create process, please refer to the [checklist](../CHECKLIST_FOR_CL_BUILD.md)

Once your verified the checklist, you can run:

         $ vivado -mode batch -source $(CL_DIR)/build/scripts/create_dcp_from_cl.tcl
         
**NOTE** *A detailed walkthrough how to build is also available in `$(CL_DIR)/build/scripts/README.md`*


