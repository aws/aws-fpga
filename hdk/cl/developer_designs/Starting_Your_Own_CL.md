# Starting Your Own Custom Logic (CL)

## Table of Content 
1. [Install HDK](#install)
2. [Create new CL Directory and Setup Environment](#setupDir)
3. [Modify Build Scripts](#modifyBuildScripts)

<a name="install"></a>
## 1. Make sure you have the FPGA HDK installed and the environment variables set up

In case you haven't cloned AWS FPGA HDK+SDK, please follow the next steps to download and configure the HDK to the source directory on the instance:

    $ git clone https://github.com/aws/aws-fpga
    $ cd aws-fpga
    $ source hdk_setup.sh

  
<a name="setupDir"></a>
## 2. Create a new CL directory, environment variable, and reference directory structure

The developer has two ways to start a new Custom Logic design:

 1) Copy one of the example directories from `$HDK_DIR/cl/examples` to `$HDK_DIR/cl/developer_designs`, and make sure to update the `$CL_DIR` environment variable to point to the new design:
 
        $ cd $HDK_DIR/cl/developer_designs
        $ cp -r $HDK_DIR/cl/examples/<example> .
        $ export CL_DIR=$(pwd)

 2) Setup a new CL directory from scratch:
 
        $ cd $HDK_DIR/cl/developer_designs
        $ mkdir <Your_New_CL_Directory>
        $ cd <Your_New_CL_Directory>
        $ export CL_DIR=$(pwd)
        $ source $HDK_DIR/cl/developer_designs/prepare_new_cl.sh
        
Setting up the `$CL_DIR` environment variable is a must as the build scripts rely on that variable.

The `prepare_new_cl.sh` will setup the directory structure to match what's expected by the HDK simulation and build scripts. Execute `source $HDK_DIR/cl/developer_designs/prepare_new_cl.sh` from within the directory you want to use for your CL development.

In both cases, double-check that the `$CL_DIR` is set correctly by calling and checking the result of:

    $ echo $CL_DIR


<a name="modifyBuildScripts"></a>
## 3. Modify the build scripts

The following scripts should be modified before starting the build:
 - `/build/constraints/*`   to set all the timing, clock and placement constraints.
 - `/build/scripts/encrypt.tcl`   CL Encryption is required, AFI creation will fail if your CL source files are not encrypted.  To enable include the source file names.
 - `/build/scripts/create_dcp_from_cl.tcl`   to update the final build scripts with right source files and IP.
        
Once your design is ready and you would like to start the build process, please refer to this [checklist](../CHECKLIST_BEFORE_BUILDING_CL.md).

Once you verified the checklist, the detailed walkthrough on how to build and submit the CL to AWS is avaiable [here](../../common/shell_v04261818/new_cl_template/build/README.md)



