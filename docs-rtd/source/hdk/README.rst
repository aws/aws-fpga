AWS FPGA Hardware Development Kit (HDK)
=======================================

Table of Contents
-----------------

- `AWS FPGA Hardware Development Kit
  (HDK) <#aws-fpga-hardware-development-kit-hdk>`__

  - `Table of Contents <#table-of-contents>`__
  - `HDK Overview <#hdk-overview>`__
  - `Getting Started <#getting-started>`__

    - `Build Accelerator AFI using HDK Design
      Flow <#build-accelerator-afi-using-hdk-design-flow>`__

      - `Step 1. Setup Development
        Environment <#step-1-setup-development-environment>`__
      - `Step 2. Clone Developer Kit
        Repository <#step-2-clone-developer-kit-repository>`__
      - `Step 3. Setup Environment for HDK Design
        Flow <#step-3-setup-environment-for-hdk-design-flow>`__
      - `Step 4. Build CL Design Check Point
        (DCP) <#step-4-build-cl-design-check-point-dcp>`__
      - `Step 5. Explore Build
        Artifacts <#step-5-explore-build-artifacts>`__
      - `Step 6. Submit Generated DCP for AFI
        Creation <#step-6-submit-generated-dcp-for-afi-creation>`__
      - `Step 7. Load Accelerator AFI on F2
        Instance <#step-7-load-accelerator-afi-on-f2-instance>`__
      - `Step 8. Validate your AFI using Example Runtime
        Software <#step-8-validate-your-afi-using-example-runtime-software>`__

  - `CL Examples <#cl-examples>`__

    - `cl_sde <#cl-sde>`__
    - `cl_dram_hbm_dma <#cl-dram-hbm-dma>`__
    - `cl_mem_perf <#cl-mem-perf>`__
    - `CL_TEMPLATE - Create Your Own Design <#cl-template-create-your-own-design>`__

  - `CL Example Hierarchy <#cl-example-hierarchy>`__

    - `Design <#design>`__
    - `Verification <#verification>`__
    - `Software <#software>`__
    - `Build <#build>`__

  - `Common Libraries <#common-libraries>`__

    - `shell_stable/ <#shell-stable>`__
    - `verif/ <#verif>`__
    - `/ip <#ip>`__
    - `/lib <#lib>`__

  - `Next Steps <#next-steps>`__

HDK Overview
------------

The HDK design flow enables developers to create RTL-based accelerator
designs for F2 instances using AMD Vivado. HDK designs must be
integrated with Small Shell, which does not include a built-in Direct
Memory Access (DMA) engine and offers full resources in the top Super
Logic Region (SLR) of the FPGA to developers.

Getting Started
---------------

Build Accelerator AFI using HDK Design Flow
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

This section provides a step-by-step guide to build an F2 AFI using the
HDK design flow. The flow starts with an existing Customer Logic (CL)
example design. Steps 1 through 3 demonstrate how to set up the HDK
development environment. Steps 4 through 5 show the commands used to
generate CL Design Checkpoint (DCP) files and other build artifacts.
Steps 6 and 7 demonstrate how to submit the DCP file to generate an AFI
for use on F2 instances.

.. _step-1-setup-development-environment:

Step 1. Setup Development Environment
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

Developers can either use the AWS-provided developer AMI for F2 or their
on-premise development environment for this demo.

.. _step-2-clone-developer-kit-repository:

Step 2. Clone Developer Kit Repository
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

.. code:: bash

  git clone https://github.com/aws/aws-fpga.git

.. _step-3-setup-environment-for-hdk-design-flow:

Step 3. Setup Environment for HDK Design Flow
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

The `hdk_setup.sh <https://github.com/aws/aws-fpga/tree/f2/hdk_setup.sh>`__ script needs to be sourced for
each terminal and takes ~2 minutes to complete when first run.

.. code:: bash

  cd aws-fpga
  source hdk_setup.sh

After the setup is done successfully, you should see
``AWS HDK setup PASSED``. Sourcing ``hdk_setup.sh`` does the following:

- Verifies a supported Vivado installation
- Sets up all environment variables required by the HDK design flow
- Generates IP simulation models for CL examples
- Downloads all required shell files from a shared S3 bucket

.. _step-4-build-cl-design-check-point-dcp:

Step 4. Build CL Design Check Point (DCP)
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

After the HDK design environment is set up, you are ready to build a
design example. Run the following commands to build CL DCP files in
Vivado. This tutorial uses the `cl_sde <https://github.com/aws/aws-fpga/tree/f2/hdk/cl/examples/cl_sde>`__
example. The same steps can be used for any other `CL
examples <https://github.com/aws/aws-fpga/tree/f2/hdk/cl/examples>`__.

.. code:: bash

  cd hdk/cl/examples/cl_sde
  export CL_DIR=$(pwd)
  cd build/scripts
  ./aws_build_dcp_from_cl.py -c cl_sde

The Shell supplies two base clocks to the CL: a 250MHz ``clk_main_a0`` clock and
a 100MHz ``clk_hbm_ref`` clock. However, the CL can run at higher frequencies
using locally generated clocks. F2 Developer Kit offers an
`AWS Clock Generation (AWS_CLK_GEN) IP <./docs/AWS_CLK_GEN_spec.html>`__
that you can leverage in your design to generate CL clocks with frequencies
specified in the `Clock Recipes User Guide <./docs/Clock_Recipes_User_Guide.html>`__.

Run the command below to build a DCP with desired clock recipes:

.. code:: bash

  ./aws_build_dcp_from_cl.sh -c cl_mem_perf --aws_clk_gen --clock_recipe_a A1 --clock_recipe_b B2 --clock_recipe_c C0 --clock_recipe_hbm H2

**NOTE**: The `cl_sde <./cl/examples/cl_sde/README.html>`__ example does not contain
the AWS_CLK_GEN component. This command uses the `cl_mem_perf <./cl/examples/cl_mem_perf/README.html>`__
example to demonstrate the AWS_CLK_GEN usage.

A few more notes on
`./aws_build_dcp_from_cl.py <https://github.com/aws/aws-fpga/blob/-/hdk/common/shell_stable/build/scripts/aws_build_dcp_from_cl.py>`__:

- Use ``--mode small_shell`` option to build CL designs with Small
  Shell.
- Use ``--cl <CL name>`` option to build a different CL design. This is
  default to ``cl_dram_hbm_dma``.
- Use ``--aws_clk_gen`` option to annotate the use of the `AWS_CLK_GEN IP <./docs/AWS_CLK_GEN_spec.html>`__ and the `Clock Recipes User Guide <./docs/Clock_Recipes_User_Guide.html>`__.
- The script also allows developers to pass different Vivado directives
  as shown below:

  - ``--place <directive>``: Default to ``SSI_SpreadLogic_high``
    placement strategy. Please refer to `Vivado User
    Guide <https://docs.amd.com/r/en-US/ug904-vivado-implementation/Available-Directives>`__
    for supported directives.
  - ``--phy_opt <directive>`` : Default to ``AggressiveExplore``
    physical optimization strategy. Please refer to `Vivado User
    Guide <https://docs.amd.com/r/en-US/ug904-vivado-implementation/Using-Directives?tocId=9xJiGeSV35ApxUsX7pAVDg>`__
    for supported directives
  - ``--route <directive>`` : Default to ``AggressiveExplore`` routing
    strategy. Please refer to `Vivado User
    Guide <https://docs.amd.com/r/en-US/ug904-vivado-implementation/Using-Directives?tocId=dV9wYjuIP6n9oUJhkoHuRg>`__
    for supported directives.

- Run ``./aws_build_dcp_from_cl.py --help`` to see more build options
  available in building CL designs.

.. _step-5-explore-build-artifacts:

Step 5. Explore Build Artifacts
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

While Vivado is running, a build log file
``YYYYY_MM_DD-HHMMSS.vivado.log`` will be created in
``$CL_DIR/build/scripts`` to track the build's progress. DCP build times
will vary based on the design size and complexity. The examples in the
development kit take between 30 to 90 minutes to build. After the design
is finished building, the following information will be shown at the
bottom of the log file:

.. code:: bash

   tail <YYYYY_MM_DD-HHMMSS.vivado.log>

       ...
       AWS FPGA: (16:05:44): Finished building design checkpoints for customer design cl_sde
       ...
       INFO: [Common 17-206] Exiting Vivado at ...

Generated post-route DCP and design manifest files are archived into a
tarball file ``<YYYY_MM_DD-HHMMSS>.Developer_CL.tar`` and saved in the
``$CL_DIR/build/checkpoints/`` directory. All design timing reports are
saved in the ``$CL_DIR/build/reports/`` directory.

⚠️ If Vivado cannot achieve timing closure for the design, the
post-route DCP file name will be marked with ``.VIOLATED`` as an
indicator. Developers need to refer to the DCPs and timing reports for
detailed timing failures.

⚠️ The build process will generate a DCP tarball file regardless of the
design's timing closure state. However, in case of a DCP with timing
failures, the design's functionality is no longer guaranteed. Therefore,
the AFI created using this DCP should be used for testing purpose ONLY.
The following warning is shown in this case:

.. code:: text

   !!! WARNING: Detected a post-route DCP with timing failure for AFI creation. Design functionalities are NOT guaranteed.

.. _step-6-submit-generated-dcp-for-afi-creation:

Step 6. Submit Generated DCP for AFI Creation
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

To submit the DCP, create an S3 bucket and upload the DCP tarball file
to the bucket. DCP submission requires the following information:

- Name of the design (Optional).
- Generic description of the logic design (Optional).
- Destination location of the tarball file object in your S3 bucket.
- Destination location of an S3 directory where AWS can save the logs
  for your AFI's creation.

To upload your tarball file to S3, you can use any of the
`tools supported by S3
<https://docs.aws.amazon.com/AmazonS3/latest/userguide/upload-objects.html>`__.

For example, you can use the AWS CLI as follows:

Create a bucket and folder for your tarball, then copy to S3.

Currently, ``us-east-1`` and ``eu-west-2`` are available as ``REGION`` options.

.. code:: bash

  export DCP_BUCKET_NAME='<DCP bucket name>'
  export DCP_FOLDER_NAME='<DCP folder name>'
  export REGION='us-east-1'
  export DCP_TARBALL_TO_INGEST='<$CL_DIR/build/checkpoints/to_aws/YYYY_MM_DD-HHMMSS.Developer_CL.tar>'

  # Create an S3 bucket (choose a unique bucket name)
  aws s3 mb s3://${DCP_BUCKET_NAME} --region ${REGION}
  # Create folder for your tarball files
  aws s3 mb s3://${DCP_BUCKET_NAME}/${DCP_FOLDER_NAME}/
  # Upload the file to S3
  aws s3 cp ${DCP_TARBALL_TO_INGEST} s3://${DCP_BUCKET_NAME}/${DCP_FOLDER_NAME}/

**NOTE**: The trailing '/' is required after ``${DCP_FOLDER_NAME}``

Create a folder for your log files

.. code:: bash

  export LOGS_BUCKET_NAME='<logs bucket name>'
  export LOGS_FOLDER_NAME='<logs folder name>'

  # Create a folder to keep your logs
  aws s3 mb s3://${LOGS_BUCKET_NAME}/${LOGS_FOLDER_NAME}/ --region ${REGION}
  # Create a temp file
  touch LOGS_FILES_GO_HERE.txt
  # Create the folder on S3
  aws s3 cp LOGS_FILES_GO_HERE.txt s3://${LOGS_BUCKET_NAME}/${LOGS_FOLDER_NAME}/

**NOTE**: The trailing '/' is required after ``${LOGS_FOLDER_NAME}``

The output of this command includes two identifiers for your AFI:

.. code:: bash

  export DCP_TARBALL_NAME=$(basename ${DCP_TARBALL_TO_INGEST})
  export CL_DESIGN_NAME='<cl_design_name>'
  export CL_DESIGN_DESCRIPTION='Description of ${CL_DESIGN_NAME}'

  # Call AWS CLI ingestion command
  aws ec2 create-fpga-image --name ${CL_DESIGN_NAME} --description "${CL_DESIGN_DESCRIPTION}" --input-storage-location Bucket=${DCP_BUCKET_NAME},Key=${DCP_FOLDER_NAME}/${DCP_TARBALL_NAME} --logs-storage-location Bucket=${LOGS_BUCKET_NAME},Key=${LOGS_FOLDER_NAME}/ --region ${REGION}

  {
      "FpgaImageId": "afi-09953582f46c45b17",
      "FpgaImageGlobalId": "agfi-0925b211f5a81b071"
  }

- ``FpgaImageId`` or AFI ID: This is the main ID used to manage
  developer's AFI through the AWS EC2 CLI and AWS SDK APIs. This ID is
  regional, i.e., if an AFI is copied across multiple regions, it will
  have a different, unique AFI ID in each region.

- ``FpgaImageGlobalId`` or AGFI ID: This is a global ID used to refer to
  an AFI from within an F2 instance. For example, to load or clear an
  AFI from an FPGA slot, developers need to use the AGFI ID. Since the
  AGFI IDs is global (by design), it allows developers to copy a
  combination of AFI/AMI to multiple regions and they will work without
  any extra setup.

The ``describe-fpga-images`` command allows developers to check the
AFI's state while the AFI creation process runs in the background. The
AFI ID returned by the ``create-fpga-image`` command must be provided.
The AFI is ready to be deployed once the creation completes and the
state code returned is ``available``.

.. code:: bash

  aws ec2 describe-fpga-images --fpga-image-ids afi-09953582f46c45b17 --region us-east-1

      ...

      {
          "FpgaImages": [
              {
                  "FpgaImageId": "afi-09953582f46c45b17",
                  "FpgaImageGlobalId": "agfi-0925b211f5a81b071",
                  "Name": "cl_sde_0x10212415",
                  "Description": "Latest devkit build of cl_sde with 0x10212415 small shell release",
                  ...
                  "State": {
                      "Code": "available"
                  },
                  ...
              }
          ]
      }

.. _step-7-load-accelerator-afi-on-f2-instance:

Step 7. Load Accelerator AFI on F2 Instance
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

Now that your AFI is available, it can be tested on an F2 instance. The
instance can be launched using any preferred AMI, private or public,
from the AWS Marketplace catalog. AWS recommends using AMIs with Ubuntu
20.04 and kernel version 5.15.

Now you need to install the FPGA Management tools by sourcing the
``sdk_setup.sh`` script:

.. code:: bash

  cd aws-fpga
  source sdk_setup.sh

Once the tools are installed, you can load the AFI onto a slot on the F2
instance. It is a good practice to clear any previously loaded AFI from
that slot:

.. code:: bash

  $ sudo fpga-clear-local-image  -S 0
  AFI          0       No AFI                  cleared           1        ok               0       0x10212415
  AFIDEVICE    0       0x1d0f      0x9048      0000:00:1e.0

You can also invoke the ``fpga-describe-local-image`` command to learn
which AFI, if any, is loaded onto a particular slot. For example, if the
slot is cleared (``slot 0`` in this example), you should get an output
similar to the following:

.. code:: bash

  $ sudo fpga-describe-local-image -S 0 -H
  Type  FpgaImageSlot  FpgaImageId             StatusName    StatusCode   ErrorName    ErrorCode   ShVersion
  AFI          0       No AFI                  cleared           1        ok               0       0x10212415
  Type  FpgaImageSlot  VendorId    DeviceId    DBDF
  AFIDEVICE    0       0x1d0f      0x9048      0000:00:1e.0

If ``fpga-describe-local-image`` API call returns a status ``busy``, the
FPGA is still performing the previous operation in the background.
Please wait until the status is ``cleared`` as above.

Now, let's load your AFI onto the FPGA on ``slot 0``:

.. code:: bash

  $ sudo fpga-load-local-image -S 0 -I agfi-0925b211f5a81b071
  AFI          0       agfi-0925b211f5a81b071  loaded            0        ok               0       0x10212415
  AFIDEVICE    0       0x1d0f      0x9048      0000:00:1e.0

**NOTE**: *The FPGA Management tools use the AGFI ID (not the AFI ID).*

Now, you can verify that the AFI was loaded properly. The output shows
the FPGA in the ``loaded`` state after the FPGA image “load” operation.
The ``-R`` option performs a PCI device remove and rescan in order to
expose the unique AFI Vendor and Device Id.

.. code:: bash

  Type  FpgaImageSlot  FpgaImageId             StatusName    StatusCode   ErrorName    ErrorCode   ShVersion
  AFI          0       agfi-0925b211f5a81b071  loaded            0        ok               0       0x10212415
  Type  FpgaImageSlot  VendorId    DeviceId    DBDF
  AFIDEVICE    0       0x1d0f      0x9048      0000:00:1e.0

.. _step-8-validate-your-afi-using-example-runtime-software:

Step 8. Validate your AFI using Example Runtime Software
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

Each CL example includes a runtime software binary, located in the
``$CL_DIR/software/runtime/`` subdirectory. Executing the software
requires the corresponding AFI to be loaded onto the FPGA. This step
demonstrates runtime software execution using the ``CL_SDE`` example.

.. code:: bash

  # Ensure the $CL_DIR is pointing to the CL_SDE example directory
  $ cd $CL_DIR/software/runtime/
  $ make

  ...

  Logical Core 1 (socket 0) forwards packets on 1 streams:
    RX P=0/Q=0 (socket 0) -> TX P=0/Q=0 (socket 0) peer=02:00:00:00:00:00

    io packet forwarding packets/burst=32
    nb forwarding cores=1 - nb forwarding ports=1
    port 0: RX queue number: 1 Tx queue number: 1
      Rx offloads=0x0 Tx offloads=0x0
      RX queue: 0
        RX desc=0 - RX free threshold=0
        RX threshold registers: pthresh=0 hthresh=0  wthresh=0
        RX Offloads=0x0
      TX queue: 0
        TX desc=0 - TX free threshold=0
        TX threshold registers: pthresh=0 hthresh=0  wthresh=0
        TX offloads=0x0 - TX RS bit threshold=0
  Press enter to exit

  Telling cores to stop...
  Waiting for lcores to finish...

    ---------------------- Forward statistics for port 0  ----------------------
    RX-packets: 10771136       RX-dropped: 0             RX-total: 10771136
    TX-packets: 8160479        TX-dropped: 2610689       TX-total: 10771168
    ----------------------------------------------------------------------------

    +++++++++++++++ Accumulated forward statistics for all ports+++++++++++++++
    RX-packets: 10771136       RX-dropped: 0             RX-total: 10771136
    TX-packets: 8160479        TX-dropped: 2610689       TX-total: 10771168
    ++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++

  Done.

  Stopping port 0...
  Stopping ports...
  Done

  Shutting down port 0...
  Closing ports...
  Done

  Bye...

CL Examples
-----------

All examples have the following features:

- Simulation model, tests, and scripts
- Xilinx Vivado implementation scripts for generating bitstream


cl_sde
~~~~~~

The cl_sde example implements the Streaming Data Engine (SDE) IP block
into FPGA custom logic to demonstrate the `Virtual Ethernet Application
<../sdk/apps/virtual-ethernet/doc/Virtual_Ethernet_Application_Guide.html>`__.

See `cl_sde <https://github.com/aws/aws-fpga/tree/f2/hdk/cl/examples/cl_sde>`__
for more information


cl_dram_hbm_dma
~~~~~~~~~~~~~~~

The cl_dram_hbm_dma example demonstrates the use and connectivity for
many of the Shell/CL interfaces and functionality. The OCL (AXI-Lite)
interface is used for general configuration, the PCIS (AXI4) interface
is used for data traffic from the host to DDR and HBM DRAM channels in
the CL (initiated by the host), and the PCIM (AXI4) interface is used
for data traffic between the host and the CL (initiated by the CL).

See `cl_dram_hbm_dma
<https://github.com/aws/aws-fpga/tree/f2/hdk/cl/examples/cl_dram_hbm_dma>`__
for more information


cl_mem_perf
~~~~~~~~~~~

The cl_mem_perf is a reference design for F2 where the objective is to
demonstrate fine tuned data paths to HBM and DDR to achieve maximum
throughput to the memories. The example also demonstrates datapath
connectivity between Host, AWS Shell, Custom Logic (CL) region in the
FPGA, HBM and DDR DIMM on the FPGA card.

See `cl_mem_perf
<https://github.com/aws/aws-fpga/tree/f2/hdk/cl/examples/cl_mem_perf>`__
for more information


CL_TEMPLATE - Create Your Own Design
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

CL_TEMPLATE is targeted to help customers create a new CL
example. Users can update the design, verification, and build flow to
meet their needs without having to tear down a separate example. We
recommend going through other CL examples before creating a new CL.

All of the design files and tests can be compiled, simulated, built, and
deployed on hardware (without any modifications). Users can add/update
design files, add new verification tests, and add new build directives
to meet their needs.

A full guide on creating your own CL design can be found in
`CL_TEMPLATE <https://github.com/aws/aws-fpga/tree/f2/hdk/cl/examples/CL_TEMPLATE>`__

To create a new CL example:

.. code:: bash

   export NEW_CL_NAME='New CL Name'
   cd hdk/cl/examples
   ./create_new_cl.py --new_cl_name ${NEW_CL_NAME}


CL Example Hierarchy
--------------------

The following sections describe common functionality across all CL
examples. `CL_TEMPLATE
<https://github.com/aws/aws-fpga/tree/f2/hdk/cl/examples/CL_TEMPLATE>`__ can be
used as a reference for what features are available in all CL examples; as well
as what's required to verify, test, and build.

Design
~~~~~~

- All CL examples store the design files under ``/hdk/cl/examples/$CL_DIR/design/``

  - For example:
    `hdk/cl/examples/CL_TEMPLATE/design/
    <https://github.com/aws/aws-fpga/tree/f2/hdk/cl/examples/CL_TEMPLATE/design/>`__

- All IP designs available by default are stored under ``/hdk/common/ip/cl_ip/``

  - More can be added from the Xilinx Vivado IP catalog

Verification
~~~~~~~~~~~~

- All CL examples utilize infrastructure found under ``/hdk/common/verif/``

- Simulation libraries are generated under
  ``hdk/common/verif/ip_simulation_libraries/``

- All examples should list out the
  ``hdk/cl/examples/$CL_DIR/verif/tests/`` and ``Makefile.tests``

  - For example, `hdk/cl/examples/CL_TEMPLATE/verif/tests/ <https://github.com/aws/aws-fpga/tree/f2/hdk/cl/examples/CL_TEMPLATE/verif/tests/>`__ and
  - `hdk/cl/examples/CL_TEMPLATE/verif/scripts/Makefile.tests <https://github.com/aws/aws-fpga/tree/f2/hdk/cl/examples/CL_TEMPLATE/verif/scripts/Makefile.tests>`__

- All HDK examples support a SH_DDR with 64GB access with an optional
  user controlled auto-precharge mode. Users can select the DDR access
  modes as follows:

  .. code:: bash

    export TEST_NAME=test_ddr

    # To Run simulations with a 64 GB DDR DIMM
    make TEST=${TEST_NAME} USE_64GB_DDR_DIMM=1

    # To Run simulations with a 64 GB DDR DIMM and DDR core with user controlled auto-precharge mode
    make TEST=${TEST_NAME} USE_AP_64GB_DDR_DIMM=1

  **NOTE**: Please refer to the `Supported DDR Modes
  <./docs/Supported_DDR_Modes.html>`__ for details on supported DDR
  configurations.

- After adding new design IPs, make sure to add the new simulation libraries to
  ``COMMON_LIBLISTS`` in `hdk/common/verif/tb/scripts/Makefile.common.inc
  <https://github.com/aws/aws-fpga/tree/f2/hdk/common/verif/tb/scripts/Makefile.common.inc>`__

  **NOTE**: This step is required for XSIM and Questa simulators

  - Simulation libraries can be found in
    `hdk/common/ip/cl_ip/cl_ip.ip_user_files/sim_scripts
    <https://github.com/aws/aws-fpga/tree/f2/hdk/common/ip/cl_ip/cl_ip.ip_user_files/sim_scripts>`__
    followed by ``"IP_NAME"/"SIMULATOR"/"IP_NAME".sh``

- Adding new IPs requires to recompile the simulation libraries

  .. code:: bash

    make regenerate_sim_libs <XSIM/VCS/QUESTA>=1


Software
~~~~~~~~

All software runtime code can be found under ``/hdk/cl/examples/$CL_DIR/software/``


Build
~~~~~

- All CL examples utilize infrastructure found under
  `hdk/common/shell_stable/build
  <https://github.com/aws/aws-fpga/tree/f2/hdk/common/shell_stable/build>`__

- Users can modify the following files to meet their build requirements:

  - `synth_<CL_NAME>.tcl
    <https://github.com/aws/aws-fpga/tree/f2/hdk/cl/examples/CL_TEMPLATE/build/scripts/synth_CL_TEMPLATE.tcl>`__
    - Example's top level script to read design's source code, IPs, and constraint files and run the design synthesis
    - Make sure to add new IP's ``.xci`` files to this script

  - `cl_synth_user.xdc
    <https://github.com/aws/aws-fpga/tree/f2/hdk/cl/examples/CL_TEMPLATE/build/constraints/cl_synth_user.xdc>`__
    - Example's synthesis constraints

  - `cl_timing_user.xdc
    <https://github.com/aws/aws-fpga/tree/f2/hdk/cl/examples/CL_TEMPLATE/build/constraints/cl_timing_user.xdc>`__
    - Example's timing constraints

  - `small_shell_cl_pnr_user.xdc
    <https://github.com/aws/aws-fpga/tree/f2/hdk/cl/examples/CL_TEMPLATE/build/constraints/small_shell_cl_pnr_user.xdc>`__
    - Example's place-and-route constraints specific to the Small Shell

For synthesis settings that are common among all CL examples, refer to:

- `synth_cl_header.tcl <https://github.com/aws/aws-fpga/tree/f2/hdk/common/shell_stable/build/scripts/synth_cl_header.tcl>`__
- `synth_cl_footer.tcl <https://github.com/aws/aws-fpga/tree/f2/hdk/common/shell_stable/build/scripts/synth_cl_footer.tcl>`__


Common Libraries
------------------

The `hdk/common/ <https://github.com/aws/aws-fpga/tree/f2/hdk/common/>`
directory includes the shell artifacts, versions, scripts, constraints and
compile settings required during the AFI generation process. Developers should
not modify or remove any files in this directory unless directed above.

shell_stable/
~~~~~~~~~~~~~

The `shell_stable/
<https://github.com/aws/aws-fpga/tree/f2/hdk/common/shell_stable>`__ directory
contains all the IPs, constraints and scripts for each shell release.

verif/
~~~~~~

The `verif/ <https://github.com/aws/aws-fpga/tree/f2/hdk/common/verif>`__
directory includes the Bus Functional Models (BFMs) used as the external
interfaces to send stimulus to the CL in simulations. Additionally, the common
verification files among all CL examples are located in this directory and
categorized under four subdirectories:

- The `models/
  <https://github.com/aws/aws-fpga/tree/f2/hdk/common/verif/models>`__
  directory includes simple models of the DRAM interface around the FPGA,
  shell, and card. You can also find Xilinx protocol checkers in this directory.

- The `scripts/
  <https://github.com/aws/aws-fpga/tree/f2/hdk/common/verif/scripts>`__
  directory includes scripts needed to generate DDR models and other necessary
  HDK setups.

- The `verif/
  <https://github.com/aws/aws-fpga/tree/f2/hdk/common/verif/include>`__
  directory includes sh_dpi_tasks.vh needed for DPI-C.
  - The ``verif/ip_simulation_libraries`` directory will be created during
  runtime. It includes the simulation libraries and CL IP compilation for all
  supported simulators.

- The `tb/ <https://github.com/aws/aws-fpga/tree/f2/hdk/common/verif/tb>`__
  directory includes the top-level testbench related files common among all CL
  examples.

- The `packages/ <https://github.com/aws/aws-fpga/tree/f2/hdk/common/verif/tb>`__
  directory includes the common functions, types and macros used in simulations.


ip/
~~~

The `ip/ <https://github.com/aws/aws-fpga/tree/f2/hdk/common/ip>`__ directory
includes all CL IPs .

lib/
~~~~

The `lib <https://github.com/aws/aws-fpga/tree/f2/hdk/common/lib>`__ directory
includes all sub-modules instantiated in CL examples.

- aws_clk_gen.sv - Generate clocks and resets to the CL design
- aws_clk_regs.sv - Houses all the Control/Status Regs for AWS_CLK_GEN
  design
- axi_clock_conv.sv - AXI-4 bus clock converter
- axil_to_cfg_cnv.sv - Convert AXIL transaction into a simple CFG bus
- axis_flop_fifo.sv - Flop based FIFO for AXI-Stream protocol
- bram_1w1r.sv - BRAM (1 write/1 read port) RTL model.
- bram_wr2.sv - BRAM (2 read/write ports) RTL model.
- ccf_ctl.v - Clock crossing FIFO control block (pointers, address
  generation, etc...)
- cdc_async_fifo.sv - Async FF-based FIFO for CDC
- cdc_sync.sv - Single- or Multi-bit Synchronizer based on Xilinx XPM
- flop_ccf.sv - Flop based clock crossing FIFO.
- flop_fifo.sv - Flop based FIFO.
- flop_fifo_in.sv - Flop based FIFO, where input is flopped by common
  flops (can be used for input signal registering).
- ft_fifo.v - Flow through FIFO.
- ft_fifo_p.v - Flow through FIFO to be used with pipelined RAM.
- gray.inc - Gray code
- hbm_wrapper.sv - Wrapper for HBM IP
- interfaces.sv - Generic interfaces (AXI-4, AXI-L, etc...)
- lib_pipe.sv - Pipeline block.
- macros.svh - Instantiation macros (AXI-4, AXI-L, etc...)
- mgt_acc_axl.sv - Used by AWS provided sh_ddr.sv
- mgt_gen_axl.sv - Used by AWS provided sh_ddr.sv
- ram_fifo_ft.sv - Ram based FIFO
- rr_arb.sv - Round robin arbiter.
- srl_fifo.sv - Shift register based fifo.
- sync.v - Synchronizer
- xpm_fifo.sv - Synchronous clock FIFO


Next Steps
---------------

- Familiarize the `cl_sde <./cl/examples/cl_sde/README.html>`__ example
- `Run RTL simulations <./docs/RTL_Simulation_Guide_for_HDK_Design_Flow.html>`__
  on the example designs
- Dive deep into the `Shell Interface Specification
  <./docs/AWS_Shell_Interface_Specification.html>`__ and `PCIe Memory Map
  <./docs/AWS_Fpga_Pcie_Memory_Map.html>`__
- Create your own CL designs or port F1 designs over to F2 systems
