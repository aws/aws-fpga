Accelerating your C/C++ application on AWS EC2 F2 (FPGA) Instances with Vitis
=============================================================================

This quick start guide will utilize a simple ``hello_world`` Vitis
example to get you started.

Table of Contents
-----------------

1. `Overview <#overview>`__
2. `Prerequisites <#prerequisites>`__

   1. `AWS Fundamentals <#aws-fundamentals>`__
   2. `Familiarize Yourself With
      Vitis <#familiarize-yourself-with-vitis>`__
   3. `GitHub and Environment
      Setup <#github-and-environment-setup>`__

3. `Hardware Emulation <#hardware-emulation>`__

   1. `Hardware Emulation Setup <#hw-emu-setup>`__
   2. `Hardware Emulation Run <#hw-emu-run>`__
   3. `Emulating the Host Application and Accelerator
      Design <#emulating-the-host-application-and-accelerator-design>`__

4. `Hardware Binary Build <#hardware-binary-build>`__
5. `Results and Artifacts <#results-and-artifacts>`__

   1. `Hardware Emulation
      Artifacts <#hardware-emulation-artifacts>`__
   2. `Hardware Binary Build
      Artifacts <#hardware-binary-build-artifacts>`__

6. `Examining Run Data <#examining-run-and-build-data>`__
7. `Additional Vitis Information <#additional-vitis-information>`__

.. _vitis-overview:

1. Overview
-----------

- Vitis is a complete development environment for applications
  accelerated using AWS EC2 F2 (FPGA) instances
- It leverages the OpenCL heterogeneous computing framework to offload
  compute intensive workloads to F2 instances
- The accelerated application is written in C/C++, OpenCL, and/or
  Verilog/VHDL

.. _vitis-prerequisites:

2. Prerequisites
----------------

.. _aws-fundamentals:

2.1 AWS Fundamentals
~~~~~~~~~~~~~~~~~~~~

AWS Fundamentals are critical to the development workflow on F2 and are `discussed here <../User-Guide-AWS-EC2-FPGA-Development-Kit.html#getting-familiar-with-aws>`__ in more detail.

For information about the development environment and AMI `please reference the User Guide <../User-Guide-AWS-EC2-FPGA-Development-Kit.html#software-defined-development-environment>`__.

.. _familiarize-yourself-with-vitis:

2.2 Familiarize Yourself With Vitis
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

If you are new to using Vitis, it is essential to understand the
following examples before proceeding with your own accelerator design:

- `Vitis HLS (High-Level Synthesis) Introductory
  Examples <https://github.com/Xilinx/Vitis-HLS-Introductory-Examples>`__
- `Vitis Tutorials <https://github.com/Xilinx/Vitis-Tutorials>`__

.. _github-and-environment-setup:

2.3 GitHub and Environment Setup
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

- Clone the GitHub repository and source the ``vitis_setup.sh`` script:

.. code:: bash

   git clone https://github.com/aws/aws-fpga.git
   cd aws-fpga
   source vitis_setup.sh

- Sourcing the `vitis_setup.sh <https://github.com/aws/aws-fpga/tree/f2/vitis_setup.sh>`__ script does the following:

  - Downloads and sets up the correct Vitis platform for the F2 FPGA:

    - AWS EC2 F2 Vitis platform package that enables Vitis kernels to
      run on AWS F2 instances
    - Valid platforms for the current stable shell version

  - Sets up the Vitis example directories
  - Installs the required libraries and package dependencies
  - Runs environment checks to verify supported tool/lib versions
  - Gathers dependencies needed to install the `Xilinx
    Runtime <https://github.com/Xilinx/XRT/tree/master>`__ (XRT) for the given tool version
  - Provides a command to install the XRT, which is necessary to perform builds,
    emulation, and run accelerated applications

If the script has successfully set up all of the tools and the
environment, you will see the following message:

.. code:: bash

   INFO: #-------------------------------------------------------------------------------#
   INFO: How to run hardware emulation an example
   INFO: cd vitis/examples/vitis_examples/hello_world
   INFO: hw_file_check
   INFO: #----------------------------- Emulation ---------------------------------------#
   INFO: make build TARGET=hw_emu PLATFORM=$SHELL_EMU_VERSION
   INFO: #-------------------------------------------------------------------------------#
   INFO: Vitis Setup PASSED.

You will also see this prompt if no XRT install is present on your
system:

.. code:: bash

   INFO: "###########################################################################"
   INFO: "#                       No XRT install detected!                          #"
   INFO: "#     To install the XRT for Vitis runtime support, run 'install_xrt'     #"
   INFO: "###########################################################################"

.. _hardware-emulation:

3. Hardware Emulation
---------------------

The Vitis hardware emulation (HW_EMU) flow enables developers to iterate
on their designs more rapidly than performing a hardware build. It is a
cycle-accurate emulation of your accelerator design. The emulation flow
invokes Vitis' hardware simulator to test both the host application and
accelerator code.

This section will walk you through the emulation process. The goal of
hardware emulation is to verify functional correctness of the logic
generated by the tools and partition the application between the host
CPU and the FPGA. Hardware emulation does not use actual FPGAs and can
be run on any compute instance. Using non-F2 EC2 compute instances
during initial development reduces cost.

.. _hw-emu-setup:

3.1 Hardware Emulation Setup
~~~~~~~~~~~~~~~~~~~~~~~~~~~~

To perform hardware emulation for the ``hello_world`` example, run the
following commands:

.. code:: bash

   cd $AWS_FPGA_REPO_DIR/vitis/examples/vitis_examples/hello_world
   ll

Prior to starting a hardware emulation run, run the ``hw_file_check``
command to insure that all files required for simulation are present. If
all required files are present, you will see
``All required simulation files are present!``.

``NOTE: All paths shown below are identical for customers using Rocky Linux, substituting 'rocky' for 'ubuntu'``

.. code:: bash

   ubuntu@ip-aaa-bb-cc-dd:~/aws-fpga/vitis/examples/vitis_examples/hello_world$ hw_file_check
   INFO: All required simulation files are present!

Otherwise, the missing files' names will be displayed. These files can
always be reobtained from the ``aws-fpga`` repository if they are
deleted or renamed at any point.

.. code:: bash

   ubuntu@ip-aaa-bb-cc-dd:~/aws-fpga/vitis/examples/vitis_examples/hello_world$ hw_file_check
   ERROR: !!! Required file: makefile_us_alveo.mk not found in current example directory !!!

The most critical file in each example directory is the ``Makefile``.
Some examples will have sub-examples, whose ``Makefiles`` are located in
the associated subdirectory.

Note the presence of the ``Makefile`` in this subdirectory. Some
examples will have sub-examples, whose ``Makefiles`` are located in the
associated subdirectory.

.. warning::

   A Makefile is required in order to run hardware emulation for all
   designs/examples

.. _hw-emu-run:

3.2 Hardware Emulation Run
~~~~~~~~~~~~~~~~~~~~~~~~~~

We recommend running hardware emulation in the background to allow
concurrent design iteration and to prevent disruption due to the time
needed for completion. Prefixing commands with ``nohup`` and ending them
with an ``&`` will insure more reliable execution.

Once you've verified that all required files are present in the current
example directory, start the hardware emulation run with the following
command:

.. code:: bash

   nohup make build TARGET=hw_emu PLATFORM=$SHELL_EMU_VERSION &

The same command can be used for all Vitis examples after running
``vitis_setup.sh``.

A successful hardware emulation run will produce log output similar to
the following:

.. code:: bash

   INFO: [v++ 60-1548] Creating build summary session with primary output /home/ubuntu/aws-fpga/vitis/examples/Vitis_Accel_Examples/hello_world/build_dir.hw_emu.xilinx_aws-vu47p-f2_202420_2/vadd.xclbin.package_summary, at Fri Jan 17 16:06:50 2025
   INFO: [v++ 60-1315] Creating rulecheck session with output '/home/ubuntu/aws-fpga/vitis/examples/Vitis_Accel_Examples/hello_world/_x/reports/package/v++_package_vadd_guidance.html', at Fri Jan 17 16:06:50 2025
   INFO: [v++ 60-895]   Target platform: /opt/Xilinx/2025.1/Vitis/platforms/xilinx_aws-vu47p-f2_202420_2.xpfm
   INFO: [v++ 60-1578]   This platform contains Xilinx Shell Archive '/opt/Xilinx/2025.1/Vitis/platforms/hw/hw.xsa'
   INFO: [v++ 74-78] Compiler Version string: 2025.1
   INFO: [v++ 60-2256] Packaging for hardware emulation
   INFO: [v++ 60-2460] Successfully copied a temporary xclbin to the output xclbin: /home/ubuntu/aws-fpga/vitis/examples/Vitis_Accel_Examples/hello_world/./build_dir.hw_emu.xilinx_aws-vu47p-f2_202420_2/vadd.xclbin
   INFO: [v++ 60-2343] Use the Vitis Unified IDE to visualize and navigate the reports. Run the following command.
       vitis -a/ --analyze /home/ubuntu/aws-fpga/vitis/examples/Vitis_Accel_Examples/hello_world/build_dir.hw_emu.xilinx_aws-vu47p-f2_202420_2/vadd.xclbin.package_summary
   INFO: [v++ 60-791] Total elapsed time: 0h 0m 5s
   INFO: [v++ 60-1653] Closing dispatch client

This line is the most significant:

.. code:: bash

   INFO: [v++ 60-2460] Successfully copied a temporary xclbin to the output xclbin: /home/ubuntu/aws-fpga/vitis/examples/Vitis_Accel_Examples/hello_world/./build_dir.hw_emu.xilinx_aws-vu47p-f2_202420_2/vadd.xclbin

The ``.xclbin`` file is what will be used to test your combined
host/accelerator application.

After running hardware emulation, a number of artifacts will be
produced. These artifacts will be discussed in a section below,
alongside those produced by hardware builds.

.. _emulating-the-host-application-and-accelerator-design:

3.3 Emulating the Host Application and Accelerator Design
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Now, let's emulate our design by running
``make run TARGET=hw_emu PLATFORM=$SHELL_EMU_VERSION``

.. code:: bash

   ubuntu@ip-aaa-bb-cc-dd:~/aws-fpga/vitis/examples/vitis_examples/hello_world$ make run TARGET=hw_emu PLATFORM=$SHELL_EMU_VERSION
   emconfigutil --platform xilinx_aws-vu47p-f2_202420_2 --od ./_x.hw_emu.xilinx_aws-vu47p-f2_202420_2
   ****** configutil v2025.1 (64-bit)
     **** SW Build 5074859 on 2024-05-20-23:21:20
     **** Start of session at: Fri Jan 17 16:48:27 2025
       ** Copyright 1986-2022 Xilinx, Inc. All Rights Reserved.
       ** Copyright 2022-2024 Advanced Micro Devices, Inc. All Rights Reserved.
   INFO: [ConfigUtil 60-895]   Target platform: /opt/Xilinx/2025.1/Vitis/platforms/xilinx_aws-vu47p-f2_202420_2.xpfm
   INFO: [ConfigUtil 60-1578]   This platform contains Xilinx Shell Archive '/opt/Xilinx/2025.1/Vitis/platforms/hw/hw.xsa'
   INFO: [ConfigUtil 60-1032] Extracting hardware platform to ./_x.hw_emu.xilinx_aws-vu47p-f2_202420_2
   emulation configuration file `emconfig.json` is created in ./_x.hw_emu.xilinx_aws-vu47p-f2_202420_2 directory
   cp -rf ./_x.hw_emu.xilinx_aws-vu47p-f2_202420_2/emconfig.json .
   XCL_EMULATION_MODE=hw_emu ./hello_world_xrt -x ./build_dir.hw_emu.xilinx_aws-vu47p-f2_202420_2/vadd.xclbin

   Open the device0
   Load the xclbin ./build_dir.hw_emu.xilinx_aws-vu47p-f2_202420_2/vadd.xclbin
   INFO: [HW-EMU 05] Path of the simulation directory : /home/ubuntu/aws-fpga/vitis/examples/Vitis_Accel_Examples/hello_world/.run/1469002/hw_emu/device0/binary_0/behav_waveform/xsim
    server socket name is   /tmp/ubuntu/device0_0_1469002
   INFO: [HW-EMU 01] Hardware emulation runs simulation underneath. Using a large data set will result in long simulation times. It is recommended that a small dataset is used for faster execution. The flow uses approximate models for Global memories and interconnect and hence the performance data generated is approximate.
   configuring dataflow mode with ert polling
   scheduler config ert(1), dataflow(1), slots(16), cudma(0), cuisr(0), cdma(0), cus(1)
   Allocate Buffer in Global Memory
   synchronize input buffer data to device global memory
   Execution of the kernel
   Get the output data from the device
   TEST PASSED

   INFO: [HW-EMU 06-0] Waiting for the simulator process to exit
   INFO: [HW-EMU 06-1] All the simulator processes exited successfully
   INFO: [HW-EMU 07-0] Please refer the path "/home/ubuntu/aws-fpga/vitis/examples/Vitis_Accel_Examples/hello_world/.run/1469002/hw_emu/device0/binary_0/behav_waveform/xsim/simulate.log" for more detailed simulation infos, errors and warnings.

At this point, we can see that our example has passed and is functional
as written. It is important to note that although the emulation output
states things like ``Open the device``, it is not interacting with an
actual FPGA, but is being simulated.

Once you have iterated on your design using hardware emulation,
performing a hardware build is the next step.

.. _hardware-binary-build:

4. Hardware Binary Build
------------------------

With the functional correctness of your design verified, it's time to
build the accelerator design into a binary that can be loaded onto an
FPGA.

The process is nearly identical to that of HW_EMU and is run with the
following command:

.. code:: bash

   nohup make build TARGET=hw PLATFORM=$SHELL_EMU_VERSION &

Again, we recommend running this build in the background to insure it's
completion without interruption.

A successful hardware (HW) build will produce output similar to the
following:

.. code:: bash

   INFO: [v++ 60-1548] Creating build summary session with primary output /home/ubuntu/aws-fpga/vitis/examples/Vitis_Accel_Examples/hello_world/build_dir.hw.xilinx_aws-vu47p-f2_202420_2/vadd.xclbin.package_summary, at Fri Jan 17 17:39:31 2025
   INFO: [v++ 60-1315] Creating rulecheck session with output '/home/ubuntu/aws-fpga/vitis/examples/Vitis_Accel_Examples/hello_world/_x/reports/package/v++_package_vadd_guidance.html', at Fri Jan 17 17:39:31 2025
   INFO: [v++ 60-895]   Target platform: /opt/Xilinx/2025.1/Vitis/platforms/xilinx_aws-vu47p-f2_202420_2.xpfm
   INFO: [v++ 60-1578]   This platform contains Xilinx Shell Archive '/opt/Xilinx/2025.1/Vitis/platforms/hw/hw.xsa'
   INFO: [v++ 74-78] Compiler Version string: 2025.1
   INFO: [v++ 60-2256] Packaging for hardware
   INFO: [v++ 60-2460] Successfully copied a temporary xclbin to the output xclbin: /home/ubuntu/aws-fpga/vitis/examples/Vitis_Accel_Examples/hello_world/./build_dir.hw.xilinx_aws-vu47p-f2_202420_2/vadd.xclbin
   INFO: [v++ 60-2343] Use the Vitis Unified IDE to visualize and navigate the reports. Run the following command.

Once again, the message stating that a ``.xclbin`` file has been
successfully copied is our assurance that the build was successful.

When a build completes, it produces several artifacts that contain
information about our design. Let's now see where we can find these
artifacts and examine them.

.. _results-and-artifacts:

5. Results and Artifacts
------------------------

Once the HW_EMU or HW run/build has completed, you will see a build
directory with the pertinent name.

.. code:: bash

   aws-fpga/vitis/examples/vitis_examples/
           hello_world/
                   build_dir.hw_emu.xilinx_aws-vu47p-f2_202420_2/
                                   or
                   build_dir.hw.xilinx_aws-vu47p-f2_202420_2/

**These directories will contain the .xclbin file, as well as other
artifacts, depending on the example run:**

.. _hardware-emulation-artifacts:

5.1 Hardware Emulation Artifacts
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

.. code:: bash

   drwxrwxr-x  2 ubuntu ubuntu     4096 Jan 17 16:06 ./
   drwxrwxr-x 12 ubuntu ubuntu     4096 Jan 17 16:06 ../
   -rw-rw-r--  1 ubuntu ubuntu 46021316 Jan 17 16:06 vadd.link.xclbin
   -rw-rw-r--  1 ubuntu ubuntu    10491 Jan 17 16:06 vadd.link.xclbin.info
   -rw-rw-r--  1 ubuntu ubuntu    33602 Jan 17 16:06 vadd.link.xclbin.link_summary
   -rw-rw-r--  1 ubuntu ubuntu 46021348 Jan 17 16:06 vadd.xclbin
   -rw-rw-r--  1 ubuntu ubuntu     4171 Jan 17 16:06 vadd.xclbin.package_summary

.. _hardware-binary-build-artifacts:

5.2 Hardware Binary Build Artifacts
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

.. code:: bash

   drwxrwxr-x  2 ubuntu ubuntu     4096 Jan 16 19:30 ./
   drwxrwxr-x 12 ubuntu ubuntu     4096 Jan 17 16:26 ../
   -rw-rw-r--  1 ubuntu ubuntu      579 Jan 16 19:30 vadd.link.ltx
   -rw-rw-r--  1 ubuntu ubuntu 47823796 Jan 16 19:30 vadd.link.xclbin
   -rw-rw-r--  1 ubuntu ubuntu    10683 Jan 16 19:30 vadd.link.xclbin.info
   -rw-rw-r--  1 ubuntu ubuntu    45974 Jan 16 19:30 vadd.link.xclbin.link_summary
   -rw-rw-r--  1 ubuntu ubuntu 47823836 Jan 16 19:30 vadd.xclbin
   -rw-rw-r--  1 ubuntu ubuntu     4111 Jan 16 19:30 vadd.xclbin.package_summary

With our ``.xclbin`` file in hand from our hardware build, it's time to
create an Amazon FPGA Image (AFI)

⚠️ **Vitis AFI generation is not currently supported on F2 instances**

.. _afi-creation:

6. Examining Run and Build Data
-------------------------------

After a HW_EMU or HW run/build, there are four files that contain very
important information:

- ``vadd.xclbin.info``

  - A text report of the generated device binary

- ``vadd.xclbin.link_summary``

  - A summary report of the linking process which generated the device
    binary

- ``vadd.link.xclbin.link_summary``

  - Contains an estimate of system performance

- ``xrt.run_summary``

  - A summarized report of events captured during application runtime

The first three of these files can be found in the newly-generated
directory prefixed with ``build_dir.<hw/hw_emu>.``. The
``xrt.run_summary`` file can be found in the example directory itself.

.. _additional-vitis-information:

7. Additional Vitis Information
-------------------------------

.. toctree::
  :maxdepth: 1

  ERRATA

`Vitis Documentation Hub <https://docs.amd.com/r/en-US/Vitis-Tutorials-Getting-Started>`__

`Back to Home <../index.html>`__
