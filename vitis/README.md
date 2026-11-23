# Quick Start Guide to Accelerating a C/C++ application on AWS EC2 F2 (FPGA) Instances with Vitis

This quick start guide introduces the Vitis development workflow using a simple `hello_world` example.

## Table of Contents

- [Overview](#overview)
- [Prerequisites](#prerequisites)
  - [AWS Fundamentals](#aws-fundamentals)
  - [Vitis Introductory Examples](#vitis-introductory-examples)
  - [GitHub and Environment Setup](#github-and-environment-setup)
- [Hardware Emulation](#hardware-emulation)
  - [Hardware Emulation Setup](#hardware-emulation-setup)
  - [Hardware Emulation Run](#hardware-emulation-run)
  - [Emulating the host Application and Accelerator Design](#emulating-the-host-application-and-accelerator-design)
- [Hardware Binary Build](#hardware-binary-build)
- [Results and Artifacts](#results-and-artifacts)
  - [Hardware Emulation Artifacts](#hardware-emulation-artifacts)
  - [Hardware Binary Build Artifacts](#hardware-binary-build-artifacts)
- [AFI Creation](#afi-creation)
  - [Examining Build Data](#examining-build-data)
- [Running the Example AFIs](#running-the-example-afis)
  - [Running the Host Application Binary With an AFI](#running-the-host-application-binary-with-an-afi)
  - [Examining Run Results](#examining-run-results)
- [Additional Vitis Information](#additional-vitis-information)

## Overview

* Vitis is a complete development environment for applications accelerated using AWS EC2 F2 (FPGA) instances
* It leverages the OpenCL heterogeneous computing framework to offload compute intensive workloads to F2 instances
* The accelerated application is written in C/C++, OpenCL, and/or Verilog/VHDL

## Prerequisites

### AWS Fundamentals

AWS Fundamentals are critical to the development workflow on F2 and are [discussed here](../User_Guide_AWS_EC2_FPGA_Development_Kit.md#getting-familiar-with-aws) in more detail.

Information about the development environment and AMI is available in [the User Guide](../User_Guide_AWS_EC2_FPGA_Development_Kit.md#software-defined-development-environment).

### Vitis Introductory Examples

The following examples provide essential background for developing an accelerator design with Vitis:

* [Vitis HLS (High-Level Synthesis) Introductory Examples](https://github.com/Xilinx/Vitis-HLS-Introductory-Examples)
* [Vitis Tutorials](https://github.com/Xilinx/Vitis-Tutorials)

### GitHub and Environment Setup

Vitis 2024.1 is not supported by the AWS F2 Developer Kit. Vivado 2024.1 remains supported for the HDK flow; see [supported_vivado_versions.txt](../supported_vivado_versions.txt).

Platform `202420_3` with XDMA shell `0x10052623` is the only supported pairing. `vitis_setup.sh` downloads this platform for the Vitis versions below:

| Vitis version | Platform version | XDMA shell | Workflow and validation |
|---|---|---|---|
| 2024.2, 2025.1, 2025.2 | `202420_3` | `0x10052623` | Hardware Emulation and AFI creation |



#### Cloning the Developer Kit and Sourcing the Setup Script

Run these commands in a Bash shell on an FPGA Developer AMI with a supported Vitis version.

``` bash
git clone https://github.com/aws/aws-fpga.git
cd aws-fpga
source vitis_setup.sh
```

* Sourcing the [vitis_setup.sh](../vitis_setup.sh) script does the following:
  * Downloads and sets up the correct Vitis platform for the F2 FPGA:
    * AWS EC2 F2 Vitis platform package that enables Vitis kernels to run on AWS F2 instances
    * A platform matching the installed Vitis version
  * Sets up the Vitis example directories
  * Installs the required libraries and package dependencies
  * Runs environment checks to verify supported tool/lib versions
  * Gathers dependencies needed to install the [Xilinx Runtime](https://github.com/Xilinx/XRT/tree/master) (XRT) for the given tool version
  * Provides a command to install the XRT, which is necessary to perform builds, emulation, and run accelerated applications

The script displays the following message after successfully setting up all of the tools and the environment:

``` bash
INFO: #-------------------------------------------------------------------------------#
INFO: How to run Hardware Emulation or a Hardware Build for an example
INFO: cd vitis/examples/vitis_examples/hello_world
INFO: hw_file_check
INFO: #---------------------------- Emulation ----------------------------------------#
INFO: make run TARGET=hw_emu PLATFORM=$SHELL_EMU_VERSION
INFO: #---------------------------- Hardware -----------------------------------------#
INFO: make build TARGET=hw PLATFORM=$SHELL_EMU_VERSION
INFO: #-------------------------------------------------------------------------------#
INFO: Vitis Setup PASSED.
```

The script also displays this prompt if no XRT install is present on the system:

``` bash
INFO: "###########################################################################"
INFO: "#                       No XRT install detected!                          #"
INFO: "#     To install the XRT for Vitis runtime support, run 'install_xrt'     #"
INFO: "###########################################################################"

```

If the "No XRT install detected!" prompt appears, run `install_xrt`. XRT conflicts with the standalone XDMA driver. If `lsmod | grep '^xdma '` shows that driver is loaded, stop applications using it and run `sudo modprobe -r xdma` before installing XRT.

## Hardware Emulation

The Vitis hardware emulation (HW_EMU) flow enables developers to iterate on their designs more rapidly than performing a hardware build. It is a cycle-accurate emulation of the accelerator design. The emulation flow invokes Vitis' hardware simulator to test both the host application and accelerator code.

This section describes the emulation process. The goal of hardware emulation is to verify functional correctness of the logic generated by the tools and partition the application between the host CPU and the FPGA. Hardware emulation does not use actual FPGAs and can be run on any compute instance. Using non-F2 EC2 compute instances during initial development reduces cost.

### Hardware Emulation Setup

Hardware emulation setup for the `hello_world` example uses the following commands:

`NOTE: All paths shown below are identical for customers using Rocky Linux, substituting 'rocky' for 'ubuntu'`

``` bash
cd $AWS_FPGA_REPO_DIR/vitis/examples/vitis_examples/hello_world
ll
```

Before a hardware emulation run, the `hw_file_check` command verifies that all files required for simulation are present. If all required files are present, the command displays `All required simulation files are present!`.

``` bash
ubuntu@ip-aaa-bb-cc-dd:~/aws-fpga/vitis/examples/vitis_examples/hello_world$ hw_file_check
INFO: All required simulation files are present!
```

Otherwise, the missing files' names will be displayed. The example directory is part of the `Vitis_Accel_Examples` clone under `$AWS_FPGA_REPO_DIR/vitis/examples/`, so restore a deleted file with `git checkout -- <file>` from the example directory.

``` bash
ubuntu@ip-aaa-bb-cc-dd:~/aws-fpga/vitis/examples/vitis_examples/hello_world$ hw_file_check
ERROR: !!! Required file: makefile_us_alveo.mk not found in current example directory !!!
```

Run `make` from the directory containing the example's `Makefile`. For an example with sub-examples, use the sub-example directory.

### Hardware Emulation Run

To build the accelerator for hardware emulation in the background, run:

``` bash
nohup make build TARGET=hw_emu PLATFORM=$SHELL_EMU_VERSION &
```

Use this command for examples that support hardware emulation after sourcing `vitis_setup.sh`. See [Vitis ERRATA](./ERRATA.md) for example and tool-version restrictions.

A successful hardware emulation build produces output similar to the following:

``` bash
INFO: [v++ 60-1548] Creating build summary session with primary output /home/ubuntu/aws-fpga/vitis/examples/Vitis_Accel_Examples/hello_world/build_dir.hw_emu.xilinx_aws-vu47p-f2_202420_3/vadd.xclbin.package_summary, at Fri Jan 17 16:06:50 2025
INFO: [v++ 60-1315] Creating rulecheck session with output '/home/ubuntu/aws-fpga/vitis/examples/Vitis_Accel_Examples/hello_world/_x/reports/package/v++_package_vadd_guidance.html', at Fri Jan 17 16:06:50 2025
INFO: [v++ 60-895]   Target platform: /opt/Xilinx/2025.2/Vitis/platforms/xilinx_aws-vu47p-f2_202420_3.xpfm
INFO: [v++ 60-1578]   This platform contains Xilinx Shell Archive '/opt/Xilinx/2025.2/Vitis/platforms/hw/hw.xsa'
INFO: [v++ 74-78] Compiler Version string: 2025.2
INFO: [v++ 60-2256] Packaging for hardware emulation
INFO: [v++ 60-2460] Successfully copied a temporary xclbin to the output xclbin: /home/ubuntu/aws-fpga/vitis/examples/Vitis_Accel_Examples/hello_world/./build_dir.hw_emu.xilinx_aws-vu47p-f2_202420_3/vadd.xclbin
INFO: [v++ 60-2343] Use the Vitis Unified IDE to visualize and navigate the reports. Run the following command.
    vitis -a/ --analyze /home/ubuntu/aws-fpga/vitis/examples/Vitis_Accel_Examples/hello_world/build_dir.hw_emu.xilinx_aws-vu47p-f2_202420_3/vadd.xclbin.package_summary
INFO: [v++ 60-791] Total elapsed time: 0h 0m 5s
INFO: [v++ 60-1653] Closing dispatch client
```

This line is the most significant:

``` bash
INFO: [v++ 60-2460] Successfully copied a temporary xclbin to the output xclbin: /home/ubuntu/aws-fpga/vitis/examples/Vitis_Accel_Examples/hello_world/./build_dir.hw_emu.xilinx_aws-vu47p-f2_202420_3/vadd.xclbin
```

The `.xclbin` file is used to test the combined host/accelerator application.

### Emulating the Host Application and Accelerator Design

The command `make run TARGET=hw_emu PLATFORM=$SHELL_EMU_VERSION` builds the host application and accelerator design, then runs hardware emulation in a single invocation. The separate `make build` step above is optional; it allows the long build to run in the background before starting emulation.

``` bash
ubuntu@ip-aaa-bb-cc-dd:~/aws-fpga/vitis/examples/vitis_examples/hello_world$ make run TARGET=hw_emu PLATFORM=$SHELL_EMU_VERSION
emconfigutil --platform xilinx_aws-vu47p-f2_202420_3 --od ./_x.hw_emu.xilinx_aws-vu47p-f2_202420_3
****** configutil v2025.2 (64-bit)
  **** SW Build 5074859 on 2024-05-20-23:21:20
  **** Start of session at: Fri Jan 17 16:48:27 2025
    ** Copyright 1986-2022 Xilinx, Inc. All Rights Reserved.
    ** Copyright 2022-2024 Advanced Micro Devices, Inc. All Rights Reserved.
INFO: [ConfigUtil 60-895]   Target platform: /opt/Xilinx/2025.2/Vitis/platforms/xilinx_aws-vu47p-f2_202420_3.xpfm
INFO: [ConfigUtil 60-1578]   This platform contains Xilinx Shell Archive '/opt/Xilinx/2025.2/Vitis/platforms/hw/hw.xsa'
INFO: [ConfigUtil 60-1032] Extracting hardware platform to ./_x.hw_emu.xilinx_aws-vu47p-f2_202420_3
emulation configuration file `emconfig.json` is created in ./_x.hw_emu.xilinx_aws-vu47p-f2_202420_3 directory
cp -rf ./_x.hw_emu.xilinx_aws-vu47p-f2_202420_3/emconfig.json .
XCL_EMULATION_MODE=hw_emu ./hello_world_xrt -x ./build_dir.hw_emu.xilinx_aws-vu47p-f2_202420_3/vadd.xclbin

Open the device0
Load the xclbin ./build_dir.hw_emu.xilinx_aws-vu47p-f2_202420_3/vadd.xclbin
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
```

At this point, we can see that our example has passed and is functional as written. It is important to note that although the emulation output states things like `Open the device`, it is not interacting with an actual FPGA, but is being simulated.

After design iteration using hardware emulation, the next step is a hardware build.

## Hardware Binary Build

After verification of functional correctness, the accelerator design can be built into a binary that can be loaded onto an FPGA.

> [!WARNING]
> Only hardware builds made with Vitis 2024.2 or later can be turned into an AFI. Details are provided in [AFI Creation](#afi-creation).

The process is nearly identical to that of HW_EMU and is run with the following command:

``` bash
nohup make build TARGET=hw PLATFORM=$SHELL_EMU_VERSION &
```

Again, we recommend running this build in the background to insure it's completion without interruption.

A successful hardware (HW) build will produce output similar to the following:

``` bash
INFO: [v++ 60-1548] Creating build summary session with primary output /home/ubuntu/aws-fpga/vitis/examples/Vitis_Accel_Examples/hello_world/build_dir.hw.xilinx_aws-vu47p-f2_202420_3/vadd.xclbin.package_summary, at Fri Jan 17 17:39:31 2025
INFO: [v++ 60-1315] Creating rulecheck session with output '/home/ubuntu/aws-fpga/vitis/examples/Vitis_Accel_Examples/hello_world/_x/reports/package/v++_package_vadd_guidance.html', at Fri Jan 17 17:39:31 2025
INFO: [v++ 60-895]   Target platform: /opt/Xilinx/2025.2/Vitis/platforms/xilinx_aws-vu47p-f2_202420_3.xpfm
INFO: [v++ 60-1578]   This platform contains Xilinx Shell Archive '/opt/Xilinx/2025.2/Vitis/platforms/hw/hw.xsa'
INFO: [v++ 74-78] Compiler Version string: 2025.2
INFO: [v++ 60-2256] Packaging for hardware
INFO: [v++ 60-2460] Successfully copied a temporary xclbin to the output xclbin: /home/ubuntu/aws-fpga/vitis/examples/Vitis_Accel_Examples/hello_world/./build_dir.hw.xilinx_aws-vu47p-f2_202420_3/vadd.xclbin
INFO: [v++ 60-2343] Use the Vitis Unified IDE to visualize and navigate the reports. Run the following command.

```

Once again, the message stating that a `.xclbin` file has been successfully copied is our assurance that the build was successful.

When a build completes, it produces several artifacts that contain information about the design. The following section describes their locations and contents.

## Results and Artifacts

Once the HW_EMU or HW run/build has completed, the artifacts are available in a build directory with the pertinent name.

``` bash
aws-fpga/vitis/examples/vitis_examples/
        hello_world/
                build_dir.hw_emu.xilinx_aws-vu47p-f2_202420_3/
                                or
                build_dir.hw.xilinx_aws-vu47p-f2_202420_3/
```

**These directories will contain the .xclbin file, as well as other artifacts, depending on the example run:**

### Hardware Emulation Artifacts

``` bash
drwxrwxr-x  2 ubuntu ubuntu     4096 Jan 17 16:06 ./
drwxrwxr-x 12 ubuntu ubuntu     4096 Jan 17 16:06 ../
-rw-rw-r--  1 ubuntu ubuntu 46021316 Jan 17 16:06 vadd.link.xclbin
-rw-rw-r--  1 ubuntu ubuntu    10491 Jan 17 16:06 vadd.link.xclbin.info
-rw-rw-r--  1 ubuntu ubuntu    33602 Jan 17 16:06 vadd.link.xclbin.link_summary
-rw-rw-r--  1 ubuntu ubuntu 46021348 Jan 17 16:06 vadd.xclbin
-rw-rw-r--  1 ubuntu ubuntu     4171 Jan 17 16:06 vadd.xclbin.package_summary
```

### Hardware Binary Build Artifacts

``` bash
drwxrwxr-x  2 ubuntu ubuntu     4096 Jan 16 19:30 ./
drwxrwxr-x 12 ubuntu ubuntu     4096 Jan 17 16:26 ../
-rw-rw-r--  1 ubuntu ubuntu      579 Jan 16 19:30 vadd.link.ltx
-rw-rw-r--  1 ubuntu ubuntu 47823796 Jan 16 19:30 vadd.link.xclbin
-rw-rw-r--  1 ubuntu ubuntu    10683 Jan 16 19:30 vadd.link.xclbin.info
-rw-rw-r--  1 ubuntu ubuntu    45974 Jan 16 19:30 vadd.link.xclbin.link_summary
-rw-rw-r--  1 ubuntu ubuntu 47823836 Jan 16 19:30 vadd.xclbin
-rw-rw-r--  1 ubuntu ubuntu     4111 Jan 16 19:30 vadd.xclbin.package_summary
```

The `.xclbin` file from the hardware build is used to create an Amazon FPGA Image (AFI).

## AFI Creation

Deployment of an accelerator design on an FPGA connected to an F2 instance requires creation of an AFI.

An AFI combines the accelerator design, referred to as Custom Logic (CL), with the FPGA's shell, which forms the interface between the host system and the design.

AFI creation requires an IAM role with the appropriate permissions attached to the EC2 instance. The [IAM role setup guide](../developer_resources/Setting_up_IAM_roles_for_devkit_use.md) covers the required permissions and [attaching the role to an instance](../developer_resources/Setting_up_IAM_roles_for_devkit_use.md#attaching-an-iam-role-to-an-ec2-instance).

The `$AWS_FPGA_REPO_DIR/vitis/tools/create_vitis_afi.sh` command builds the AFI from within a build directory, as shown in [Results and Artifacts](#results-and-artifacts).

``` bash
cd "$AWS_FPGA_REPO_DIR/vitis/examples/vitis_examples/hello_world/build_dir.hw.$SHELL_EMU_VERSION"

S3_BUCKET="my-fpga-bucket"
S3_DCP_KEY="vitis/dcp"
S3_LOGS_KEY="vitis/logs"
XCLBIN="vadd.xclbin"
AWSXCLBIN="vadd"
AWS_REGION="us-east-1"

bash $AWS_FPGA_REPO_DIR/vitis/tools/create_vitis_afi.sh \
    -s3_bucket="$S3_BUCKET" \
    -s3_dcp_key="$S3_DCP_KEY" \
    -s3_logs_key="$S3_LOGS_KEY" \
    -xclbin="$XCLBIN" \
    -o="$AWSXCLBIN" \
    -region="$AWS_REGION"
```

All options are required except `-aws_profile_name`.

* `-s3_bucket` - the S3 bucket that receives the AFI creation files
* `-s3_dcp_key` - the key prefix in that bucket for the AFI creation archive
* `-s3_logs_key` - the key prefix in that bucket for AFI creation logs
* `-xclbin` - the input `.xclbin` file, for example `vadd.xclbin`
* `-o` - the output `.awsxclbin` basename, for example `vadd`
* `-region` - the AWS Region in which to create the AFI
* `-aws_profile_name` - optional named AWS profile; specified by setting `AWS_PROFILE_NAME` and appending `-aws_profile_name="$AWS_PROFILE_NAME"` to the command

Command help is available with `bash $AWS_FPGA_REPO_DIR/vitis/tools/create_vitis_afi.sh -h` or `bash $AWS_FPGA_REPO_DIR/vitis/tools/create_vitis_afi.sh --help`.

The results will look similar to below:

``` text
drwxrwxr-x 3 ubuntu ubuntu     4096 Jan 16 17:17 ./
drwxrwxr-x 9 ubuntu ubuntu     4096 Jan 16 17:48 ../
-rw-rw-r-- 1 ubuntu ubuntu 47708160 Jan 16 17:17 2025_01_16-171710_Developer_Vitis_Kernel.tar
-rw-rw-r-- 1 ubuntu ubuntu 47698217 Jan 16 17:17 2025_01_16-171710_SH_CL_routed.dcp
-rw-rw-r-- 1 ubuntu ubuntu       98 Jan 16 17:17 2025_01_16-171710_afi_id.txt
-rw-rw-r-- 1 ubuntu ubuntu       22 Jan 16 17:17 2025_01_16-171710_agfi_id.txt
-rw-rw-r-- 1 ubuntu ubuntu     5838 Jan 16 17:17 2025_01_16-171710_build.json
-rw-rw-r-- 1 ubuntu ubuntu      670 Jan 16 17:17 2025_01_16-171710_clocks.json
-rw-rw-r-- 1 ubuntu ubuntu      389 Jan 16 17:17 2025_01_16-171710_manifest.txt
-rw-rw-r-- 1 ubuntu ubuntu    51964 Jan 16 17:17 vadd.awsxclbin
drwxrwxr-x 2 ubuntu ubuntu     4096 Jan 16 17:17 to_aws/
-rw-rw-r-- 1 ubuntu ubuntu      579 Jan 16 03:23 vadd.link.ltx
-rw-rw-r-- 1 ubuntu ubuntu 47751100 Jan 16 03:23 vadd.link.xclbin
-rw-rw-r-- 1 ubuntu ubuntu    10683 Jan 16 03:23 vadd.link.xclbin.info
-rw-rw-r-- 1 ubuntu ubuntu    45974 Jan 16 03:23 vadd.link.xclbin.link_summary
-rw-rw-r-- 1 ubuntu ubuntu 47751140 Jan 16 03:23 vadd.xclbin
-rw-rw-r-- 1 ubuntu ubuntu     4111 Jan 16 03:23 vadd.xclbin.package_summary
```

The AFI creation status can be checked using the AFI ID from the generated `*_afi_id.txt` file, such as `2025_01_16-171710_afi_id.txt`.

``` text
{
    "FpgaImageId": "afi-abcdef0123456789a",
    "FpgaImageGlobalId": "agfi-abcdef0123456789a"
}
```

The following command checks the status using the `afi` string:

`aws ec2 describe-fpga-images --fpga-image-ids afi-abcdef0123456789a --region <aws-region>`

Which will yield the output below once successfully processed and available:

``` text
{
    "FpgaImages": [
        {
            "FpgaImageId": "afi-abcdef0123456789a",
            "FpgaImageGlobalId": "agfi-abcdef0123456789a",
            "Name": "vadd",
            "Description": "vadd_Vitis",
            "ShellVersion": "0x10052623",
            "PciId": {
                "DeviceId": "0xf010",
                "VendorId": "0x1d0f",
                "SubsystemId": "0x1d51",
                "SubsystemVendorId": "0xfedd"
            },
            "State": {
                "Code": "available"
            },
            "CreateTime": "2025-01-16T17:17:14.000Z",
            "UpdateTime": "2025-01-16T17:33:54.000Z",
            "OwnerId": "012345678901",
            "Tags": [],
            "Public": false,
            "DataRetentionSupport": false
        }
    ]
}
```

While the AFI is being processed, the `"State"` field reports `"pending"`. Periodic status checks indicate when processing has finished.

If AFI processing fails, the provided error message identifies the error that requires correction.

Once the state is `"available"`, the AFI is ready to use.

### Examining Build Data

The `hello_world` HW_EMU or HW build produces the following reports. XRT can also produce a runtime report when profiling or tracing is enabled in `xrt.ini`:

* `vadd.link.xclbin.info`
  * A text report of the generated device binary

* `vadd.link.xclbin.link_summary`
  * A summary report of the linking process, including an estimate of system performance

* `vadd.xclbin.package_summary`
  * A summary report of the packaging process

* `xrt.run_summary`
  * A summarized report of events captured during application runtime

The first three files are in the `build_dir.hw.<platform>` or `build_dir.hw_emu.<platform>` directory. When generated, `xrt.run_summary` is in the example directory itself.

Running Vitis AFIs is discussed in the next section.

## Running the Example AFIs

### Running the Host Application Binary With an AFI

Once the AFI is available, the accelerated application can run on an F2 instance.
The runtime instance needs XRT and its AWS extension for the Vitis version used to build the example. On an FPGA Developer AMI, source `vitis_setup.sh` and run `install_xrt` if XRT is missing, as described above. The standalone XDMA driver must be unloaded before installing XRT.

Source the XRT environment on the runtime instance and clear any emulation setting before running on hardware:

``` bash
source /opt/xilinx/xrt/setup.sh
unset XCL_EMULATION_MODE
```

If you built the example on a different instance, copy both artifacts to the runtime instance:

* The host application executable, built with `make host`
* The `.awsxclbin` file produced by `create_vitis_afi.sh`

If you built `hello_world` on this F2 instance, build and run the host application from the example directory:

``` bash
cd "$AWS_FPGA_REPO_DIR/vitis/examples/vitis_examples/hello_world"
make host
./hello_world_xrt -x "build_dir.hw.$SHELL_EMU_VERSION/vadd.awsxclbin"
```

On a separate F2 runtime instance, run `./hello_world_xrt -x vadd.awsxclbin` from the directory containing the two copied files.

Examples that use two `.awsxclbin` files, such as `kernel_swap`, are called with two flags:

``` bash
./<host_executable> -x1 <first.awsxclbin> -x2 <second.awsxclbin>
```

The Python-based example `hello_world_py` is currently under development; see [Vitis ERRATA](./ERRATA.md#examples). Its host argument syntax uses `-k` in place of `-x`:

``` bash
python3 host.py -k vadd.awsxclbin
```

Some examples take the `.awsxclbin` as a positional argument with no flag:

``` bash
./<host_executable> vadd.awsxclbin
```

Each example's `README` provides specific instructions.


### Examining Run Results

When working with the Vitis examples, some emit a passing message and others don't.
Example output from the `hello_world` example is shown below:

``` bash
Open the device0
Load the xclbin build_dir.hw.xilinx_aws-vu47p-f2_202420_3/vadd.awsxclbin
Allocate Buffer in Global Memory
synchronize input buffer data to device global memory
Execution of the kernel
Get the output data from the device
TEST PASSED
```

Some examples emit performance figures, while others don't:

```bash
Found Platform
Platform Name: Xilinx
INFO: Reading krnl_vaddmul.awsxclbin
Loading: 'krnl_vaddmul.awsxclbin'
Trying to program device[0]: xilinx_aws-vu47p-f2_xdma-shell-v10052623_202420_3
Device[0]: program successful!
Creating a kernel [krnl_vaddmul:{krnl_vaddmul_1}] for CU(1)
Creating a kernel [krnl_vaddmul:{krnl_vaddmul_2}] for CU(2)
Creating a kernel [krnl_vaddmul:{krnl_vaddmul_3}] for CU(3)
THROUGHPUT = 154.183 GB/s
TEST PASSED
```

## Additional Vitis Information

* [Vitis Documentation Hub](https://docs.amd.com/r/en-US/Vitis-Tutorials-Getting-Started)
* [Vitis ERRATA](./ERRATA.md)
