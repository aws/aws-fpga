# AWS EC2 FPGA Software Development Kit

This directory includes the drivers and runtime environment required by any EC2 FPGA Instance.

The [SDK userspace directory](./userspace) contains the [Amazon FPGA Image (AFI) Management Tools](./userspace/fpga_mgmt_tools/README.md), which includes both the source code to the AFI Management Tools as well as detailed descriptions of the commands to use on an FPGA instance.

The SDK is **NOT** used to build or register AFI, rather it is only used for managing and deploying pre-built AFIs. For building and registering AFIs, please refer to the [HDK](../hdk/README.md).

**NOTE:** This SDK is designed and tested for Linux environments only.

# Quick Start

## Using an AFI on an EC2 FPGA Instance

You can setup and install the SDK with the following few steps.  Note that the first two steps may be skipped if you have already ran them in the above HDK setup.

```bash
    # Fetch the HDK and SDK code
    git clone https://github.com/aws/aws-fpga.git
    # Move to the root directory of the repository before running the next script
    cd aws-fpga
    # Set up the envronment variables, build and install the SDK
    source sdk_setup.sh
```

**NOTE:** The `sdk_setup.sh` would install the [FPGA management tools](./userspace/fpga_mgmt_tools/README.md) if they are not already available in `/usr/bin`. The `sdk_setup.sh` requires having `gcc` installed.  if it is not installed, try running the next command to install it on Amazon Linux, Centos or Redhat distributions:

## Notes on using AFI Management Tools

Early release of the AFI management tools may return uninformative errors or unexpected responses. We recommend running commands a second time after waiting 15-30 seconds if an unexpected response is received. For example, if a loaded image does not show up when using the `fpga-describe-local-image` API, attempt rerunning the command prior to calling `fpga-load-local-image` again.

The `fpga-describe-local-image` API is currently asynchronous which will require polling with `fpga-describe-local-image` until the expected image appears. If the describe call does not provide the expected response, attempt the `fpga-load-local-image` one more time. Attempting to load images that are not compatible with the currently loaded shell will fail and may not return an informative error message. Please verify the design was built with the shell that is loaded on the instance.

Please reach out to the AWS FPGA team with any instability issues so we can help as soon as possible.
