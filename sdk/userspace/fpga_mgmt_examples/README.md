# FPGA Management C API Examples

## Overview
This directory contains example code demonstrating how to use the AWS FPGA Management C API for clearing and loading FPGA images.

## Prerequisites
- AWS F2 Instance
- AWS FPGA SDK
- GCC Compiler

## Setup
1. Clone the repository
2. Source the SDK:

`source ./sdk_setup.sh`


## Examples
The repository includes the following examples:

### FPGA Clearing
1. `clear_single_fpga.c`: Demonstrates clearing an image from a single FPGA slot
2. `clear_multiple_fpga.c`: Demonstrates clearing images from 8 FPGA slots

### FPGA Loading
1. `load_single_fpga.c`: Demonstrates loading an AFI to a single FPGA slot
2. `load_multiple_fpga.c`: Demonstrates loading an AFI to 8 FPGA slots
3. `prefetch_multiple_afi.c`: Demonstrates loading multiple AFIs to a single FPGA slot

## Building the Examples
The examples are built while sourcing the SDK. If subsequent edits are made, the examples can be rebuilt by navigating to the example source directory and running:

`make`


To build a specific example:

* `make clear_single_fpga`
* `make clear_multiple_fpga`
* `make load_single_fpga`
* `make load_multiple_fpga`
* `make prefetch_multiple_afi`


## Running the Examples
Ensure you have sourced the AWS FPGA SDK before running:

`source ./sdk_setup.sh`


Run an example:

* `sudo ./clear_single_fpga`
* `sudo ./clear_multiple_fpga`
* `sudo ./load_single_fpga`
* `sudo ./load_multiple_fpga`
* `sudo ./prefetch_multiple_afi`


## Important Notes
- These examples must be run on an F2 instance
- `fpga_mgmt_load_local_image`, `fpga_mgmt_load_local_image_flags`, and `fpga_mgmt_load_local_image_with_options` send the load command and return without waiting for the load to finish. Immediately after calling one of them, call `fpga_mgmt_describe_local_image` once a second until the AFI is loaded and the status is no longer busy. The load is completed by these describe calls, so if you don't poll, the AFI might not load. `load_multiple_fpga.c` shows this pattern. The `_sync` variants, used by `load_single_fpga.c`, poll for you.
- Ensure you have the correct AFI ID when loading images
- Always check error messages for troubleshooting

## License
http://aws.amazon.com/apache2.0/

## Support
https://github.com/aws/aws-fpga
