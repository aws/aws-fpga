# AWS EC2 FPGA SDK Management directories

The [fpga_image_tools directory](./fpga_image_tools) contains the [Amazon FPGA Image (AFI) Management Tools](./fpga_image_tools/README.md).

APIs, Hardware Abstraction Layers (HALs), and utilities needed for building the AFI Management Tools are found in the [`include`](./include), [`hal`](./hal), and [`utils`](./utils) directories.

The developer have one of two options to use the management tools:

1) Compile and install the reference tools found under [`/fpga_image_tool` directory](./fpga_image_tools). Once the install is successful, the developer can use these tools through linux shell command line.

2) Integrate the provided source code into the developer C/C++ application for performing FPGA management without invoking shell command line.

