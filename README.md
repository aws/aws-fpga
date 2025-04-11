
![f2_headline_graphic](./shared/assets/f2_headline_graphic.png)

# AWS F2

## F2 FPGA Development Kit Overview

The documentation and assets provided on this branch (and other branches prefixed with `f2`) are relevant to F2 instances only.

The F2 FPGA Development Kit is a hardware-software development kit that enables developers to create accelerators for the high-performance accelerator cards on EC2 F2 instances. Using the development kit, you can architect, simulate, optimize, and test your designs.

## F2 FPGA Development Kit Documentation

For full documentation, including a user guide, code snippets, and tutorials, see the [AWS EC2 FPGA Development Kit User Guide](./User_Guide_AWS_EC2_FPGA_Development_Kit.md)

## F2 FPGA ReadTheDocs (Beta)

We are currently migrating our F2 documentation to comply with the ReadTheDocs standard. To familiarize yourself with the new layout, please [click here](https://awsdocs-fpga-f2.readthedocs-hosted.com).

# ❗Amazon EC2 F1 End of Life Notice❗

We are retiring the F1 instances on December 20, 2025.

Only existing F1 customers who have run F1 instances anytime between Dec 2023 - Dec 2024 can restart or launch new F1 instances. Effective December 20, 2025, F1 instances or access data stored on F1 instance local storage will be no longer available. Please transfer any needed data stored in F1 instance local storage before December 20, 2025.

| aws-fpga F1 Branch       | devKit Version | devAMI                                                                                                                                                                                                                      |
|:-------------------------|:---------------|:----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
| [f1_xdma_shell](https://github.com/aws/aws-fpga/tree/f1_xdma_shell)            | 1.4.25+        | [FPGA Developer AMI 1.16.1 (Ubuntu)](https://aws.amazon.com/marketplace/pp/prodview-f5kjsenkfkz5u) |
| [f1_small_shell](https://github.com/aws/aws-fpga/tree/f1_small_shell)           | 1.4.25+        | [FPGA Developer AMI 1.16.1 (Ubuntu)](https://aws.amazon.com/marketplace/pp/prodview-f5kjsenkfkz5u) |

# Support

For any issues with this developer kit documentation or code, please open a [GitHub issue](https://github.com/aws/aws-fpga/issues) with all steps to reproduce.

For questions, please open a [re:Post issue with the 'FPGA Development' tag](https://repost.aws/tags/TAc7ofO5tbQRO57aX1lBYbjA/fpga-development).