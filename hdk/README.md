# AWS FPGA HDK
<span style="display: inline-block;">
[![API Reference](http://img.shields.io/badge/api-reference-blue.svg)](http://docs.aws.amazon.com/techdoc/fpga)
[![Join the chat at https://gitter.im/aws/aws-fpga](https://badges.gitter.im/Join%20Chat.svg)](https://gitter.im/aws/aws-fpga?utm_source=badge&utm_medium=badge&utm_campaign=pr-badge&utm_content=badge)


AWS FPGA HDK is the official AWS HDK for programming FPGA on AWS EC2 and generating Amazon FPGA Image (AFI)

Check out our [release notes](./release_notes.md) for information about the latest bug fixes, updates, and features added to the HDK.

## Overview

AWS FPGA HDK includes all design files and scripts needed to generate an Amazon FPGA Image (AFI). Developers can download it and use it in their preferred design environment. AWS do offer an AMI with the needed tools to develop, simulate and compile called `FPGA Developer AMI`  on [AWS Marketplace](https://aws.amazon.com/marketplace) 

## Installion

AWS FPGA HDK and SDK can be cloned to your EC2 instance or server by calling:
`
after installing, go the root directory of the HDK and call ‘sh hdk_setup.sh’ to setup the environment

## Content

The [/doc](./doc) directory have a step by step walkthrough how to use the HDK

The [Custom Logic (cl)](./cl) directory is where the Custom Logic is expected to be developed, it includes a set of [examples directory](./cl/examples), as well as a placeholder for developer's own Custom Logic under [developers_design directory] (./cl/developers_design).  

The [common directory] (./common) include AWS-provided scripts, timing constrains and compile settings required during the AFI generation process. Developers should not change these files
