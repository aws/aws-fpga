# AWS AFI Manifest File Specification

An AFI submittion to AWS through  [`aws ec2 createFpgaImage` API](./TBD), which includes a pointer to an S3 bucket with a tar file: The tar file would include the encrypted and compiled fpga image(a.k.a. Design Checkpoint or DCP) and a mandatory `manifest.txt` file.

This document provides the specification for the `manifest.txt` file.  While worth nothing that AFI built through the scripts provided by AWS would have the manifest file generated automatically.


The manifest file is a text file formated with KEY=VALUE pairs. Some keys are mandatory while others are highly reocmmended

##The mandatory keys are marked with [Mandatory]

## Manifest file specification: Version 1

* **MANIFEST_FORMAT_VERSION=**1 [Mandatory]  
      
* **DCP_HASH=**.....   [Mandatory]    
      *Includes the sha256sum value of the submitted Design Checkpoint (DCP)*

* **SHELL_VERSION**=......   [Mandatory]  
      *Taken from aws-fpga/hdk/common/[shell directory]/build/checkpoints/from_aws*

* **FILE_NAME=**.....     
      *The .dcp file name including the file type suffix*

* **HDK_VERSION=**.....     
      *[TBD]* 

* **DATE=** YY_MM_DD-HHMM     
      *Following same format used in the automatic build reports used by AWS scripts*
      
* **CLK_MAIN=**      
      *Frequency of main and global clk_main in Mhz. When this setting is missing, the default value would be 125.   Legal values are from 10 to 250*
      
* **CLK_EXTRA_A1=**      
      *Extra clock A1 frequency in Mhz. It must be an integer divider of CLK_MAIN. When this setting is missing, the default value would be equal to CLK_MAIN value*
      
* **CLK_EXTRA_A2=**      
      *Extra clock A2 frequency in Mhz. It must be an integer divider of CLK_MAIN. When this setting is missing, the default value would be equal to CLK_MAIN value*
      
* **CLK_EXTRA_A3=**      
      *Extra clock A3 frequency in Mhz. It must be an integer divider of CLK_MAIN. When this setting is missing, the default value would be equal to CLK_MAIN value*
      
* **CLK_EXTRA_B0=**      
      *Extra clock B0 frequency in Mhz. It can have any value up to 500. When this setting is missing, the default value would be equal to CLK_MAIN value*
      
* **CLK_EXTRA_B1=**      
      *Extra clock A1 frequency in Mhz. It must be an integer divider of CLK_EXTRA_B0. When this setting is missing, the default value would be equal to CLK_EXTRA_B0 value*
      
* **CLK_EXTRA_C0=**      
      *Extra clock C0 frequency in Mhz. It can have any value up to 500. When this setting is missing, the default value would be equal to CLK_MAIN value*
      
* **CLK_EXTRA_C1=**      
      *Extra clock C1 frequency in Mhz. It must be an integer divider of CLK_EXTRA_C1. When this setting is missing, the default value would be equal to CLK_EXTRA_C0 value*

      
      
      
 
