# AWS AFI Manifest File Specification

An AFI submission to AWS through  [`aws ec2 create-fpga-image` API](./TBD), includes a pointer to an S3 bucket with a tar file: The tar file includes the encrypted and compiled fpga image(a.k.a. Design Checkpoint or DCP) and a mandatory `manifest.txt` file.

This document provides the specification for the `manifest.txt` file.  Note that an AFI built through the scripts provided by AWS would have the manifest file generated automatically.


The manifest file is a text file formatted with KEY/VALUE pairs. Some keys are mandatory while others are highly recommended. The mandatory keys are marked with [Mandatory]

## Manifest file specification: Version 1

* **manifest_format_version=**1 [Mandatory]  

* **pci_vendor_id=** [Mandatory]
      * 0x1D0F for Amazon

* **pci_device_id=** [Mandatory]
      * 0xF000 through 0xF0FF for example CLs.

* **pci_subsystem_id=** [Optional]
      * defaults to 0 if not available
      
* **pci_subsystem_vendor_id=** [Optional]
      * defaults to 0 if not available
       
* **dcp_hash=**.....   [Mandatory]    
      *Includes the sha256sum value of the submitted Design Checkpoint (DCP)*

* **shell_version**=.....   [Mandatory]  
      *Taken from aws-fpga/hdk/common/[shell directory]/build/checkpoints/from_aws*

* **dcp_file_name=**.....     
      *The .dcp file name including the file type suffix*

* **hdk_version=**.....     
      *[TBD]* 

* **date=** YY_MM_DD-HHMM     
      *Following same format used in the automatic build reports used by AWS scripts*
      
* **clk_main_a0=**      
      *Frequency of main and global clk_main_a0 in Mhz. When this setting is missing, the default value would be 125.   Legal values are from 10 to 250*
      
* **clk_extra_a1=**      
      *CL input clock clk_extra_a1 frequency in Mhz. It must be an integer divider of clk_main_a0. When this setting is missing, the default value would be equal to CLK_MAIN value*
      
* **clk_extra_a2=**      
      *CL input clock clk_extra_a2 frequency in Mhz. It must be an integer divider of clk_main_a0. When this setting is missing, the default value would be equal to CLK_MAIN value*
      
* **clk_extra_a3=**      
      *CL input clock clk_extra_a3 frequency in Mhz. It must be an integer divider of clk_main_a0. When this setting is missing, the default value would be equal to CLK_MAIN value*
      
* **clk_extra_b0=**      
      *CL input clock clk_extra_b0 frequency in Mhz. It can have any value up to 500. When this setting is missing, the default value would be equal to clk_main_a0 value*
      
* **clk_extra_b1=**      
      *CL input clock clk_extra_b1 frequency in Mhz. It must be an integer divider of CLK_EXTRA_B0. When this setting is missing, the default value would be equal to clk_extra_b0 value*
      
* **clk_extra_c0=**      
      *CL input clock clk_extra_c0 frequency in Mhz. It can have any value up to 500. When this setting is missing, the default value would be equal to clk_main_a0 value*
      
* **clk_extra_c1=**      
      *CL input clock clk_extra_c1 in Mhz. It must be an integer divider of CLK_EXTRA_C1. When this setting is missing, the default value would be equal to clk_extra_c0 value*

      
      
      
 
