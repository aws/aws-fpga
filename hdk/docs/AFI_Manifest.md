# AWS AFI Manifest File Specification

An AFI submission to AWS using  `aws ec2 create-fpga-image` includes a pointer to an S3 bucket with a tar file: The tar file includes the encrypted and compiled fpga image(a.k.a. Design Checkpoint or DCP) and a mandatory `manifest.txt` file.

This document provides the specification for the `manifest.txt` file.  Note that an AFI built through the scripts provided by AWS will generate the manifest file automatically.


The manifest file is a text file formatted with key=value pairs. Some keys are mandatory while others are highly recommended. The mandatory keys are marked with [Mandatory]

## Manifest file specification: Version 1

* **manifest_format_version=** 1 [Mandatory]  

* **pci_vendor_id=** [Mandatory]  
      *0x1D0F is the detault value that is pre-assigned by Amazon*

* **pci_device_id=** [Mandatory]  
      *0xF000 is the detault value that is pre-assigned by Amazon*

* **pci_subsystem_id=** [Mandatory]  
      *Must be non-zero*
      
* **pci_subsystem_vendor_id=** [Mandatory]  
      *Must be non-zero* 

* **dcp_hash=**.....   [Mandatory]    
      *Includes the sha256sum value of the submitted Design Checkpoint (DCP)*

* **shell_version**=.....   [Mandatory]  
      *Taken from aws-fpga/hdk/common/[shell directory]/build/checkpoints/from_aws*

* **dcp_file_name=**.....   [Mandatory]  
      *The .dcp file name including the file type suffix*

* **hdk_version=**.....     
      *Taken from aws-fpga/hdk/hdk_version.txt* 

* **date=** YY_MM_DD-HHMMSS     
      *Following same format used in the automatic build reports used by AWS scripts*

* **clock_recipe_a**=....   [Mandatory]  
      *A clock recipe ID in the form Ax, indicating which clock settings will be used in clock group A in this CL*  
      *Supported clock recipes are listed in Clock Group A of [supported clock recipes](./clock_recipes.csv)*
 
* **clock_recipe_b**=....  
      *A clock recipe ID in the form Bx, indicating which clock settings will be used in clock group B in this CL*  
      *Supported clock recipes are listed in Clock Group B of [supported clock recipes](./clock_recipes.csv)*  
      *If this field is missing, recipe B0 will be used*
 
* **clock_recipe_c**=....   
      *A clock recipe ID in the form Cx, indicating which clock settings will be used in clock group C in this CL*  
      *Supported clock recipes are listed in Clock Group C of [supported clock recipes](./clock_recipes.csv)*  
      *If this field is missing, recipe C0 will be used*

