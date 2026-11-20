AWS AFI Manifest File Specification
===================================

An AFI submission to AWS using ``aws ec2 create-fpga-image`` includes a
pointer to an S3 bucket with a tar file containing the encrypted FPGA
Design Checkpoint (DCP) and a mandatory ``manifest.txt`` file.

This document is a purely informative specification for the
``manifest.txt`` file formatted with key=value pairs. Developers should
never manually modify the manifest as it’s automatically created by the
AWS build scripts.

Manifest file specification: Version 2
--------------------------------------

- **manifest_format_version=** 2

- **pci_vendor_id=**

  - *0x1D0F is the default value that is pre-assigned by Amazon - For
    more information, see* `AFI PCIe
    IDs <./../README.html#afi-pcie-ids>`__

- **pci_device_id=**

  - *0xF000 is the default value that is pre-assigned by Amazon - For
    more information, see* `AFI PCIe
    IDs <./../README.html#afi-pcie-ids>`__

- **pci_subsystem_id=**

  - *Must be non-zero - For more information, see* `AFI PCIe
    IDs <./../README.html#afi-pcie-ids>`__

- **pci_subsystem_vendor_id=**

  - *Must be non-zero - For more information, see* `AFI PCIe
    IDs <./../README.html#afi-pcie-ids>`__

- **dcp_hash=**\ …..

  - *Includes the sha256sum value of the submitted Design Checkpoint
    (DCP)*

- **shell_version=**\ …..

  - *The hex ID of the shell the design was built for, for example
    ``0x10212415`` for the Small Shell or ``0x10052623`` for the XDMA
    Shell. The released shell IDs are listed in*
    `aws-fpga/hdk/common/shell_stable/shell_version.txt <https://github.com/aws/aws-fpga/tree/f2/hdk/common/shell_stable/shell_version.txt>`__

- **dcp_file_name=**\ …..

  - *The .dcp file name including the file type suffix*

- **hdk_version=**\ …..

  - *Taken from aws-fpga/release_version.txt*

- **tool_version=**\ …..

  - *Use the vivado tool version used (from the*
    `supported_vivado_versions.txt <https://github.com/aws/aws-fpga/tree/f2/supported_vivado_versions.txt>`__\ *).
    For example, you would enter ``2024.1`` into the manifest for a
    supported version of ``vivado v2024.1 (64-bit)``*

- **date=YY_MM_DD-HHMMSS**

  - *Following same format used in the automatic build reports used by
    AWS scripts*

- **clock_recipe_a=**\ ….

  - *Deprecated, please refer to the* `AWS Clock Recipes User
    Guide <./Clock-Recipes-User-Guide.html>`__

- **clock_recipe_b=**\ ….

  - *Deprecated, please refer to the* `AWS Clock Recipes User
    Guide <./Clock-Recipes-User-Guide.html>`__

- **clock_recipe_c=**\ ….

  - *Deprecated, please refer to the* `AWS Clock Recipes User
    Guide <./Clock-Recipes-User-Guide.html>`__

- **clock_recipe_hbm=**\ ….

  - *Deprecated, please refer to the* `AWS Clock Recipes User
    Guide <./Clock-Recipes-User-Guide.html>`__

`Back to Home <../../index.html>`__
