#!/bin/bash

export HDK_DIR=${HDK_DIR:=$(pwd)/hdk}

# The next variable should not be modified and should always point to the /common directory that's provided by HDK
export HDK_COMMON_DIR=$(HDK_DIR)/common

# Point to the latest version of AWS shell
export HDK_SHELL_DIR=$(HDK_COMMON_DIR)/shell_latest

# The CL_DIR is where the actual Custom Logic design reside, the developer is expected to override this
export CL_DIR=$(HDK_DIR)/cl/developer_designs

# Create DDR and PCIe IP models and patch PCIe
source $(HDK_DIR)/common/verif/scripts/init.sh
