export HDK_DIR=${HDK_DIR:=`pwd`}

# The next variable should not be modified and should always point to the /common directory that's provided by HDK
export HDK_COMMON_DIR=$HDK_DIR/common

# The CL_DIR is where the actual Custom Logic design reside, the developer is expected to override this
export CL_DIR=$HDK_DIR/cl/developer_designs
