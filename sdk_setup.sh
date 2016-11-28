#!/bin/bash

export SDK_DIR=${SDK_DIR:=$(pwd)/sdk}

echo "Done setting environment variables."

# 
# Execute sdk_install.sh inside a subshell so the user's current
# shell does not exit on errors from the install.
# 
bash $SDK_DIR/sdk_install.sh
RET=$?

if [ $RET != 0 ]; then
    echo "Error: AWS SDK install was unsuccessful, sdk_install.sh returned $RET" 
	exit $RET
fi

echo "Done with AWS SDK setup."
