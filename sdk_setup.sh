#!/bin/bash

#
# Copyright 2015-2016 Amazon.com, Inc. or its affiliates. All Rights Reserved.
#
# Licensed under the Apache License, Version 2.0 (the "License"). You may
# not use this file except in compliance with the License. A copy of the
# License is located at
#
#     http://aws.amazon.com/apache2.0/
#
# or in the "license" file accompanying this file. This file is distributed
# on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
# express or implied. See the License for the specific language governing
# permissions and limitations under the License.
#

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
