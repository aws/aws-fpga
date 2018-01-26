# Amazon FPGA Hardware Development Kit
#
# Copyright 2016 Amazon.com, Inc. or its affiliates. All Rights Reserved.
#
# Licensed under the Amazon Software License (the "License"). You may not use
# this file except in compliance with the License. A copy of the License is
# located at
#
#    http://aws.amazon.com/asl/
#
# or in the "license" file accompanying this file. This file is distributed on
# an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, express or
# implied. See the License for the specific language governing permissions and
# limitations under the License.

function info_msg {
  echo -e "INFO: $1"
}

function debug_msg {
  if [[ $debug == 0 ]]; then
    return
  fi
  echo -e "DEBUG: $1"
}

function err_msg {
  echo -e >&2 "ERROR: $1"
}

function warn_msg {
  echo -e "WARNING: $1"
}

function setup_patches {

    bucket="aws-fpga-developer-ami/1.3.3/Patches"
    object="AR703530_SDx_patch.zip"
    patch_dirname="AR703530"
    patch_root="$AWS_FPGA_REPO_DIR/patches"

    if [ ! -d $patch_root/$patch_dirname ]; then

        info_msg "Downloading the $patch_dirname patch."

        curl -s https://s3.amazonaws.com/$bucket/$object -o $object || { err_msg "Failed to download Patch $object from $bucket/$object"; return 2; }

        mkdir -p $patch_root || { err_msg "Failed to create path $patch_root"; return 2; }

        info_msg "Extracting the $patch_dirname patch."

        unzip $object -d $patch_root/$patch_dirname || { err_msg "Failed to unzip $object into: $patch_root/$patch_dirname"; return 2; }

        rm $object

        chmod -R 755 $patch_root/$patch_dirname

    fi

    : ${MYVIVADO:=$patch_root/$patch_dirname/vivado}
    export MYVIVADO=$MYVIVADO

}
