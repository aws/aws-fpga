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

function is_myvivado_set {
    if env | grep -q ^MYVIVADO=
    then
        true
    else
        false
    fi
}


function is_vivado_available {
    if ! vivado -version > /dev/null 2>&1 ; then
        false
    else
        true
    fi
}

function get_base_vivado_version {
    local  __resultvar=$1

    if is_myvivado_set
    then

        local MYVIVADO_ENV_VAR_BACKUP=$MYVIVADO

        unset MYVIVADO
        local __vivado_version=$(get_vivado_version)
        export MYVIVADO=$MYVIVADO_ENV_VAR_BACKUP
    else

        local __vivado_version=$(get_vivado_version)
    fi

    if [[ "$__resultvar" ]]; then
        eval $__resultvar="'$__vivado_version'"
    else
        echo "$__vivado_version"
    fi

}

function munge_myvivado_var {
    if [[ ! -z $1 ]]; then
        if ! echo "$MYVIVADO" | /bin/grep -Eq "(^|:)$1($|:)" ; then
            if [ "$2" = "after" ] ; then
                MYVIVADO="$MYVIVADO:$1"
            else
                MYVIVADO="$1:$MYVIVADO"
            fi
        fi
        export MYVIVADO
    fi
}

function get_vivado_version {
    local __resultvar=$1

    local __vivado_version=`vivado -version | grep Vivado | head -1`

    if [[ "$__resultvar" ]]; then
        eval $__resultvar="'__$vivado_version'"
    else
        echo "$__vivado_version"
    fi
}

function setup_patches {
    patch_AR71715
}

function patch_AR71715 {
    local bucket="aws-fpga-developer-ami/1.5.0/Patches"
    local object="AR71715.zip"
    local patch_dirname="AR71715"
    local patch_root="$XILINX_SDX/patches"
    local tool_dir="$XILINX_SDX"

    declare -a valid_vivado_versions=( "Vivado v2018.2_AR71275_op (64-bit)"
                                        "Vivado v2018.2.op (64-bit)"
                                        "Vivado v2018.2 (64-bit)"
                                     )

    local base_vivado_version=$(get_base_vivado_version)
    is_patch_valid=false
    info_msg "Base vivado version is $base_vivado_version ; Checking if patch AR71715 needs to be installed"
    for vivado_version in "${valid_vivado_versions[@]}"
    do
        if [ ":$vivado_version" == ":$base_vivado_version" ]; then
            is_patch_valid=true
        fi
    done

    if [ "$is_patch_valid" == "true" ]; then

        info_msg " SDX patch $patch_dirname is valid for $base_vivado_version"

        if [ ! -d $patch_root/$patch_dirname ]; then

            info_msg "Downloading the $patch_dirname patch."

            curl -s https://s3.amazonaws.com/$bucket/$object -o $object || { err_msg "Failed to download Patch $object from $bucket/$object"; return 2; }

            sudo mkdir -p $patch_root || { err_msg "Failed to create path $patch_root  you need to have root permissions to install this patch. If you dont have root permissions please contact your system administrator";  return 2; }

            info_msg "Extracting the $patch_dirname patch."

            sudo unzip $object -d $patch_root/$patch_dirname || { err_msg "Failed to unzip $object into: $patch_root/$patch_dirname"; return 2; }
            sudo cp $tool_dir/scripts/ocl/ocl_util.tcl $tool_dir/scripts/ocl/ocl_util.tcl.bkp
            sudo cp -f $patch_root/$patch_dirname/sdx/scripts/ocl/ocl_util.tcl $tool_dir/scripts/ocl/ocl_util.tcl

            rm $object

            chmod -R 755 $patch_root/$patch_dirname
        fi
    fi
}


function allow_non_root {
       [ ! -z ${AWS_FPGA_ALLOW_NON_ROOT} ]
}
