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

function is_xilinx_path_set {
    if env | grep -q ^XILINX_PATH
    then
        true
    else
        false
    fi
}

# Function to check whether a command exists.
exists() {
    if command -v $1 >/dev/null 2>&1
    then
        return 0
    else
        return 1
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
    elif is_xilinx_path_set
    then
        local XILINX_PATH_ENV_VAR_BACKUP=$XILINX_PATH
        unset XILINX_PATH
        local __vivado_version=$(get_vivado_version)
        export XILINX_PATH=$XILINX_PATH_ENV_VAR_BACKUP
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
    local caller_script="${BASH_SOURCE[1]}"

    info_msg "Checking if patch AR71715 needs to be installed"
    patch_AR71715

    info_msg "Checking if patch AR73068 needs to be installed"
    patch_AR73068 "$caller_script"
}

function is_patch_applied {
    local patch_name="$1"
    local long_vivado_version=$(get_vivado_version)

    if [[ "$long_vivado_version" =~ .*"$patch_name".* ]]; then
      true
    else
      false
    fi
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
    for vivado_version in "${valid_vivado_versions[@]}"
    do
        if [ ":$vivado_version" == ":$base_vivado_version" ]; then
            is_patch_valid=true
        fi
    done

    if [ "$is_patch_valid" == "true" ]; then

        info_msg "Patch AR71715 is valid for $base_vivado_version"

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

function install_patch {
    local patch_name="$1"
    local patch_bucket="$2"
    local patch_object="$3"
    local patch_dir_name="${patch_object%.*}"

    if is_patch_applied $patch_name
    then
        info_msg "$patch_name is already applied. Skipping."
    else
        info_msg "Applying $patch_name"
        info_msg "in bucket $patch_bucket"
        info_msg "object $patch_object"

        # Checking if the patches directory exists and making it if it doesn't
        [ -d $script_dir/patches ] || mkdir -p $script_dir/patches

        info_msg "Downloading the $patch_name from $patch_bucket/$patch_object."
        debug_msg "curl -s $patch_bucket/$patch_object -o $script_dir/patches/$patch_object"

        curl -s $patch_bucket/$patch_object -o $script_dir/patches/$patch_object || { err_msg "Failed to download Patch $object from $patch_bucket/$patch_object"; return 2; }

        info_msg "Extracting the $patch_name to $script_dir/patches/$patch_dir_name."

        unzip -q -o $script_dir/patches/$patch_object -d $script_dir/patches/$patch_dir_name  || { err_msg "Failed to extract $script_dir/patches/$patch_object to $script_dir/patches/$patch_dir_name"; return 2; }

        # XILINX_PATH should not have AR73068 at this point.
        info_msg "Appending XILINX_PATH with $script_dir/patches/$patch_dir_name/vivado"

        export XILINX_PATH=$XILINX_PATH:$script_dir/patches/$patch_dir_name/vivado
    fi
}

function fix_patch_vitis_AR73068_2019_2 {
    local patch_object="$1"
    local patch_dir_name="${patch_object%.*}"
    pushd patches/$patch_dir_name

    sed -i '/.*checksum.*/d' ./vivado/data/ip/xilinx/ddr4_v2_2/component.xml
    sed -i 's/coreRevision>73068/coreRevision>8/' ./vivado/data/ip/xilinx/ddr4_v2_2/component.xml
    popd
}

function patch_AR73068_2019_2 {
    info_msg "Patching Vivado/Vitis 2019.2 with Xilinx Patch AR73068"
    local fix_patch="$1"
    local patch_bucket="https://aws-fpga-developer-ami.s3.amazonaws.com/1.8.0/Patches/AR73068"
    local patch_object="AR73068_Vivado_2019_2_preliminary_rev1.zip"

    install_patch "AR73068" "$patch_bucket" "$patch_object"

    if [[ "$fix_patch" == true ]]; then
      info_msg "Fixing Patch AR73068 for Vitis"
      fix_patch_vitis_AR73068_2019_2 "$patch_object"
    fi
}

function patch_AR73068_2019_1 {
    info_msg "Patching Vivado 2019.1 with Xilinx Patch AR73068"

    local patch_bucket="https://aws-fpga-developer-ami.s3.amazonaws.com/1.7.0/Patches/AR73068"
    local patch_object="AR73068_Vivado_2019_1_preliminary_rev1.zip"

    install_patch "AR73068" "$patch_bucket" "$patch_object"
}

function patch_AR73068_2018_3 {
    info_msg "Patching Vivado 2018.3 with Xilinx Patch AR73068"

    local patch_bucket="https://aws-fpga-developer-ami.s3.amazonaws.com/1.6.0/Patches/AR73068"
    local patch_object="AR73068_Vivado_2018_3_preliminary_rev1.zip"

    install_patch "AR73068" "$patch_bucket" "$patch_object"
}

function patch_AR73068_2018_2 {
    info_msg "Patching Vivado 2018.2 with Xilinx Patch AR73068"

    local patch_bucket="https://aws-fpga-developer-ami.s3.amazonaws.com/1.5.0/Patches/AR73068"
    local patch_object="AR73068_Vivado_2018_2_preliminary_rev1.zip"

    install_patch "AR73068" "$patch_bucket" "$patch_object"
}

function patch_AR73068_2017_4 {
    info_msg "Patching Vivado 2017.4 with Xilinx Patch AR73068"

    local patch_bucket="https://aws-fpga-developer-ami.s3.amazonaws.com/1.4.0/Patches/AR73068"
    local patch_object="AR73068_Vivado_2017_4_preliminary_rev2.zip"

    install_patch "AR73068" "$patch_bucket" "$patch_object"
}

function patch_AR73068 {
    local base_vivado_version=$(get_base_vivado_version)
    local caller_script="$1"
    local fix_patch=false

    # Vitis specific changes
    if [[ "$caller_script" =~ "vitis_setup.sh" ]]; then
      info_msg "Patching Vitis with AR73068"
      fix_patch=true
    fi

    if [[ "${base_vivado_version}" =~ "Vivado v2019.2" ]]; then
      info_msg "Patch $patch_name is valid for Vivado $base_vivado_version."
      patch_AR73068_2019_2 "$fix_patch"
    elif [[ "${base_vivado_version}" =~ "Vivado v2019.1" ]]; then
      info_msg "Patch $patch_name is valid for Vivado $base_vivado_version."
      patch_AR73068_2019_1
    elif [[ "${base_vivado_version}" =~ "Vivado v2018.3" ]]; then
      info_msg "Patch $patch_name is valid for Vivado $base_vivado_version."
      patch_AR73068_2018_3
    elif [[ "${base_vivado_version}" =~ "Vivado v2018.2" ]]; then
      info_msg "Patch $patch_name is valid for Vivado $base_vivado_version."
      patch_AR73068_2018_2
    elif [[ "${base_vivado_version}" =~ "Vivado v2017.4" ]]; then
      info_msg "Patch $patch_name is valid for Vivado $base_vivado_version."
      patch_AR73068_2017_4
    else
      info_msg "Patch AR73068 not applicable for Vivado ${base_vivado_version}."
    fi
}

function allow_non_root {
       [ ! -z ${AWS_FPGA_ALLOW_NON_ROOT} ]
}

function allow_others {
       [ ! -z ${AWS_FPGA_SDK_OTHERS} ]
}
