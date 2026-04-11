# Amazon FPGA Hardware Development Kit
#
# Copyright 2020 Amazon.com, Inc. or its affiliates. All Rights Reserved.
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
    if [[ ${debug:-0} == 0 ]]; then
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

function get_tools_dst_dir {
  echo $PATH | grep -q "/usr/local/bin"
  if [[ $? -ne 0 ]] ; then
    echo "/usr/bin"
  else
    echo "/usr/local/bin"
  fi
}

[[ -n "${BASH_VERSION:-}" ]] && export -f get_tools_dst_dir
function get_tools_lib_dir {
  if [ -d "/usr/local/lib64" ]; then
    echo "/usr/local/lib64"
  elif [ -d "/usr/local/lib" ]; then
    echo "/usr/local/lib"
  elif [ -d "/usr/lib64" ]; then
    echo "/usr/lib64"
  elif [ -d "/usr/lib" ]; then
    echo "/usr/lib"
  else
    err_msg "Error: No directory for installing libraries."
    exit 1
  fi
}
[[ -n "${BASH_VERSION:-}" ]] && export -f get_tools_lib_dir

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

identify_coap_server() {
  local flavor=$(awk -F"=" '/^ID_LIKE/{print $2}' /etc/os-release)
  local card_ips=""
  echo ${flavor} | grep -iq rhel && lease_file=/var/lib/dhcpd/dhcpd.leases
  echo ${flavor} | grep -iq debian && lease_file=/var/lib/dhcp/dhcpd.leases
  local possible_servers=$(awk '/^lease/{print $2}' ${lease_file} | sort -u)
  for server in ${possible_servers} ;do
    ping -c 1 ${server} >/dev/null 2>&1 && card_ips="${card_ips} ${server}"
  done
  echo $(echo $card_ips | xargs)
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
    # unset MYVIVADO so we always start with a clear non-patched version
    unset MYVIVADO

    patch_AR70350
}

function patch_AR70350 {
    local bucket="aws-fpga-developer-ami/1.3.3/Patches"
    local object="AR703530_SDx_patch.zip"
    local patch_dirname="AR703530"
    local patch_root="$AWS_FPGA_REPO_DIR/patches"
    declare -a valid_vivado_versions=(	"Vivado v2017.1_sdx (64-bit)"
                                        "Vivado v2017.1_sdxop (64-bit)"
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
        if [ ! -d $patch_root/$patch_dirname ]; then

            info_msg "Downloading the $patch_dirname patch."

            curl -s https://s3.amazonaws.com/$bucket/$object -o $object || { err_msg "Failed to download Patch $object from $bucket/$object"; return 2; }

            mkdir -p $patch_root || { err_msg "Failed to create path $patch_root"; return 2; }

            info_msg "Extracting the $patch_dirname patch."

            unzip $object -d $patch_root/$patch_dirname || { err_msg "Failed to unzip $object into: $patch_root/$patch_dirname"; return 2; }

            rm $object

            chmod -R 755 $patch_root/$patch_dirname
        fi

        munge_myvivado_var $patch_root/$patch_dirname/vivado
    fi

}

function check_vivado_version() {
    local act_version="$1" exp_version_file="$2" compare="$3"

    extract_vivado_version "$act_version" || { VIVADO_VERSION_CHECK=0; return 1; }
    local act_base="$EXTRACTED_VIVADO_BASEVER" act_patches="$EXTRACTED_VIVADO_PATCHES"
    local act_bits="$EXTRACTED_VIVADO_OSBITS" act_patch_num="$EXTRACTED_VIVADO_PATCHES_NUM"

    [[ -f "$exp_version_file" ]] || { VIVADO_VERSION_CHECK=0; return 1; }

    while IFS= read -r line; do
        [[ -z "$line" || "$line" =~ ^[[:space:]]*# ]] && continue

        extract_vivado_version "$line" || continue

        [[ "$EXTRACTED_VIVADO_BASEVER" == "$act_base" && "$EXTRACTED_VIVADO_OSBITS" == "$act_bits" ]] || continue

        local patch_num=$([[ $compare -eq 0 ]] && echo "$EXTRACTED_VIVADO_PATCHES_NUM" || echo "$act_patch_num")
        if [[ $patch_num -eq 0 ]]; then
            VIVADO_VERSION_CHECK=1
            return 0
        fi

        local matches=0 act_array=($act_patches) exp_array=($EXTRACTED_VIVADO_PATCHES)
        for ap in "${act_array[@]}"; do
            for ep in "${exp_array[@]}"; do
                [[ "$ap" == "$ep" ]] && ((matches++))
            done
        done

        [[ $matches -eq $patch_num ]] && { VIVADO_VERSION_CHECK=1; return 0; }

    done < "$exp_version_file"

    VIVADO_VERSION_CHECK=0
}

function extract_vivado_version() {
    local version="$1"
    [[ -z "$version" ]] && return 1

    local remainder vivado_token tail osbits patches patches_no_underscores

    remainder="${version#* }"
    [[ "$remainder" == "$version" ]] && return 1

    vivado_token="${remainder%% *}"
    tail="${remainder#* }"
    [[ "$tail" == "$remainder" ]] && return 1

    osbits="${tail##* }"

    [[ -z "$vivado_token" || -z "$osbits" ]] && return 1

    EXTRACTED_VIVADO_BASEVER="${vivado_token%%_*}"
    patches="${vivado_token#*_}"

    if [[ "$patches" == "$vivado_token" ]]; then
        EXTRACTED_VIVADO_PATCHES=""
        EXTRACTED_VIVADO_PATCHES_NUM=0
    else
        EXTRACTED_VIVADO_PATCHES="${patches//_/ }"
        patches_no_underscores="${patches//_/}"
        EXTRACTED_VIVADO_PATCHES_NUM=$(( ${#patches} - ${#patches_no_underscores} + 1 ))
    fi

    EXTRACTED_VIVADO_OSBITS="${osbits//[()]/}"

    return 0
}

function allow_non_root {
       [ ! -z ${AWS_FPGA_ALLOW_NON_ROOT} ]
}

function get_pkg_manager {
    os=$(cat /etc/os-release)
    install_command=""
    if [[ "${os}" == *"Ubuntu"* ]]; then
        install_command="apt"
    elif [[ "${os}" == *"Rocky Linux"* ]]; then
        install_command="dnf"
    else
        err_msg "Couldn't find a package list for this distro!"
        return 1
    fi
    echo "${install_command}"
}

function get_install_command {
    local pkg_manager=$(get_pkg_manager)
    [[ -z "$pkg_manager" ]] && return 1
    echo "sudo ${pkg_manager} install -y"
}

function is_rocky_linux {
    [[ $(cat /etc/os-release) == *"Rocky Linux"* ]]
}

function is_ubuntu {
    [[ $(cat /etc/os-release) == *"Ubuntu"* ]]
}

function check_for_empty_var {
    local var_name="$1"
    local var_value="$2"
    local error_msg="${3:-Variable ${var_name} is not defined or empty!}"

    [[ -z "$var_value" ]] && err_msg "$error_msg" && return 1
    return 0
}
