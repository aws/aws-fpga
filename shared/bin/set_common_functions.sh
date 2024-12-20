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

function get_tools_dst_dir {
  echo $PATH | grep -q "/usr/local/bin"
  if [[ $? -ne 0 ]] ; then
    echo "/usr/bin"
  else
    echo "/usr/local/bin"
  fi
}

export -f get_tools_dst_dir
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
export -f get_tools_lib_dir

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

function check_vivado_version () {
   local act_version=$1;      shift
   local exp_version_file=$1; shift
   local compare=$1;          shift

   #echo "check_vivado_version $act_version $exp_version_file"
   extract_vivado_version "$act_version"
   local act_basever="$EXTRACTED_VIVADO_BASEVER"
   local act_patches="$EXTRACTED_VIVADO_PATCHES"
   local act_osbits="$EXTRACTED_VIVADO_OSBITS"
   local act_patches_num="$EXTRACTED_VIVADO_PATCHES_NUM"
   local ver_matches=0
   
   while read line; do
      extract_vivado_version "$line"
      local exp_basever="$EXTRACTED_VIVADO_BASEVER"
      local exp_patches="$EXTRACTED_VIVADO_PATCHES"
      local exp_osbits="$EXTRACTED_VIVADO_OSBITS"
      local exp_patches_num="$EXTRACTED_VIVADO_PATCHES_NUM"

      local basever_matches=0
      local osbits_matches=0
      local patches_matches=0
      local patches_match=0

      if [ "$exp_basever" == "$act_basever" ]; then
         basever_match=1
      fi

      if [ "$exp_osbits" == "$act_osbits" ]; then
         osbits_matches=1
      fi

      for act_patch in $act_patches; do
         for exp_patch in $exp_patches; do
            if [ "$exp_patch" == "$act_patch" ]; then
               ((patches_match=patches_match+1))
            fi
         done
      done

      if [ $compare -eq 0 ]; then
         patches_num=$exp_patches_num
      else
         patches_num=$act_patches_num
      fi

      if [[ $basever_match -eq 1 && $osbits_matches -eq 1 ]]; then
         if [ $patches_num -gt 0 ]; then
            if [ $patches_match -eq $patches_num ]; then
               ver_matches=1
            fi
         else
            ver_matches=1
         fi
      fi
      #echo "basever_match   = $basever_match"
      #echo "ver_matches     = $ver_matches"
      #echo "patches_match   = $patches_match"
      #echo "act_patches_num = $act_patches_num"
      #echo "exp_patches_num = $exp_patches_num"

      if [ $ver_matches -eq 1 ]; then
         break
      fi
   done < $exp_version_file

   VIVADO_VERSION_CHECK=$ver_matches

} # check_vivado_version

function extract_vivado_version () {
   local version=$1; shift

   #echo "----------------------------------------------------------------"
   #echo "extract_vivado_version -> $version"

   local tmp_var=()
   for i in `echo $version`; do
      tmp_var+=($i)
   done

   local vivado_version_arr=();
   for i in `echo ${tmp_var[1]} | tr "_" " "`; do
      vivado_version_arr+=($i)
   done

   EXTRACTED_VIVADO_BASEVER=${vivado_version_arr[0]}
   EXTRACTED_VIVADO_PATCHES=${vivado_version_arr[@]:1}
   EXTRACTED_VIVADO_PATCHES_NUM=1
   if [ -z $EXTRACTED_VIVADO_PATCHES ]; then
      EXTRACTED_VIVADO_PATCHES_NUM=0
   else
      EXTRACTED_VIVADO_PATCHES_NUM=${#vivado_version_arr[@]:1}
      ((EXTRACTED_VIVADO_PATCHES_NUM-=1))
   fi
   EXTRACTED_VIVADO_OSBITS=${tmp_var[3]}

   #echo EXTRACTED_VIVADO_BASEVER=$EXTRACTED_VIVADO_BASEVER
   #echo EXTRACTED_VIVADO_PATCHES=$EXTRACTED_VIVADO_PATCHES

} # extract_vivado_version

function allow_non_root {
       [ ! -z ${AWS_FPGA_ALLOW_NON_ROOT} ]
}

