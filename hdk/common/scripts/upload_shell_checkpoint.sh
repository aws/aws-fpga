#!/bin/bash

hdk_shell_version=$1
if [[ ":$hdk_shell_version" == ":" ]]; then
  echo "error: You must specify the HDK shell version to use."
  exit 2
fi

if [[ ":$HDK_COMMON_DIR" == ":" ]]; then
  echo "error: HDK_COMMON_DIR is not set. Run hdk_setup.sh"
  exit 2
fi

hdk_shell_dir=$HDK_COMMON_DIR/$hdk_shell_version
if [ ! -d $hdk_shell_dir ]; then
  echo "error: Shell dir doesn't exist: $hdk_shell_dir"
  echo "error: Invalid shell version: $hdk_shell_version"
  exit 2
fi

hdk_shell=$hdk_shell_dir/build/checkpoints/from_aws/SH_CL_BB_routed.dcp
if [ ! -e $hdk_shell ]; then
  echo "error: Shell checkpoint doesn't exist: $hdk_shell"
  exit 2
fi

echo "HDK shell checkpoint: $hdk_shell"

act_sha1=$( sha1sum $hdk_shell | awk '{ print $1 }' )
echo $act_sha1 > $hdk_shell.sha1
echo "Checkpoint sha1=$act_sha1"

#hdk_shell_s3_bucket=cartalla-f1
hdk_shell_s3_bucket=aws-fpga-hdk-resources
s3_hdk_shell=s3://$hdk_shell_s3_bucket/hdk/$hdk_shell_version/build/checkpoints/from_aws/SH_CL_BB_routed.dcp
echo "Copying shell checkpoint to $s3_hdk_shell"
aws s3 cp $hdk_shell $s3_hdk_shell --acl public-read || { echo "error: Checkpoint upload failed"; exit 2; }
echo "Copying shell checkpoint sha1 to $s3_hdk_shell.sha1"
aws s3 cp $hdk_shell.sha1 $s3_hdk_shell.sha1 --acl public-read || { echo "error: Checkpoint sha1 upload failed"; exit 2; }
