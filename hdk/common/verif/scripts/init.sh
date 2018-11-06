#!/bin/bash

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

if [[ ":$HDK_COMMON_DIR" == ":" ]]; then
  echo "error: HDK_COMMON_DIR not set. Source hdk_setup.sh first."
  exit 2
fi

if [[ ":$VIVADO_VER" == ":" ]]; then
  echo "error: VIVADO_VER not set. Source hdk_setup.sh first."
  exit 2
fi

models_dir=$1
if [[ ":$models_dir" == ":" ]]; then
  models_dir=$HDK_COMMON_DIR/verif/models
fi

if [ ! -e $models_dir ]; then
  mkdir -p $models_dir
fi

lockfile_filename=$models_dir/build.lock

# Prevent multiple users from building in the same directory.
# Set the number of retries to 0 so that we will just fail
# and let the other process complete the build.
if [ -e /bin/lockfile ]; then
  if ! lockfile -r 0 $lockfile_filename; then
    echo "error: $lockfile_filename exists"
    echo "error: Another process is already building the models."
    exit 2
  fi
fi

echo "$VIVADO_VER" > $models_dir/.vivado_version

if ! vivado -mode batch -source $HDK_COMMON_DIR/verif/scripts/init.tcl; then
  rm -f $lockfile_filename
  exit 2
fi

ddr4_imports_dir=tmp/tmp_ddr_ex/ddr4_core_ex/imports
ddr4_model_dir=$models_dir/ddr4_model
ddr4_rdimm_model_dir=$models_dir/ddr4_rdimm_wrapper
if [ ! -d $ddr4_model_dir ]; then mkdir -p $ddr4_model_dir; fi
if [ ! -d $ddr4_rdimm_model_dir ]; then mkdir -p $ddr4_rdimm_model_dir; fi
echo "Copying files to $ddr4_model_dir"
cp $ddr4_imports_dir/arch_defines.v              $ddr4_model_dir/
cp $ddr4_imports_dir/arch_package.sv              $ddr4_model_dir/
cp $ddr4_imports_dir/ddr4_model.sv               $ddr4_model_dir/
cp $ddr4_imports_dir/ddr4_sdram_model_wrapper.sv $ddr4_model_dir/
#cp $ddr4_imports_dir/dimm_interface.sv           $ddr4_model_dir/
#cp $ddr4_imports_dir/dimm_subtest.vh             $ddr4_model_dir/
#cp $ddr4_imports_dir/dimm.vh                     $ddr4_model_dir/
cp $ddr4_imports_dir/interface.sv                $ddr4_model_dir/
cp $ddr4_imports_dir/MemoryArray.sv              $ddr4_model_dir/
cp $ddr4_imports_dir/proj_package.sv             $ddr4_model_dir/
cp $ddr4_imports_dir/StateTableCore.sv           $ddr4_model_dir/
cp $ddr4_imports_dir/StateTable.sv               $ddr4_model_dir/
#cp $ddr4_imports_dir/subtest.vh                  $ddr4_model_dir/
cp $ddr4_imports_dir/timing_tasks.sv             $ddr4_model_dir/

echo "Copying files to $ddr4_rdimm_model_dir"
cp $ddr4_imports_dir/ddr4_bi_delay.sv            $ddr4_rdimm_model_dir/
cp $ddr4_imports_dir/ddr4_db_delay_model.sv      $ddr4_rdimm_model_dir/
cp $ddr4_imports_dir/ddr4_db_dly_dir.sv          $ddr4_rdimm_model_dir/
cp $ddr4_imports_dir/ddr4_dimm.sv                $ddr4_rdimm_model_dir/
cp $ddr4_imports_dir/ddr4_dir_detect.sv          $ddr4_rdimm_model_dir/
cp $ddr4_imports_dir/ddr4_rank.sv                $ddr4_rdimm_model_dir/
cp $ddr4_imports_dir/ddr4_rcd_model.sv           $ddr4_rdimm_model_dir/
cp $ddr4_imports_dir/ddr4_rdimm_wrapper.sv       $ddr4_rdimm_model_dir/


echo "patching ddr4_rdimm_wrapper.sv file"
sed -i s/_4G/_8G/g  $ddr4_rdimm_model_dir/ddr4_rdimm_wrapper.sv
sed -i -e 's/\/\/\LRDIMM/\: LRDIMM/g' $ddr4_rdimm_model_dir/ddr4_rdimm_wrapper.sv
sed -i -e 's/\/\/\!LRDIMM/\: NOT_LRDIMM/g' $ddr4_rdimm_model_dir/ddr4_rdimm_wrapper.sv

echo "patching ddr4_sdram_model_wrapper.sv file"
sed -i '/`include "arch_package.sv"/d' $ddr4_model_dir/ddr4_sdram_model_wrapper.sv
sed -i '/`include "proj_package.sv"/d' $ddr4_model_dir/ddr4_sdram_model_wrapper.sv
sed -i '/`include "interface.sv"/d' $ddr4_model_dir/ddr4_sdram_model_wrapper.sv
sed -i '/`include "ddr4_model.sv"/d' $ddr4_model_dir/ddr4_sdram_model_wrapper.sv

echo "\`include \"arch_package.sv\"" >> $ddr4_model_dir/ddr4_sdram_model_wrapper.sv
echo "\`include \"proj_package.sv\"" >> $ddr4_model_dir/ddr4_sdram_model_wrapper.sv
echo "\`include \"interface.sv\"" >> $ddr4_model_dir/ddr4_sdram_model_wrapper.sv
echo "\`include \"ddr4_model.sv\"" >> $ddr4_model_dir/ddr4_sdram_model_wrapper.sv

echo "patching interface.sv file"
sed -i '/`include "ddr4_sdram_model_wrapper.sv"/d' $ddr4_model_dir/interface.sv
sed -i '2i`ifndef DDR4_INT_DEF' $ddr4_model_dir/interface.sv
sed -i '3i  `define DDR4_INT_DEF' $ddr4_model_dir/interface.sv
sed -i '$a`endif' $ddr4_model_dir/interface.sv

echo "patching proj_package.sv file"
sed -i '/`include "ddr4_sdram_model_wrapper.sv"/d' $ddr4_model_dir/proj_package.sv
sed -i '2i`ifndef DDR4_PROJ_PKG' $ddr4_model_dir/proj_package.sv
sed -i '3i  `define DDR4_PROJ_PKG' $ddr4_model_dir/proj_package.sv
sed -i '$a`endif' $ddr4_model_dir/proj_package.sv

echo "patching ddr4_model.sv file"
sed -i '1i`ifndef DDR4_MODEL_DEF' $ddr4_model_dir/ddr4_model.sv
sed -i '2i `define DDR4_MODEL_DEF' $ddr4_model_dir/ddr4_model.sv
sed -i '$a`endif' $ddr4_model_dir/ddr4_model.sv

rm -f $lockfile_filename
