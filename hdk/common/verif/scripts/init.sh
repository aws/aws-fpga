#!/bin/sh

## Amazon FGPA Hardware Development Kit
## 
## Copyright 2016 Amazon.com, Inc. or its affiliates. All Rights Reserved.
## 
## Licensed under the Amazon Software License (the "License"). You may not use
## this file except in compliance with the License. A copy of the License is
## located at
## 
##    http://aws.amazon.com/asl/
## 
## or in the "license" file accompanying this file. This file is distributed on
## an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, express or
## implied. See the License for the specific language governing permissions and
## limitations under the License.

models_dir=$1
if [[ ":$models_dir" == ":" ]]; then
  models_dir=$HDK_COMMON_DIR/verif/models
fi
if [ ! -e $models_dir ]; then
  mkdir -p $models_dir
fi

if ! vivado -mode batch -source $HDK_COMMON_DIR/verif/scripts/init.tcl; then
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

