#!/usr/bin/bash -ex

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

cd $SDK_DIR/tests
rm -rf fio_dma_tools_original
aws s3 cp s3://aws-fpga-jenkins-testing/fio_dma_tools/ fio_dma_tools_original/ --recursive
cd fio_dma_tools_original
rm -rf xdma_v2017_1/
cd fio
chmod +x configure
./configure
make
mv fio ../scripts
cd ..
rm -rf fio
cd ..
aws s3 rm s3://aws-fpga-jenkins-testing/fio_dma_tools_compiled --recursive
aws s3 cp fio_dma_tools_original/ s3://aws-fpga-jenkins-testing/fio_dma_tools_compiled --recursive
rm -rf fio_dma_tools_original/
