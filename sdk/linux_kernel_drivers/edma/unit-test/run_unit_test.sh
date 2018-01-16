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

set -ex

readonly test_filename=mt_read_write.c

usage="
Usage:
------
$(basename "$0") -- a script to compile and run multithreaded tests on the below sizes and max chunk size"

data_size=(0x1000 0x5000 0x10000 0x100000)
max_chunk=(0x10 0x100 0x500 0x2000) 

for ((i=0;i<${#data_size[@]};i++))
do
	for ((j=0;j<${#max_chunk[@]};j++))
	do
		#first build the test
		gcc $test_filename -DSIZE_OF_DATA=${data_size[$i]} -DCHUNK_SIZE=${max_chunk[$j]} -lpthread -o test_data-${data_size[$i]}_chunk-${max_chunk[$j]}_mt

		#clear dmesh
		sudo dmesg -C
		
		#run test and fump dmesg
		sudo ./test_data-${data_size[$i]}_chunk-${max_chunk[$j]}_mt > test_data-${data_size[$i]}_chunk-${max_chunk[$j]}_mt.log
		
		if [ $? -eq 0 ]
		then
			mv test_data-${data_size[$i]}_chunk-${max_chunk[$j]}_mt.log test_data-${data_size[$i]}_chunk-${max_chunk[$j]}_mt.log.PASS
		else
			mv test_data-${data_size[$i]}_chunk-${max_chunk[$j]}_mt.log test_data-${data_size[$i]}_chunk-${max_chunk[$j]}_mt.log.FAIL
		fi			
		
		dmesg > test_data-${data_size[$i]}_chunk-${max_chunk[$j]}_mt.log.dmesg
	done
    
done

wait
