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

readonly test_filename=perf_test.c
readonly result_filename=perf.log

usage="
Usage:
------
$(basename "$0") -- a script to compile and run performance (i.e. latency and bandwidth) test on the edma and outputs the result to a file."

data_size=(0x100 0x1000 0x5000)
number_of_repetitions=(0x10 0x100 0x200)

rm -f $result_filename

for ((i=0;i<${#data_size[@]};i++))
do
	for ((j=0;j<${#number_of_repetitions[@]};j++))
	do
		#first build the test
		gcc $test_filename -DSIZE_OF_DATA=${data_size[$i]} -DNUMBER_OF_REPETITIONS=${number_of_repetitions[$j]} -o perf_test_read_${data_size[$i]}_${number_of_repetitions[$j]}
		gcc $test_filename -DSIZE_OF_DATA=${data_size[$i]} -DNUMBER_OF_REPETITIONS=${number_of_repetitions[$j]} -DWRITE_PERF=1 -DWRITE_PERF_VERIFY -o perf_test_write_${data_size[$i]}_${number_of_repetitions[$j]}

		#clear dmesh		
		sudo dmesg -C
		
		#run test and fump dmesg
		sudo ./perf_test_read_${data_size[$i]}_${number_of_repetitions[$j]} >> $result_filename
		echo " " >> $result_filename
		sudo ./perf_test_write_${data_size[$i]}_${number_of_repetitions[$j]} >> $result_filename
		echo " " >> $result_filename
						
		dmesg > perf_${data_size[$i]}_${number_of_repetitions[$j]}.dmesg
	done
    
done

wait
