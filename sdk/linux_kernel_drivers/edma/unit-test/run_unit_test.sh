#!/bin/bash

readonly test_filename=mt_read_write.c

usage="
Usage:
------
$(basename "$0") -- a script to compile and run multithreaded tests on the below sizes and max chunk size"

data_size=(0x1000 0x5000 0x10000 0x100000)
max_chnuk=(0x10 0x100 0x500 0x2000) 

for ((i=0;i<${#data_size[@]};i++))
do
	for ((j=0;j<${#max_chnuk[@]};j++))
	do
		#first build the test
		gcc $test_filename -DSIZE_OF_DATA=${data_size[$i]} -DCHUNK_SIZE=${max_chnuk[$j]} -lpthread -o test_data-${data_size[$i]}_chunk-${max_chnuk[$j]}_mt

		#clear dmesh		
		dmesg -C
		
		#run test and fump dmesg
		./test_data-${data_size[$i]}_chunk-${max_chnuk[$j]}_mt > test_data-${data_size[$i]}_chunk-${max_chnuk[$j]}_mt.log
		
		if [ $? -eq 0 ]
		then
			mv test_data-${data_size[$i]}_chunk-${max_chnuk[$j]}_mt.log test_data-${data_size[$i]}_chunk-${max_chnuk[$j]}_mt.log.PASS
		else
			mv test_data-${data_size[$i]}_chunk-${max_chnuk[$j]}_mt.log test_data-${data_size[$i]}_chunk-${max_chnuk[$j]}_mt.log.FAIL
		fi			
		
		dmesg > test_data-${data_size[$i]}_chunk-${max_chnuk[$j]}_mt.log.dmesg
	done
    
done

wait
