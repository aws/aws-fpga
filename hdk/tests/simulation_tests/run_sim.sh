#!/usr/bin/env bash

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

# Exit on any error
set -e
# Process command line args

while [[ $# -gt 1 ]]
do
key="$1"

case $key in
    --test-name)
        test_name="$2"
        shift
        shift
        ;;
    --test-dir)
        test_dir="$2"
        shift
        shift
        ;;
    --simulator)
        simulator="$2"
	shift
	shift
	;;
    --test-type)
        test_type="$2"
        shift
        shift
        ;;
    *)
        echo -e >&2 "ERROR: Invalid option: $1\n"
        exit 1
        ;;
esac
done

# Run the test
pushd $test_dir
case "$simulator" in
	vcs)
	case "$test_type" in
	    sv)
	       make TEST="$test_name" VCS=1
	       ;;
	    sv_fast)
	       make TEST="$test_name" AXI_MEMORY_MODEL=1 VCS=1
	        ;;
	    sv_fast_ecc_direct)
	       make TEST="$test_name" AXI_MEMORY_MODEL=1 ECC_DIRECT=1 ECC_ADDR_HI=1000 ECC_ADDR_LO=0 VCS=1
	        ;;
	    sv_fast_ecc_rnd)
	       make TEST="$test_name" AXI_MEMORY_MODEL=1 ECC_RAND=1 RND_ECC_WEIGHT=100 VCS=1
	        ;;
	    sv_fast_ecc_rnd_100)
	       make TEST="$test_name" AXI_MEMORY_MODEL=1 ECC_RAND=1 RND_ECC_WEIGHT=100 VCS=1
	        ;;
	    sv_fast_ecc_rnd_50)
	       make TEST="$test_name" AXI_MEMORY_MODEL=1 ECC_RAND=1 RND_ECC_WEIGHT=50 VCS=1
	        ;;
	    sv_fast_ecc_rnd_10)
	       make TEST="$test_name" AXI_MEMORY_MODEL=1 ECC_RAND=1 RND_ECC_WEIGHT=10 VCS=1
	        ;;
	    sv_fast_ecc_rnd_0)
	       make TEST="$test_name" AXI_MEMORY_MODEL=1 ECC_RAND=1 RND_ECC_WEIGHT=0 VCS=1
	        ;;
	    sv_ddr_bkdr)
	       make TEST="$test_name" DDR_BKDR=1 VCS=1
	        ;;
	    vhdl)
	       make TEST="$test_name" VCS=1
	        ;;
	    c)
	       make C_TEST="$test_name" VCS=1
	        ;;
	    *)
	        echo -e >&2 "ERROR: Invalid option: $1\n"
	        exit 1
	        ;;
	esac
	;;
	ies)
	case "$test_type" in
	    sv)
	       make TEST="$test_name" IES=1
	       ;;
	    sv_fast)
	       make TEST="$test_name" AXI_MEMORY_MODEL=1 IES=1
	        ;;
	    sv_fast_ecc_direct)
	       make TEST="$test_name" AXI_MEMORY_MODEL=1 ECC_DIRECT=1 ECC_ADDR_HI=1000 ECC_ADDR_LO=0 IES=1
	        ;;
	    sv_fast_ecc_rnd)
	       make TEST="$test_name" AXI_MEMORY_MODEL=1 ECC_RAND=1 RND_ECC_WEIGHT=100 IES=1
	        ;;
	    sv_fast_ecc_rnd_100)
	       make TEST="$test_name" AXI_MEMORY_MODEL=1 ECC_RAND=1 RND_ECC_WEIGHT=100 IES=1
	        ;;
	    sv_fast_ecc_rnd_50)
	       make TEST="$test_name" AXI_MEMORY_MODEL=1 ECC_RAND=1 RND_ECC_WEIGHT=50 IES=1
	        ;;
	    sv_fast_ecc_rnd_10)
	       make TEST="$test_name" AXI_MEMORY_MODEL=1 ECC_RAND=1 RND_ECC_WEIGHT=10 IES=1
	        ;;
	    sv_fast_ecc_rnd_0)
	       make TEST="$test_name" AXI_MEMORY_MODEL=1 ECC_RAND=1 RND_ECC_WEIGHT=0 IES=1
	        ;;
	    sv_ddr_bkdr)
	       make TEST="$test_name" DDR_BKDR=1 IES=1
	        ;;
	    vhdl)
	       make TEST="$test_name" IES=1
	        ;;
	    c)
	       make C_TEST="$test_name" IES=1
	        ;;
	    *)
	        echo -e >&2 "ERROR: Invalid option: $1\n"
	        exit 1
	        ;;
	esac
	;;
	questa)
	case "$test_type" in
	    sv)
	       make TEST="$test_name" QUESTA=1
	       ;;
	    sv_fast)
	       make TEST="$test_name" AXI_MEMORY_MODEL=1 QUESTA=1
	        ;;
	    sv_fast_ecc_direct)
	       make TEST="$test_name" AXI_MEMORY_MODEL=1 ECC_DIRECT=1 ECC_ADDR_HI=1000 ECC_ADDR_LO=0 QUESTA=1
	        ;;
	    sv_fast_ecc_rnd)
	       make TEST="$test_name" AXI_MEMORY_MODEL=1 ECC_RAND=1 RND_ECC_WEIGHT=100 QUESTA=1
	        ;;
	    sv_fast_ecc_rnd_100)
	       make TEST="$test_name" AXI_MEMORY_MODEL=1 ECC_RAND=1 RND_ECC_WEIGHT=100 QUESTA=1
	        ;;
	    sv_fast_ecc_rnd_50)
	       make TEST="$test_name" AXI_MEMORY_MODEL=1 ECC_RAND=1 RND_ECC_WEIGHT=50 QUESTA=1
	        ;;
	    sv_fast_ecc_rnd_10)
	       make TEST="$test_name" AXI_MEMORY_MODEL=1 ECC_RAND=1 RND_ECC_WEIGHT=10 QUESTA=1
	        ;;
	    sv_fast_ecc_rnd_0)
	       make TEST="$test_name" AXI_MEMORY_MODEL=1 ECC_RAND=1 RND_ECC_WEIGHT=0 QUESTA=1
	        ;;
	    sv_ddr_bkdr)
	       make TEST="$test_name" DDR_BKDR=1 QUESTA=1
	        ;;
	    vhdl)
	       make TEST="$test_name" QUESTA=1
	        ;;
	    c)
	       make C_TEST="$test_name" QUESTA=1
	        ;;
	    *)
	        echo -e >&2 "ERROR: Invalid option: $1\n"
	        exit 1
	        ;;
	esac
	;;
	*)
	case "$test_type" in
	    sv)
	       make TEST="$test_name"
	       ;;
	    sv_fast)
	       make TEST="$test_name" AXI_MEMORY_MODEL=1
	        ;;
	    sv_fast_ecc_direct)
	       make TEST="$test_name" AXI_MEMORY_MODEL=1 ECC_DIRECT=1 ECC_ADDR_HI=1000 ECC_ADDR_LO=0
	        ;;
	    sv_fast_ecc_rnd)
	       make TEST="$test_name" AXI_MEMORY_MODEL=1 ECC_RAND=1 RND_ECC_WEIGHT=100
	        ;;
	    sv_fast_ecc_rnd_100)
	       make TEST="$test_name" AXI_MEMORY_MODEL=1 ECC_RAND=1 RND_ECC_WEIGHT=100
	        ;;
	    sv_fast_ecc_rnd_50)
	       make TEST="$test_name" AXI_MEMORY_MODEL=1 ECC_RAND=1 RND_ECC_WEIGHT=50
	        ;;
	    sv_fast_ecc_rnd_10)
	       make TEST="$test_name" AXI_MEMORY_MODEL=1 ECC_RAND=1 RND_ECC_WEIGHT=10
	        ;;
	    sv_fast_ecc_rnd_0)
	       make TEST="$test_name" AXI_MEMORY_MODEL=1 ECC_RAND=1 RND_ECC_WEIGHT=0
	        ;;
	    sv_ddr_bkdr)
	       make TEST="$test_name" DDR_BKDR=1
	        ;;
	    vhdl)
	       make TEST="$test_name"
	        ;;
	    c)
	       make C_TEST="$test_name"
	        ;;
	    *)
	        echo -e >&2 "ERROR: Invalid option: $1\n"
	        exit 1
	        ;;
	esac
	;;
esac
# Exit out of the test dir
popd
