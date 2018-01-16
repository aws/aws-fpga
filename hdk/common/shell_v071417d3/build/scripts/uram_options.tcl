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

##################################################
### URAM options - 2017.1 sdx
##################################################
switch $uram_option {
    "2" {
        set synth_uram_option "-max_uram_cascade_height 2"
        set uramHeight 2
    }
    "3" {
        set synth_uram_option "-max_uram_cascade_height 3"
        set uramHeight 3
    }
    "4" {
        set synth_uram_option "-max_uram_cascade_height 1"
        set uramHeight 4
    }
    default {
        set synth_uram_option "-max_uram_cascade_height 1"
        set uramHeight 4
    }
}