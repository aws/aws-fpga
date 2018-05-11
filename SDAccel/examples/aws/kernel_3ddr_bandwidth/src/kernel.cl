// Amazon FPGA Hardware Development Kit
//
// Copyright 2016-2018 Amazon.com, Inc. or its affiliates. All Rights Reserved.
//
// Licensed under the Amazon Software License (the "License"). You may not use
// this file except in compliance with the License. A copy of the License is
// located at
//
//    http://aws.amazon.com/asl/
//
// or in the "license" file accompanying this file. This file is distributed on
// an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, express or
// implied. See the License for the specific language governing permissions and
// limitations under the License.

kernel __attribute__ ((reqd_work_group_size(1,1,1)))
void bandwidth(__global uint16  * __restrict input0,
               __global uint16  * __restrict output0,
               __global uint16  * __restrict output1,
               ulong num_blocks)
{
    __attribute__((xcl_pipeline_loop))
    for (ulong blockindex=0; blockindex<num_blocks; blockindex++) {
        uint16 temp0 = input0[blockindex];
        output0[blockindex] = temp0;
        output1[blockindex] = temp0;
    }
}
