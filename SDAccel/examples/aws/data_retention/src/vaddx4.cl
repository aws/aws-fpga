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

__kernel void
vadd0(
     const int length,
     __global int* a,
     __global int* b,
     __global int* c,
     const int mult) {

  c[ get_global_id(0) ] = ( mult * a[ get_global_id(0) ] ) + b[ get_global_id(0) ];
     
  return;
}
__kernel void
vadd1(
     const int length,
     __global int* a,
     __global int* b,
     __global int* c,
     const int mult) {

  c[ get_global_id(0) ] = ( mult * a[ get_global_id(0) ] ) + b[ get_global_id(0) ];
     
  return;
}
__kernel void
vadd2(
     const int length,
     __global int* a,
     __global int* b,
     __global int* c,
     const int mult) {

  c[ get_global_id(0) ] = ( mult * a[ get_global_id(0) ] ) + b[ get_global_id(0) ];
     
  return;
}
__kernel void
vadd3(
     const int length,
     __global int* a,
     __global int* b,
     __global int* c,
     const int mult) {

  c[ get_global_id(0) ] = ( mult * a[ get_global_id(0) ] ) + b[ get_global_id(0) ];
     
  return;
}
