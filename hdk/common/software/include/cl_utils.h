// Amazon FPGA Hardware Development Kit
//
// Copyright 2016 Amazon.com, Inc. or its affiliates. All Rights Reserved.
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


void sv_printf(char *msg);
void sv_map_host_memory(uint8_t *memory);

void cl_peek(uint64_t addr, uint32_t *data);
void cl_poke(uint64_t addr, uint32_t  data);
void sv_pause(uint32_t x);

void test_main(uint32_t *exit_code);
