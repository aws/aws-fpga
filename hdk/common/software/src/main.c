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

#include <stdio.h>
#include <stdlib.h>

#include "pcie_utils.h"
#include "cl_utils.h"

bool verbose = false;

int
main(int argc, char **argv)
{
  int exit_code;

  if (!pcie_connect(&argc, &argv)) {
    printf("Error: pcie_connect failed, Please specify slot\n");
    return -1;
  }

  test_main(&exit_code);

  return exit_code;
}
