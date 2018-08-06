/*
 * Amazon FPGA Hardware Development Kit
 *
 * Copyright 2016 Amazon.com, Inc. or its affiliates. All Rights Reserved.
 *
 * Licensed under the Amazon Software License (the "License"). You may not use
 * this file except in compliance with the License. A copy of the License is
 * located at
 *
 *    http://aws.amazon.com/asl/
 *
 * or in the "license" file accompanying this file. This file is distributed on
 * an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, express or
 * implied. See the License for the specific language governing permissions and
 * limitations under the License.
 */

#include <stdint.h>

/* general test library functions */
int fpga_mgmt_tests_init(void);
typedef int (*fpga_mgmt_tests_logger_f)(uint32_t log_level, const char* message);
int fpga_mgmt_tests_provide_logger(fpga_mgmt_tests_logger_f log_f, const char* logger_name);

/* test implementations */
int fpga_mgmt_test_readdir(unsigned int num_threads);
