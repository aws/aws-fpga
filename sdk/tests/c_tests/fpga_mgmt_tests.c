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

#include <fpga_pci.h>
#include <fpga_mgmt.h>
#include <utils/lcd.h>

#include "fpga_mgmt_tests.h"

int fpga_mgmt_tests_init(void)
{
	int rc;

    /* initialize the fpga_mgmt library */
    rc = fpga_mgmt_init();
    fail_on(rc, out, "Unable to initialize the fpga_mgmt library");

out:
	return rc;
}

int fpga_mgmt_tests_provide_logger(fpga_mgmt_tests_logger_f log_f, const char* logger_name)
{
	int rc;
	static bool initialized = false;
	static struct logger logger = {0};

	if (initialized) {
		log_error("fpga_mgmt_tests_provide_logger can only be called once");
		return -1;
	}

	logger.name = "python logger";
	logger.log = log_f;

	rc = log_attach(&logger, NULL, 0);
	fail_on(rc, out, "unabled to attach a new logger");

	rc = log_init(logger_name);
	fail_on(rc, out, "unabled initialize logger");

	initialized = true;
out:
	return rc;
}
