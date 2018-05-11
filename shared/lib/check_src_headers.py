#!/usr/bin/env python

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

import argparse
import logging
import re
import sys
import os
import traceback

from fileprovider import FileProvider
try:
    import aws_fpga_test_utils
    from aws_fpga_test_utils.AwsFpgaTestBase import AwsFpgaTestBase
    import aws_fpga_utils
except ImportError as e:
    traceback.print_tb(sys.exc_info()[2])
    print "error: {}\nMake sure to source shared/tests/bin/setup_test_env.sh".format(sys.exc_info()[1])
    sys.exit(1)

logger = aws_fpga_utils.get_logger(__name__)

description = '''This script checks all files within the repository for license headers.
It lists out all files that don't comply and exits with an error code 2.
'''

asl_header1 = '''Amazon FPGA Hardware Development Kit

Copyright 2016 Amazon.com, Inc. or its affiliates. All Rights Reserved.

Licensed under the Amazon Software License (the "License"). You may not use
this file except in compliance with the License. A copy of the License is
located at

   http://aws.amazon.com/asl/

or in the "license" file accompanying this file. This file is distributed on
an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, express or
implied. See the License for the specific language governing permissions and
limitations under the License.
'''

asl_header2 = '''Amazon FPGA Hardware Development Kit

Copyright 2016-2018 Amazon.com, Inc. or its affiliates. All Rights Reserved.

Licensed under the Amazon Software License (the "License"). You may not use
this file except in compliance with the License. A copy of the License is
located at

   http://aws.amazon.com/asl/

or in the "license" file accompanying this file. This file is distributed on
an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, express or
implied. See the License for the specific language governing permissions and
limitations under the License.
'''

apache_header_2016 = '''Copyright 2015-2016 Amazon.com, Inc. or its affiliates. All Rights Reserved.

Licensed under the Apache License, Version 2.0 (the "License"). You may
not use this file except in compliance with the License. A copy of the
License is located at

    http://aws.amazon.com/apache2.0/

or in the "license" file accompanying this file. This file is distributed
on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
express or implied. See the License for the specific language governing
permissions and limitations under the License.
 '''

apache_header_2017 = '''Copyright 2015-2017 Amazon.com, Inc. or its affiliates. All Rights Reserved.

Licensed under the Apache License, Version 2.0 (the "License"). You may
not use this file except in compliance with the License. A copy of the
License is located at

    http://aws.amazon.com/apache2.0/

or in the "license" file accompanying this file. This file is distributed
on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
express or implied. See the License for the specific language governing
permissions and limitations under the License.
 '''

gpl2_header = '''Copyright 2015 Amazon.com, Inc. or its affiliates.

This software is available to you under a choice of one of two
licenses.  You may choose to be licensed under the terms of the GNU
General Public License (GPL) Version 2, available from the file
COPYING in the main directory of this source tree, or the
BSD license below:

    Redistribution and use in source and binary forms, with or
    without modification, are permitted provided that the following
    conditions are met:

     - Redistributions of source code must retain the above
       copyright notice, this list of conditions and the following
       disclaimer.

     - Redistributions in binary form must reproduce the above
       copyright notice, this list of conditions and the following
       disclaimer in the documentation and/or other materials
       provided with the distribution.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS
BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN
ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
'''

xilinx_xdma1 = '''Xilinx XDMA IP Core Linux Driver
Copyright(c) 2015 - 2017 Xilinx, Inc.

This program is free software; you can redistribute it and/or modify it
under the terms and conditions of the GNU General Public License,
version 2, as published by the Free Software Foundation.

This program is distributed in the hope it will be useful, but WITHOUT
ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
more details.

You should have received a copy of the GNU General Public License along
with this program.  If not, see <http://www.gnu.org/licenses/>.

The full GNU General Public License is included in this distribution in
the file called "LICENSE".
'''

xilinx_xdma2 = '''Xilinx XDMA IP Core Linux Driver

Copyright(c) Sidebranch.
Copyright(c) Xilinx, Inc.
'''

xilinx1 = '''\xa9 Copyright 2017 Xilinx, Inc. All rights reserved.

This file contains confidential and proprietary information of Xilinx, Inc. and is protected under U.S. and
international copyright and other intellectual property laws.

DISCLAIMER
This disclaimer is not a license and does not grant any rights to the materials distributed herewith.
Except as otherwise provided in a valid license issued to you by Xilinx, and to the maximum extent
permitted by applicable law: (1) THESE MATERIALS ARE MADE AVAILABLE "AS IS" AND WITH ALL
FAULTS, AND XILINX HEREBY DISCLAIMS ALL WARRANTIES AND CONDITIONS, EXPRESS, IMPLIED, OR
STATUTORY, INCLUDING BUT NOT LIMITED TO WARRANTIES OF MERCHANTABILITY, NONINFRINGEMENT,
OR FITNESS FOR ANY PARTICULAR PURPOSE; and (2) Xilinx shall not be liable (whether
in contract or tort, including negligence, or under any other theory of liability) for any loss or damage of
any kind or nature related to, arising under or in connection with these materials, including for any
direct, or any indirect, special, incidental, or consequential loss or damage (including loss of data,
profits, goodwill, or any type of loss or damage suffered as a result of any action brought by a third
party) even if such damage or loss was reasonably foreseeable or Xilinx had been advised of the
possibility of the same.

CRITICAL APPLICATIONS
Xilinx products are not designed or intended to be fail-safe, or for use in any application requiring failsafe
performance, such as life-support or safety devices or systems, Class III medical devices, nuclear
facilities, applications related to the deployment of airbags, or any other applications that could lead to
death, personal injury, or severe property or environmental damage (individually and collectively,
"Critical Applications"). Customer assumes the sole risk and liability of any use of Xilinx products in
Critical Applications, subject only to applicable laws and regulations governing limitations on product
liability.

THIS COPYRIGHT NOTICE AND DISCLAIMER MUST BE RETAINED AS PART OF THIS FILE AT ALL TIMES.
'''

xilinx2_header = '''(c) Copyright 2017 Xilinx, Inc. All rights reserved.

This file contains confidential and proprietary information
of Xilinx, Inc. and is protected under U.S. and
international copyright and other intellectual property
laws.

DISCLAIMER
This disclaimer is not a license and does not grant any
rights to the materials distributed herewith. Except as
otherwise provided in a valid license issued to you by
Xilinx, and to the maximum extent permitted by applicable
law: (1) THESE MATERIALS ARE MADE AVAILABLE "AS IS" AND
WITH ALL FAULTS, AND XILINX HEREBY DISCLAIMS ALL WARRANTIES
AND CONDITIONS, EXPRESS, IMPLIED, OR STATUTORY, INCLUDING
BUT NOT LIMITED TO WARRANTIES OF MERCHANTABILITY, NON-
INFRINGEMENT, OR FITNESS FOR ANY PARTICULAR PURPOSE; and
(2) Xilinx shall not be liable (whether in contract or tort,
including negligence, or under any other theory of
liability) for any loss or damage of any kind or nature
related to, arising under or in connection with these
materials, including for any direct, or any indirect,
special, incidental, or consequential loss or damage
(including loss of data, profits, goodwill, or any type of
loss or damage suffered as a result of any action brought
by a third party) even if such damage or loss was
reasonably foreseeable or Xilinx had been advised of the
possibility of the same.

CRITICAL APPLICATIONS
Xilinx products are not designed or intended to be fail-
safe, or for use in any application requiring fail-safe
performance, such as life-support or safety devices or
systems, Class III medical devices, nuclear facilities,
applications related to the deployment of airbags, or any
other applications that could lead to death, personal
injury, or severe property or environmental damage
(individually and collectively, "Critical
Applications"). Customer assumes the sole risk and
liability of any use of Xilinx products in Critical
Applications, subject only to applicable laws and
regulations governing limitations on product liability.

THIS COPYRIGHT NOTICE AND DISCLAIMER MUST BE RETAINED AS
PART OF THIS FILE AT ALL TIMES.

DO NOT MODIFY THIS FILE.
'''

xilinx3_header = '''(c) Copyright 2011-2012 Xilinx, Inc. All rights reserved.

This file contains confidential and proprietary information
of Xilinx, Inc. and is protected under U.S. and
international copyright and other intellectual property
laws.

DISCLAIMER
This disclaimer is not a license and does not grant any
rights to the materials distributed herewith. Except as
otherwise provided in a valid license issued to you by
Xilinx, and to the maximum extent permitted by applicable
law: (1) THESE MATERIALS ARE MADE AVAILABLE "AS IS" AND
WITH ALL FAULTS, AND XILINX HEREBY DISCLAIMS ALL WARRANTIES
AND CONDITIONS, EXPRESS, IMPLIED, OR STATUTORY, INCLUDING
BUT NOT LIMITED TO WARRANTIES OF MERCHANTABILITY, NON-
INFRINGEMENT, OR FITNESS FOR ANY PARTICULAR PURPOSE; and
(2) Xilinx shall not be liable (whether in contract or tort,
including negligence, or under any other theory of
liability) for any loss or damage of any kind or nature
related to, arising under or in connection with these
materials, including for any direct, or any indirect,
special, incidental, or consequential loss or damage
(including loss of data, profits, goodwill, or any type of
loss or damage suffered as a result of any action brought
by a third party) even if such damage or loss was
reasonably foreseeable or Xilinx had been advised of the
possibility of the same.

CRITICAL APPLICATIONS
Xilinx products are not designed or intended to be fail-
safe, or for use in any application requiring fail-safe
performance, such as life-support or safety devices or
systems, Class III medical devices, nuclear facilities,
applications related to the deployment of airbags, or any
other applications that could lead to death, personal
injury, or severe property or environmental damage
(individually and collectively, "Critical
Applications"). Customer assumes the sole risk and
liability of any use of Xilinx products in Critical
Applications, subject only to applicable laws and
regulations governing limitations on product liability.
'''

xilinx4_header = '''Xilinx SDAccel HAL userspace driver extension APIs
Performance Monitoring Exposed Parameters
Copyright (C) 2015-2017, Xilinx Inc - All rights reserved

Licensed under the Apache License, Version 2.0 (the "License"). You may
not use this file except in compliance with the License. A copy of the
License is located at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS, WITHOUT
WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the
License for the specific language governing permissions and limitations
under the License.
'''

xilinx5_header = '''Xilinx SDAccel xclbin container definition
Copyright (C) 2015-2017, Xilinx Inc - All rights reserved
'''

xilinx6_header = '''Xilinx SDAccel HAL userspace driver APIs
Copyright (C) 2015-2017, Xilinx Inc - All rights reserved

Licensed under the Apache License, Version 2.0 (the "License"). You may
not use this file except in compliance with the License. A copy of the
License is located at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS, WITHOUT
WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the
License for the specific language governing permissions and limitations
under the License.
'''

xilinx7_header = '''Xilinx SDAccel HAL userspace driver extension APIs
Performance Monitoring Exposed Parameters
Copyright (C) 2015-2016, Xilinx Inc - All rights reserved

Licensed under the Apache License, Version 2.0 (the "License"). You may
not use this file except in compliance with the License. A copy of the
License is located at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS, WITHOUT
WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the
License for the specific language governing permissions and limitations
under the License.
'''

xilinx8_header = '''Copyright (C) 2018 Xilinx, Inc
'''

xilinx9_header = '''Copyright (C) 2015-2018 Xilinx, Inc
'''

xilinx10_header = '''Copyright (C) 2016-2018 Xilinx, Inc
'''

xilinx11_header = '''Copyright (C) 2017-2018 Xilinx, Inc
'''

all_exp_header_lines = [
    asl_header1.split("\n"),
    asl_header2.split("\n"),
    apache_header_2016.split("\n"),
    apache_header_2017.split("\n"),
    gpl2_header.split("\n"),
    xilinx_xdma1.split("\n"),
    xilinx_xdma2.split("\n"),
    xilinx1.split("\n"),
    xilinx2_header.split("\n"),
    xilinx3_header.split("\n"),
    xilinx4_header.split("\n"),
    xilinx5_header.split("\n"),
    xilinx6_header.split("\n"),
    xilinx7_header.split("\n"),
    xilinx8_header.split("\n"),
    xilinx9_header.split("\n"),
    xilinx10_header.split("\n"),
    xilinx11_header.split("\n"),
    ]
min_header_lines = len(min(all_exp_header_lines, key=len))
max_header_lines = len(max(all_exp_header_lines, key=len))
logger.info("max_header_lines={}".format(max_header_lines))

def check_header_lines(prefix, act_lines, exp_lines):
    # Strip off leading spaces and prefix
    prefix_re = re.compile(r' *' + re.escape(prefix) + r' *')

    if len(act_lines) < len(exp_lines):
        return False
    for linenum in range(len(exp_lines) - 1):
        # Strip off leading and trailing spaces from expected line
        exp_line = exp_lines[linenum].rstrip().lstrip()
        # Strip prefix off of actual line, if exists, then strip off leading and trailing spaces
        act_line = prefix_re.sub('', act_lines[linenum], 1).rstrip().lstrip()
        if act_line != exp_line:
#             logger.info("Failed to find header:\nexp: {}\nact: {}\nexp lines:\n{}\nact lines:\n{}".format(
#                exp_line, act_line, "\n".join(exp_lines), "\n".join(act_lines)))
#             logger.info(repr(exp_line))
#             logger.info(repr(act_line))
            return False
    return True

def find_header(file_path):
    '''
    Find header in the first lines of the file.
    If the first line is '#!" then the 2nd line should be blank and the header
    should start on the 3rd line.
    Otherwise the header should be on the first line.

    @returns True if header is found, false otherwise.
    '''
    lines = []
    f = open(file_path, 'r')
    while f and len(lines) < max_header_lines:
        line = f.readline()
        if line == '':
            if len(lines) < min_header_lines:
                logger.error("Less than {} lines in file".format(min_header_lines))
                return False
        lines.append(line.rstrip())
    if re.match(r'#!', lines[0]):
        if lines[1] != '':
            logger.error("Expected blank line after: {}\nact line: {}".format(lines[0], lines[1]))
            return False
        lines = lines[2:]
        lines.append(f.readline().rstrip())
        lines.append(f.readline().rstrip())
    # Get the comment character
    if len(lines[0]) == 0:
        logger.error("Blank line found instead of the start of the header")
        return False
    if lines[0][0] == '#':
        prefix = '#'
    elif len(lines[0]) > 1 and lines[0][0:2] == '/*':
        prefix = ' *'
        lines = lines[1:]
    elif len(lines[0]) > 1 and lines[0][0:2] == '//':
        prefix = '//'
    elif len(lines[0]) > 1 and lines[0][0:2] == '--':
        prefix = '--'
    else:
        logger.error("Line doesn't start with a recognized comment string: {}".format(lines[0]))
        return
    # Allow a leading header line
    if re.match(re.escape(prefix) + "[ -=\*]*$", lines[0]):
        lines = lines[1:]
        lines.append(f.readline().rstrip())
    for exp_header_lines in all_exp_header_lines:
        if check_header_lines(prefix, lines, exp_header_lines):
            return True
    logger.error("Failed to find header in {}:\nprefix={}\nact lines at top of file:\n{}".format(file_path, prefix, "\n".join(lines)))
    return False

def check_headers(dir):

    logger.info("Checking path: " + dir)

    file_provider = FileProvider()
    os.chdir(file_provider.repo_dir)
    file_provider.set_exclude_files([
            ".*\.css$",
            ".*\.csv$",
            ".*\.diff$",
            ".*\.f$",
            ".*\.JPG$",
            ".*\.jpg$",
            ".*\.md$",
            ".*\.patch$",
            ".*\.PNG$",
            ".*\.png$",
            ".*\.pdf$",
            ".*\.pptx$",
            ".*\.txt$",
            ".*\.xdc$",
            ".*\.xlsx$",
            ".*\.xml$",

            ".*\.gitignore$",
            ".*\.gitmodules$",
            ".*Jenkinsfile.*",
            ".*supported_vivado_versions\.txt$",

            "hdk/.*/ccf_ctl\.v$",
            "hdk/.*/design_error\.inc$",
            "hdk/.*/flop_ccf\.sv$",
            "hdk/.*/flop_fifo_2\.sv$",
            "hdk/.*/flop_fifo_lu\.sv$",
            "hdk/.*/flop_fifo\.sv$",
            "hdk/.*/ft_fifo_p2\.v$",
            "hdk/.*/ft_fifo_p\.v$",
            "hdk/.*/ft_fifo\.v$",
            "hdk/.*/gray\.inc$",
            "hdk/.*/lib_pipe\.sv$",
            "hdk/.*/push_2_fifo_double_pop\.sv$",
            "hdk/.*/push_2_fifo_guts\.inc$",
            "hdk/.*/push_2_fifo\.sv$",
            "hdk/.*/ram_2p_bit_en\.v$",
            "hdk/.*/ram_2p_dc\.v$",
            "hdk/.*/ram_2p_syn\.v$",
            "hdk/.*/ram_2p_trial_synth\.v$",
            "hdk/.*/ram_2p\.v$",
            "hdk/.*/rr_arb\.sv$",
            "hdk/.*/sync\.v$",
            "hdk/.*/README$",
            "hdk/.*/hdk_version\.txt$",
            "hdk/.*/dest_register_slice\.v$",
            "hdk/.*/src_register_slice\.v$",
            "hdk/cl/examples/cl_.+/\.critical_warnings",
            "hdk/cl/examples/cl_.+/\.warnings",

            "sdk/linux_kernel_drivers/xdma/10-xdma\.rules",

            "sdk/linux_kernel_drivers/xocl/10-xocl\.rules",
            "sdk/linux_kernel_drivers/xocl/LICENSE$",

            "SDAccel/userspace/src/test",
	    "SDAccel/examples/aws/kernel_3ddr_bandwidth/description.json",
	    "SDAccel/examples/aws/helloworld_ocl_runtime/helloworld",
            "SDAccel/examples/aws/helloworld_ocl_runtime/vector_addition.hw.xilinx_aws-vu9p-f1_dynamic_5_0.awsxclbin"    
        ])

    file_provider.set_exclude_paths([
            "\.git$",

            "hdk/common/shell_.*/design/ip$",
            "hdk/cl/examples/cl_.*/build/checkpoints$",
            "hdk/.+/xsim\.dir$",

            "SDAccel/aws_platform",
            "SDAccel/examples/3rd_party",
            "SDAccel/examples/xilinx",
        ])

    file_path_list = sorted(file_provider.get_files(dir))
    assert file_path_list, "No files found in {}".format(dir)

    logger.info("Checking {} files".format(len(file_path_list)))
    files_with_bad_headers = []
    for file_path in file_path_list:
        if os.path.islink(file_path):
            continue
        logger.debug("Checking {}".format(file_path))
        if not find_header(file_path):
            logger.error("Invalid or missing header in {}".format(file_path))
            files_with_bad_headers.append(file_path)

    rc = 0
    if files_with_bad_headers:
        rc = 1
        logger.error("Following files didn't have the correct header:\n  {}".format(
            "\n  ".join(files_with_bad_headers)))

    logger.info("Checked {} files".format(len(file_path_list)))
    logger.info("{} errors".format(len(files_with_bad_headers)))
    return rc

if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=description, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument('--dir', action='store', required=False, default=os.path.abspath(__file__) + "/../../../" , help='Directory to check for the headers')
    parser.add_argument('--debug', action='store_true', required=False, help='Enable debug messages')

    args = parser.parse_args()

    logging_level = logging.INFO
    if args.debug:
        logger.setLevel(logging.DEBUG)

    sys.exit(check_headers(args.dir))
