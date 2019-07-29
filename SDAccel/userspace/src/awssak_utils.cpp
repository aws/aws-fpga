/**
 * Copyright (C) 2017-2018 Xilinx, Inc
 * Author: Umang Parekh, Ryan Radjabi
 * Common AWSSAK Util functions
 *
 * Licensed under the Apache License, Version 2.0 (the "License"). You may
 * not use this file except in compliance with the License. A copy of the
 * License is located at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS, WITHOUT
 * WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the
 * License for the specific language governing permissions and limitations
 * under the License.
 */

#include "awssak_utils.h"

#define BIT(x) (0x1 << x)

std::string parseCUStatus(unsigned val)  {
    char delim = '(';
    std::string status;
    if (val & 0x1) {
    status += delim;
    status += "START";
    delim = '|';
    }
    if (val & 0x2) {
    status += delim;
    status += "DONE";
    delim = '|';
    }
    if (val & 0x4) {
    status += delim;
    status += "IDLE";
    delim = '|';
    }
    if (val & 0x8) {
    status += delim;
    status += "READY";
    delim = '|';
    }
    if (val & 0x10) {
    status += delim;
    status += "RESTART";
    delim = '|';
    }
    if (status.size())
    status += ')';
    else if (val == 0x0)
    status = "(--)";
    else
    status = "(UNKNOWN)";
    return status;
}

std::string parseFirewallStatus(unsigned val)  {
    char delim = '(';
    std::string status;
    // Read channel error
    if (val & BIT(0)) {
    status += delim;
    status += "READ_RESPONSE_BUSY";
    delim = '|';
    }
    if (val & BIT(1)) {
    status += delim;
    status += "RECS_ARREADY_MAX_WAIT";
    delim = '|';
    }
    if (val & BIT(2)) {
    status += delim;
    status += "RECS_CONTINUOUS_RTRANSFERS_MAX_WAIT";
    delim = '|';
    }
    if (val & BIT(3)) {
    status += delim;
    status += "ERRS_RDATA_NUM";
    delim = '|';
    }
    if (val & BIT(4)) {
    status += delim;
    status += "ERRS_RID";
    delim = '|';
    }
    // Write channel error
    if (val & BIT(16)) {
    status += delim;
    status += "WRITE_RESPONSE_BUSY";
    delim = '|';
    }
    if (val & BIT(17)) {
    status += delim;
    status += "RECS_AWREADY_MAX_WAIT";
    delim = '|';
    }
    if (val & BIT(18)) {
    status += delim;
    status += "RECS_WREADY_MAX_WAIT";
    delim = '|';
    }
    if (val & BIT(19)) {
    status += delim;
    status += "RECS_WRITE_TO_BVALID_MAX_WAIT";
    delim = '|';
    }
    if (val & BIT(20)) {
    status += delim;
    status += "ERRS_BRESP";
    delim = '|';
    }
    if (status.size())
    status += ')';
    else if (val == 0x0)
    status = "(GOOD)";
    else
    status = "(UNKNOWN)";
    return status;
}

