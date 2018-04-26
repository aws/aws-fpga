/*
 * Copyright (C) 2017-2018 Xilinx, Inc
 * Author: Sonal Santan
 * AWS HAL Driver for SDAccel/OpenCL runtime evnrionemnt, for AWS EC2 F1
 *
 * Code copied from SDAccel XDMA based HAL driver
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
//#define INTERNAL_TESTING 1

#include <cstring>

#include "xclbin2.h"

#ifdef INTERNAL_TESTING
#define AFI_ID_STR_MAX 64
#else
#include "hal/fpga_common.h"
#endif

const char *get_afi_from_xclBin(const xclBin *buffer)
{
    const char *afid = reinterpret_cast<const char *>(buffer);
    afid += buffer->m_primaryFirmwareOffset;
    if (buffer->m_primaryFirmwareLength > AFI_ID_STR_MAX)
        return nullptr;
    if (std::memcmp(afid, "afi-", 4) && std::memcmp(afid, "agfi-", 5))
        return nullptr;
    return afid;
}

const char *get_afi_from_axlf(const axlf *buffer)
{
    const axlf_section_header *bit_header = xclbin::get_axlf_section(buffer, BITSTREAM);
    const char *afid = reinterpret_cast<const char *>(buffer);
    afid += bit_header->m_sectionOffset;
    if (bit_header->m_sectionSize > AFI_ID_STR_MAX)
        return nullptr;
    if (std::memcmp(afid, "afi-", 4) && std::memcmp(afid, "agfi-", 5))
        return nullptr;
    return afid;
}
