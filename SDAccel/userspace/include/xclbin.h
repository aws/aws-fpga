/**
 * Copyright (C) 2015-2018 Xilinx, Inc
 *
 * Xilinx SDAccel xclbin container definition
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

#ifndef _XCLBIN_H_
#define _XCLBIN_H_

#if defined(__KERNEL__)
#include <linux/types.h>
#elif defined(__cplusplus)
#include <cstdlib>
#include <cstdint>
#include <algorithm>
#else
#include <stdlib.h>
#include <stdint.h>
#endif

#ifdef __cplusplus
extern "C" {
#endif

    enum XCLBIN_MODE {
        // Use with flat flow where the full FPGA is re-programmed
        XCLBIN_FLAT,
        // Used with Partial Reconfig flow
        XCLBIN_PR,
        // Unused at the moment
        XCLBIN_TANDEM_STAGE2,
        // Unused at the moment
        XCLBIN_TANDEM_STAGE2_WITH_PR,
        // Used in HW emulation
        XCLBIN_HW_EMU,
        // Used in SW emulation
        XCLBIN_SW_EMU,
        XCLBIN_MODE_MAX
    };

    /**
     * Note that xclBin format has been deprecated from 2017.1 release onwards.
     * SDAccel has switched to AXLF also known as xclbin2 -- look for struct axlf
     * below.
     */

    struct xclBin {
        char m_magic[8];                    /* should be xclbin0\0  */
        uint64_t m_length;                  /* total size of the xclbin file */
        uint64_t m_timeStamp;               /* number of seconds since epoch when xclbin was created */
        uint64_t m_version;                 /* tool version used to create xclbin */
        unsigned m_mode;                    /* XCLBIN_MODE */
        char m_nextXclBin[24];              /* Name of next xclbin file in the daisy chain */
        uint64_t m_metadataOffset;          /* file offset of embedded metadata */
        uint64_t m_metadataLength;          /* size of the embedded metdata */
        uint64_t m_primaryFirmwareOffset;   /* file offset of bitstream or emulation archive */
        uint64_t m_primaryFirmwareLength;   /* size of the bistream or emulation archive */
        uint64_t m_secondaryFirmwareOffset; /* file offset of clear bitstream if any */
        uint64_t m_secondaryFirmwareLength; /* size of the clear bitstream */
        uint64_t m_driverOffset;            /* file offset of embedded device driver if any (currently unused) */
        uint64_t m_driverLength;            /* size of the embedded device driver (currently unused) */

        // Extra debug information for hardware and hardware emulation debug

        uint64_t m_dwarfOffset ;
        uint64_t m_dwarfLength ;
        uint64_t m_ipiMappingOffset ;
        uint64_t m_ipiMappingLength ;
    };

    /*
     *  AXLF LAYOUT
     *  -----------
     *
     *  -----------------------------------------
     *  | Magic                                 |
     *  -----------------------------------------
     *  | Header                                |
     *  -----------------------------------------
     *  | One or more section headers           |
     *  -----------------------------------------
     *  | Matching number of sections with data |
     *  -----------------------------------------
     *
     */

    enum axlf_section_kind {
        BITSTREAM = 0,
        CLEARING_BITSTREAM = 1,
        EMBEDDED_METADATA = 2,
        FIRMWARE = 3,
        DEBUG_DATA = 4
    };

    struct axlf_section_header {
        uint32_t m_sectionKind;             /* Section type */
        char m_sectionName[16];             /* Examples: "stage2", "clear1", "clear2", "ocl1", "ocl2, "ublaze" */
        uint64_t m_sectionOffset;           /* File offset of section data */
        uint64_t m_sectionSize;             /* Size of section data */
    };

    struct axlf_header {
        uint64_t m_length;                  /* Total size of the xclbin file */
        uint64_t m_timeStamp;               /* Number of seconds since epoch when xclbin was created */
        uint64_t m_featureRomTimeStamp;     /* TimeSinceEpoch of the Feature ROM in the DSA */
        uint32_t m_version;                 /* Tool version used to create xclbin */
        uint32_t m_mode;                    /* XCLBIN_MODE */
        uint64_t m_platformId;              /* 64 bit platform ID: vendor-device-subvendor-subdev */
        uint64_t m_featureId;               /* 64 bit feature id */
        unsigned char m_platformVBNV[64];   /* e.g. xilinx:xil-accel-rd-ku115:4ddr-xpr:3.4: null terminated */
        char m_next_axlf[16];               /* Name of next xclbin file in the daisy chain */
        char m_debug_bin[16];               /* Name of binary with debug information */
        uint32_t m_numSections;             /* Number of section headers */
    };

    struct axlf {
        char m_magic[8];                            /* Should be "xclbin2\0"  */
        unsigned char m_cipher[32];                 /* HMAC output digest */
        unsigned char m_keyBlock[256];              /* Signature for validation of binary */
        uint64_t m_uniqueId;                        /* axlf's uniqueId, use it to skip re-download etc */
        struct axlf_header m_header;                /* Inline header */
        struct axlf_section_header m_sections[1];   /* One or more section headers follow */
    };

    //xilinx internal
    struct xlnx_bitstream {
        uint8_t m_freq[8];
        char bits[1];
    };

# ifdef __cplusplus
    namespace xclbin {
      inline const axlf_section_header*
      get_axlf_section(const axlf* top, axlf_section_kind kind)
      {
        auto begin = top->m_sections;
        auto end = begin + top->m_header.m_numSections;
        auto itr = std::find_if(begin,end,[kind](const axlf_section_header& sec) { return sec.m_sectionKind==kind; });
        return (itr!=end) ? &(*itr) : nullptr;
      }
    }
# endif

#ifdef __cplusplus
}
#endif

#endif
