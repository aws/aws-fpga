/**
 *  Copyright (C) 2015-2018 Xilinx, Inc
 *
 *  This file is dual licensed.  It may be redistributed and/or modified
 *  under the terms of the Apache 2.0 License OR version 2 of the GNU
 *  General Public License.
 *
 *  Apache License Verbiage
 *
 *  Licensed under the Apache License, Version 2.0 (the "License");
 *  you may not use this file except in compliance with the License.
 *  You may obtain a copy of the License at
 *
 *  http://www.apache.org/licenses/LICENSE-2.0
 *
 *  Unless required by applicable law or agreed to in writing, software
 *  distributed under the License is distributed on an "AS IS" BASIS,
 *  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 *  See the License for the specific language governing permissions and
 *  limitations under the License.
 *
 *  GPL license Verbiage:
 *
 *  This program is free software; you can redistribute it and/or modify it under the terms of the GNU General Public License as published by the Free Software Foundation; either version 2 of the License, or (at your option) any later version.
 *  This program is distributed in the hope that it will be useful, but WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU General Public License for more details.
 *  You should have received a copy of the GNU General Public License along with this program; if not, write to the Free Software Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA 02111-1307 USA
 *
 */


/**
 *  Xilinx SDAccel FPGA BIOS definition
 *  Copyright (C) 2016-2017, Xilinx Inc - All rights reserved
 */


//Layout: At address 0xB0000, we will have the FeatureRomHeader that comprises:
//
//1. First have FeatureRomHeader: 152 bytes of information followed by
//2. Then, as a part of FeatureRomHeader we have the PRRegion struct(s).
//      The number of such structs will be same as OCLRegionCount.
//3. After this the freq scaling table is laid out. 
//

//#include <stdint.h>

typedef struct PartialRegion {
  uint16_t clk[4]; 
  uint8_t XPR; //0 : non-xpt, 1: xpr
} PRRegion;

// Each entry represents one row in freq scaling table.
struct FreqScalingTableRow{
  short config0;
  short freq;
  short config2;
};

enum PROMType  {
  BPI    = 0
  ,SPI   = 1
   //room for 6 more types of flash devices.
};

enum DebugType  {
  DT_NIFD  = 0x01,
  DT_FIREWALL  = 0x02
  //There is room for future expansion upto 8 IPs
};

// This bit mask is used with the FeatureBitMap to calculate 64 bool features
//
// To test if a feature is provided:
//   FeatureRomHeader header;
//   if (FeatureBitMask::FBM_IS_UNIFIED & header.FeatureBitMap)
//     // it is supported
//   else
//     // it is not supported
//
// To set if a feature is provided:
//   header.FeatureBitMap = 0;
//   header.FeatureBitMap |= FeatureBitMask::FBM_IS_UNIFIED;
//
enum FeatureBitMask
{ 
   UNIFIED_PLATFORM      =   0x0000000000000001       /* bit 1 : Unified platform */
   ,XARE_ENBLD           =   0x0000000000000002       /* bit 2 : Aurora link enabled DSA */
   ,BOARD_MGMT_ENBLD     =   0x0000000000000004       /* bit 3 : Has MB based power monitoring */
   ,MB_SCHEDULER         =   0x0000000000000008       /* bit 4:  Has MB based scheduler */
   ,PROM_MASK            =   0x0000000000000070       /* bits 5,6 &7  : 3 bits for PROMType */
   /**  ------ Bit 8 unused **/
   ,DEBUG_MASK           =   0x000000000000FF00       /* bits 9 through 16  : 8 bits for DebugType */

   //....more
};



// In the following data structures, the EntryPointString, MajorVersion, and MinorVersion
// values are all used in the Runtime to identify if the ROM is producing valid data, and 
// to pick the schema to read the rest of the data; Ergo, these values shall not change.

/* 
 * Struct used for >  2017.2_sdx
 * This struct should be used for version (==) 10.0 (Major: 10, Minor: 0)
 */
struct FeatureRomHeader { 
  unsigned char EntryPointString[4];  // This is "xlnx"
  uint8_t MajorVersion;               // Feature ROM's major version eg 1 
  uint8_t MinorVersion;               // minor version eg 2.
  // -- DO NOT CHANGE THE TYPES ABOVE THIS LINE --
  uint32_t VivadoBuildID;             // Vivado Software Build (e.g., 1761098 ). From ./vivado --version
  uint32_t IPBuildID;                 // IP Build (e.g., 1759159 from abve)
  uint64_t TimeSinceEpoch;            // linux time(NULL) call, at write_dsa_rom invocation
  unsigned char FPGAPartName[64];     // The hardware FPGA part. Null termninated
  unsigned char VBNVName[64];         // eg : xilinx:xil-accel-rd-ku115:4ddr-xpr:3.4: null terminated
  uint8_t DDRChannelCount;            // 4 for TUL
  uint8_t DDRChannelSize;             // 4 (in GB)
  uint64_t DRBaseAddress;	      // The Dynamic Range's (AppPF/CL/Userspace) Base Address
  uint64_t FeatureBitMap;             // Feature Bit Map, specifies 64 different bool features, maps to enum FeatureBitMask
};


/* 
 * Struct used for 2017.1_sdx
 * This struct should be used for all versions below (<) 10.0 (Major: 10, Minor: 0)
struct FeatureRomHeader { 
  unsigned char EntryPointString[4];  // This is "xlnx"
  uint8_t MajorVersion;               // Feature ROM's major version eg 1 
  uint8_t MinorVersion;               // minor version eg 2.
  // -- DO NOT CHANGE THE TYPES ABOVE THIS LINE --
  uint32_t VivadoBuildID;             // Vivado Software Build (e.g., 1761098 ). From ./vivado --version
  uint32_t IPBuildID;                 // IP Build (e.g., 1759159 from abve)
  uint64_t TimeSinceEpoch;            // linux time(NULL) call, at write_dsa_rom invocation
  unsigned char FPGAPartName[64];     // The hardware FPGA part. Null termninated
  unsigned char VBNVName[64];         // eg : xilinx:xil-accel-rd-ku115:4ddr-xpr:3.4: null terminated
  uint8_t DDRChannelCount;            // 4 for TUL
  uint8_t DDRChannelSize;             // 4 (in GB)
  uint8_t OCLRegionCount;             // Number of OCL regions 
  uint8_t FPGAType;                   // maps to enum FPGAGeneration
  uint8_t NumFreqTableRows;           // Number of rows in freq scaling table.
  PRRegion region[1];                 // The PRRegion struct, lay them out one after another totalling OCLRegionCount.
  unsigned char FreqTable[1];         // NumFreqTableRows of FreqScalingTableRow struct
};
*/

