/**
 * Copyright (C) 2016-2018 Xilinx, Inc
 * Author(s): Hem C Neema
 * PCIe HAL Driver layered on top of XOCL GEM kernel driver
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

#include <errno.h>

#include <iostream>
#include <fstream>
#include <vector>
#include <iomanip>
#include <fcntl.h>
#include <sys/ioctl.h>
#include <sys/mman.h>
#include <cstring>
#include <unistd.h>
#include <sys/file.h>

#include "xclbin2.h"
#include "scan.h"
#include "awssak.h"


uint32_t xcldev::device::getIPCountAddrNames(int type, std::vector<uint64_t> *baseAddress, std::vector<std::string> * portNames) {
    debug_ip_layout *map;
    std::string path = "/sys/bus/pci/devices/" + xcldev::pci_device_scanner::device_list[ m_idx ].user_name + "/debug_ip_layout";
    std::ifstream ifs(path.c_str(), std::ifstream::binary);
    uint32_t count = 0;
    char buffer[4096];
    if( ifs.good() ) {
        //sysfs max file size is 4096
        ifs.read(buffer, 4096);
        if (ifs.gcount() > 0) {
            map = (debug_ip_layout*)(buffer);
            for( unsigned int i = 0; i < map->m_count; i++ ) {
                if (map->m_debug_ip_data[i].m_type == type) {
                    if(baseAddress)baseAddress->push_back(map->m_debug_ip_data[i].m_base_address);
                    if(portNames) portNames->push_back((char*)map->m_debug_ip_data[i].m_name);
                    ++count;
                }
            }
        }
        ifs.close();
    }
    else {
        std::cout <<  "ERROR: Failed to open debug IP layout file. Ensure that a valid xclbin is successfully downloaded. \n";
        return -1;
    }
    return count;
}

std::pair<size_t, size_t> xcldev::device::getCUNamePortName (std::vector<std::string>& aSlotNames,
    std::vector< std::pair<std::string, std::string> >& aCUNamePortNames) {
    //Slotnames are of the format "/cuname/portname" or "cuname/portname", split them and return in separate vector
    //return max length of the cuname and port names
    size_t max1 = 0, max2 = 0;
    char sep = '/';
    for (auto slotName: aSlotNames) {
        size_t found1;
        size_t start = 0;
        found1 = slotName.find(sep, 0);
        if (found1 == 0) {
            //if the cuname starts with a '/'
            start = 1;
            found1 = slotName.find(sep, 1);
        }
        if (found1 != std::string::npos) {
            aCUNamePortNames.emplace_back(slotName.substr(start, found1-start), slotName.substr(found1+1));
        }
        else {
            aCUNamePortNames.emplace_back("Unknown", "Unknown");
        }
        //Replace the name of the host-spm to something simple
        if (aCUNamePortNames.back().first.find("interconnect_host_aximm") != std::string::npos) {
            aCUNamePortNames.pop_back();
            aCUNamePortNames.emplace_back("XDMA", "N/A");
        }
        max1 = std::max(aCUNamePortNames.back().first.length(), max1);
        max2 = std::max(aCUNamePortNames.back().second.length(), max2);
    }
    return std::pair<size_t, size_t>(max1, max2);
}

int xcldev::device::readSPMCounters() {
    xclDebugCountersResults debugResults = {0};
    std::vector<std::string> slotNames;
    std::vector< std::pair<std::string, std::string> > cuNameportNames;
    unsigned int numSlots = getIPCountAddrNames (AXI_MM_MONITOR, nullptr, &slotNames);
    if (numSlots == 0) {
        std::cout << "ERROR: SPM IP does not exist on the platform" << std::endl;
        return 0;
    }
    std::pair<size_t, size_t> widths = getCUNamePortName(slotNames, cuNameportNames);
    xclDebugReadIPStatus(m_handle, XCL_DEBUG_READ_TYPE_SPM, &debugResults);

    std::cout << "SDx Performance Monitor Counters\n";
    int col1 = std::max(widths.first, strlen("CU Name")) + 4;
    int col2 = std::max(widths.second, strlen("AXI Portname"));

    std::cout << std::left
            << std::setw(col1) << "CU Name"
            << " " << std::setw(col2) << "AXI Portname"
            << "  " << std::setw(16)  << "Write Bytes"
            << "  " << std::setw(16)  << "Write Trans."
            << "  " << std::setw(16)  << "Read Bytes"
            << "  " << std::setw(16)  << "Read Tranx."
            << "  " << std::setw(16)  << "Outstanding Cnt"
            << "  " << std::setw(16)  << "Last Wr Addr"
            << "  " << std::setw(16)  << "Last Wr Data"
            << "  " << std::setw(16)  << "Last Rd Addr"
            << "  " << std::setw(16)  << "Last Rd Data"
            << std::endl;
    for (unsigned int i = 0; i<debugResults.NumSlots; ++i) {
        std::cout << std::left
            << std::setw(col1) << cuNameportNames[i].first
            << " " << std::setw(col2) << cuNameportNames[i].second
            << "  " << std::setw(16) << debugResults.WriteBytes[i]
            << "  " << std::setw(16) << debugResults.WriteTranx[i]
            << "  " << std::setw(16) << debugResults.ReadBytes[i]
            << "  " << std::setw(16) << debugResults.ReadTranx[i]
            << "  " << std::setw(16) << debugResults.OutStandCnts[i]
            << "  " << std::hex << "0x" << std::setw(16) << debugResults.LastWriteAddr[i] << std::dec
            << "  " << std::setw(16) << debugResults.LastWriteData[i]
            << "  " << std::hex << "0x" << std::setw(16) <<  debugResults.LastReadAddr[i] << std::dec
            << "  " << std::setw(16) << debugResults.LastReadData[i]
            << std::endl;
    }
    return 0;
}

int xcldev::device::readLAPCheckers(int aVerbose) {
    xclDebugCheckersResults debugResults = {0};
    //if (getuid() && geteuid()) {
    //    std::cout << "ERROR: Reading LAPC requires root privileges" << std::endl;
    //    return -EACCES;
    //}
    std::vector<std::string> lapcSlotNames;
    std::vector< std::pair<std::string, std::string> > cuNameportNames;
    unsigned int numSlots = getIPCountAddrNames (LAPC, nullptr, &lapcSlotNames);
    if (numSlots == 0) {
        std::cout << "ERROR: LAPC IP does not exist on the platform" << std::endl;
        return 0;
    }
    std::pair<size_t, size_t> widths = getCUNamePortName(lapcSlotNames, cuNameportNames);
    xclDebugReadIPStatus(m_handle, XCL_DEBUG_READ_TYPE_LAPC, &debugResults);
    bool violations_found = false;
    bool invalid_codes = false;
    std::cout << "Light Weight AXI Protocol Checkers codes \n";
    int col1 = std::max(widths.first, strlen("CU Name")) + 4;
    int col2 = std::max(widths.second, strlen("AXI Portname"));

    for (unsigned int i = 0; i<debugResults.NumSlots; ++i) {
        if (!xclAXICheckerCodes::isValidAXICheckerCodes(debugResults.OverallStatus[i],
                        debugResults.SnapshotStatus[i], debugResults.CumulativeStatus[i])) {
            std::cout << "CU Name: " << cuNameportNames[i].first << " AXI Port: " << cuNameportNames[i].second << "\n";
            std::cout << "  Invalid codes read, skip decoding\n";
            invalid_codes = true;
        }
        else if (debugResults.OverallStatus[i]) {
            std::cout << "CU Name: " << cuNameportNames[i].first << " AXI Port: " << cuNameportNames[i].second << "\n";
            std::cout << "  First violation: \n";
            std::cout << "    " <<  xclAXICheckerCodes::decodeAXICheckerCodes(debugResults.SnapshotStatus[i]);
            //snapshot reflects first violation, cumulative has all violations
            unsigned int tCummStatus[4];
            std::transform(debugResults.CumulativeStatus[i], debugResults.CumulativeStatus[i]+4, debugResults.SnapshotStatus[i], tCummStatus, std::bit_xor<unsigned int>());
            std::cout << "  Other violations: \n";
            std::string tstr = xclAXICheckerCodes::decodeAXICheckerCodes(tCummStatus);
            if (tstr == "") {
              std::cout << "    None";
            }
            else {
              std::cout << "    " <<  tstr;
            }
            violations_found = true;
        }
    }
    if (!violations_found && !invalid_codes) {
        std::cout << "No AXI violations found \n";
    }
    if (violations_found && aVerbose && !invalid_codes) {
        std::cout << "\n";
        std::cout << std::left
                << std::setw(col1) << "CU Name"
                << " " << std::setw(col2) << "AXI Portname"
                << "  " << std::setw(16) << "Overall Status"
                << "  " << std::setw(16) << "Snapshot[0]"
                << "  " << std::setw(16) << "Snapshot[1]"
                << "  " << std::setw(16) << "Snapshot[2]"
                << "  " << std::setw(16) << "Snapshot[3]"
                << "  " << std::setw(16) << "Cumulative[0]"
                << "  " << std::setw(16) << "Cumulative[1]"
                << "  " << std::setw(16) << "Cumulative[2]"
                << "  " << std::setw(16) << "Cumulative[3]"
                << std::endl;
        for (unsigned int i = 0; i<debugResults.NumSlots; ++i) {
            std::cout << std::left
                << std::setw(col1) << cuNameportNames[i].first
                << " " << std::setw(col2) << cuNameportNames[i].second
                << "  " << std::setw(16) << std::hex << debugResults.OverallStatus[i]
                << "  " << std::setw(16) << std::hex << debugResults.SnapshotStatus[i][0]
                << "  " << std::setw(16) << std::hex << debugResults.SnapshotStatus[i][1]
                << "  " << std::setw(16) << std::hex << debugResults.SnapshotStatus[i][2]
                << "  " << std::setw(16) << std::hex << debugResults.SnapshotStatus[i][3]
                << "  " << std::setw(16) << std::hex << debugResults.CumulativeStatus[i][0]
                << "  " << std::setw(16) << std::hex << debugResults.CumulativeStatus[i][1]
                << "  " << std::setw(16) << std::hex << debugResults.CumulativeStatus[i][2]
                << "  " << std::setw(16) << std::hex << debugResults.CumulativeStatus[i][3]
                << std::dec << std::endl;
        }
    }
    return 0;
}

int xcldev::device::print_debug_ip_list (int aVerbose) {
    static const char * debug_ip_names[7] = {
        "unknown", "lapc", "ila", "spm", "tracefunnel", "monitorfifolite", "monitorfifofull"
    };
    int available_ip [7] = {0};
    debug_ip_layout *map;
    std::string path = "/sys/bus/pci/devices/" + xcldev::pci_device_scanner::device_list[ m_idx ].user_name + "/debug_ip_layout";
    std::ifstream ifs(path.c_str(), std::ifstream::binary);

    char buffer[4096];
    std::stringstream sstr;
    if( ifs.good() ) {
        ifs.read(buffer, 4096);
        if (ifs.gcount() > 0) {
            map = (debug_ip_layout*)(buffer);
            std::cout << "Number of IPs found: " << map->m_count << "\n";
            for( unsigned int i = 0; i < map->m_count; i++ ) {
                if ( map->m_debug_ip_data[i].m_type > sizeof (debug_ip_names)/sizeof(debug_ip_names[0])) {
                    std::cout  << "Found invalid IP in debug ip layout with type "
                                << map->m_debug_ip_data[i].m_type << std::endl;
                    ifs.close();
                    return -1;
                }
                ++available_ip[map->m_debug_ip_data[i].m_type];
            }
            for(unsigned int i = 0; i<sizeof(available_ip)/sizeof(available_ip[0]); ++i) {
                if (available_ip[i])
                    sstr << debug_ip_names[i] << "(" << available_ip[i] << ") ";
            }
                ifs.close();
        }
        else {
            std::cout << "INFO: Failed to find any debug IPs on the platform. Ensure that a valid bitstream with debug IPs (SPM, LAPC) is successfully downloaded. \n";
            ifs.close();
            return 0;
        }
    } else {
        std::cout << "INFO: Failed to find any debug IPs on the platform. Ensure that a valid bitstream with debug IPs (SPM, LAPC) is successfully downloaded. \n";
        return 0;
    }
    std::cout << "IPs found [<ipname>(<count>)]: " << sstr.str() << std::endl;
    std::cout << "Run 'xbsak status' with option --<ipname> to get more information about the IP" << std::endl;
    return 0;
}


