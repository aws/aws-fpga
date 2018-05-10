/**
 * Copyright (C) 2017-2018 Xilinx, Inc
 * Author: Sonal Santan
 * Simple command line utility to inetract with SDX PCIe devices
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
#include <iostream>
#include <cstring>
#include <sys/types.h>
#include <fcntl.h>
#include <unistd.h>
#include <string>

#include "xclhal.h"
namespace xcldev {
  class memaccess {
    std::string mDevName;
    size_t mDDRSize, mDataAlignment;
  public:
    memaccess(std::string aDevName, size_t aDDRSize, size_t aDataAlignment) :
              mDevName(aDevName), mDDRSize(aDDRSize), mDataAlignment (aDataAlignment) {}

    int read(std::string aFilename, unsigned long long aStartAddr = 0, unsigned long long aSize = 0) {
      void *buf = 0;
      unsigned long long size;
      unsigned long long blockSize = 0x20000;
      if (posix_memalign(&buf, 4096, blockSize))
        return -1;
      std::memset(buf, 0, blockSize);

      //sanity check
      if (aStartAddr > mDDRSize) {
        std::cout << "Start address " << std::hex << aStartAddr <<
        " is greater than device memory " << std::hex << mDDRSize << std::endl;
        return -1;
      }
      //sanity check
      if (aSize > mDDRSize || aStartAddr+aSize > mDDRSize) {
        std::cout << "Read size " << std::dec << aSize << " from address 0x" << std::hex << aStartAddr <<
          " goes beyond the device memory" << std::endl;
        return -1;
      }

      unsigned long long endAddr = aSize == 0 ? mDDRSize : aStartAddr+aSize;

      size = endAddr-aStartAddr;
      std::ofstream outFile(aFilename, std::ofstream::out | std::ofstream::binary);

      // Use plain POSIX open/pwrite/close.
      std::string baseName = mDevName;
      baseName += "_c2h_0";
      int fd = open(baseName.c_str(), O_RDONLY);
      if (fd < 0) {
        std::cout << "Unable to open device node " << baseName << "\n";
        return -1;
      }
      size_t count = size;
      uint64_t incr;
      size_t nRead = 0;
      for (uint64_t phy = aStartAddr; phy < aStartAddr+size; phy += incr) {
        incr = (count >= blockSize) ? blockSize : count;
        nRead = pread(fd, (char *)buf, incr, phy);
        if (nRead == (size_t)-1) {
          //error
          std::cout << "Error (" << strerror (errno) << ") reading " << incr << " bytes from DDR at offset " << std::hex << phy << std::dec << "\n";
          return -1;
        }
        count -= nRead;
        if (nRead) {
          outFile.write((const char*)(char*)buf, nRead);
          if ((outFile.rdstate() & std::ifstream::failbit) != 0) {
            std::cout << "Error writing to file \n";
          }
        }
        std::cout << "INFO: Read block 0x" << std::hex << nRead << " total 0x" <<size-count << std::endl;
      }
      close(fd);
      if (count != 0) {
        std::cout << "Error! Read " << std::dec << size-count << " bytes, requested " << size << std::endl;
        return -1;
      }
      std::cout << "INFO: Written " << std::dec << size << " bytes "
        << " to file " << aFilename << std::endl;
      outFile.close();
      free(buf);
      return count;
    }

    int write(unsigned long long aStartAddr, unsigned long long aSize, unsigned int aPattern) {
      void *buf = 0;
      int wfd = -1;
      unsigned long long endAddr;
      unsigned long long size;
      unsigned long long blockSize = 0x20000;
      if (posix_memalign(&buf, 4096, blockSize))
        return -1;

      //sanity check
      if (aStartAddr > mDDRSize) {
        std::cout << "Start address " << std::hex << aStartAddr <<
           " is greater than device memory " << std::hex << mDDRSize << std::endl;
        return -1;
      }
      //sanity check
      if (aSize > mDDRSize || aStartAddr+aSize > mDDRSize) {
        std::cout << "Read size " << std::dec << aSize << " from address 0x" << std::hex << aStartAddr <<
          " goes beyond the device memory" << std::endl;
        return -1;
      }

      endAddr = aSize == 0 ? mDDRSize : aStartAddr + aSize;
      size = endAddr-aStartAddr;

      // Use plain POSIX open/pwrite/close.
      std::string baseName = mDevName;
      baseName += "_h2c_0";

      std::cout << "INFO: Writing DDR with " << std::dec << size << " bytes of pattern: 0x"
         << std::hex << aPattern << " from address 0x" <<std::hex << aStartAddr << std::endl;

      wfd = open(baseName.c_str(), O_WRONLY);
      if (wfd < 0) {
        std::cout << "Unable to open device node " << baseName << " for write\n";
        return -1;
      }
      unsigned long long count = size;
      uint64_t incr;
      std::memset(buf, aPattern, blockSize);
      for(uint64_t phy=aStartAddr; phy<endAddr; phy+=incr) {
        incr = (count >= blockSize) ? blockSize : count;
        size_t nWrite = pwrite(wfd, (const char *)buf, incr, phy);
        if (nWrite == (size_t)-1) {
          //error
          std::cout << "Error (" << strerror (errno) << ") writing " << incr << " bytes to DDR at offset " << std::hex << phy << std::dec << "\n";
          return -1;
        }
        count -= nWrite;
      }

      close(wfd);
      if (count != 0) {
        std::cout << "Error! Written " << std::dec << size-count << " bytes, requested " << size << std::endl;
        return -1;
      }
      return count;
    }
  };
}
