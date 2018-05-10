/**
 * Copyright (C) 2016-2018 Xilinx, Inc
 * Author: Sonal Santan
 * XDMA HAL multi-threading safe, multi-channel DMA read/write support
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

#ifndef _XDMA_DATA_MOVER_H_
#define _XDMA_DATA_MOVER_H_

#include <fstream>
#include <list>
#include <vector>
#include <string>
#include <mutex>
#include <condition_variable>
#include <cassert>
#include <sys/types.h>
#include <sys/stat.h>
#include <fcntl.h>
#include <unistd.h>
#include <sys/file.h>

// Work around GCC 4.8 + XDMA BAR implementation bugs
// With -O3 PCIe BAR read/write are not reliable hence force -O2 as max
// optimization level for pcieBarRead() and pcieBarWrite()
#if defined(__GNUC__) && defined(NDEBUG)
#define SHIM_O2 __attribute__ ((optimize("-O2")))
#else
#define SHIM_O2
#endif

#if defined(AWS_EDMA)
        #define DMA_PATHNAME "/dev/edma"
        #define DMA_PATHH2C "_queue_"
        #define DMA_PATHC2H "_queue_"
#else
        #define DMA_PATHNAME "/dev/xdma"
        #define DMA_PATHH2C "_h2c_"
        #define DMA_PATHC2H "_c2h_"
#endif

namespace awsbwhal {
    class DMAChannelManager
    {
    public:
        DMAChannelManager(unsigned deviceIndex, unsigned count, std::ios_base::openmode mode) : mCount(count) {
            std::string baseName(DMA_PATHNAME);
            baseName += std::to_string(deviceIndex);
            assert((mode == std::ios_base::in) || (mode == std::ios_base::out));
            const char *suffix = (mode == std::ios_base::out) ? DMA_PATHH2C : DMA_PATHC2H;
            baseName += suffix;
            for (mIndex = 0; mIndex < static_cast<int>(mCount); ++mIndex) {
                std::string fileName(baseName);
                fileName += std::to_string(mIndex);
                mChannel.push_back(open(fileName.c_str(), (mode == std::ios_base::out) ? O_WRONLY : O_RDONLY));
            }
            --mIndex;
        }

        ~DMAChannelManager() {
            unlock();
            for (unsigned i = 0; i < mCount; i++) {
                close(mChannel[i]);
            }
        }

        bool isGood() const {
            for (unsigned i = 0; i < mCount; i++) {
                if (mChannel[i] < 0)
                    return false;
            }
            return true;
        }

        void releaseDMAChannel(int channel) {
            std::lock_guard<std::mutex> lck(mMtx);
            mChannel[++mIndex] = channel;
            mCV.notify_one();
        }

        int acquireDMAChannel() {
            std::unique_lock<std::mutex> lck(mMtx);
            while(mIndex < 0) {
                mCV.wait(lck);
            }
            return mChannel[mIndex--];
        }

        bool lock() const {
            for (unsigned i = 0; i < mCount; i++) {
                if (!flock(mChannel[i], LOCK_EX | LOCK_NB))
                    continue;
                // Unable to lock channel i, unlock all channels locked so far
                for (unsigned j = 0; j < i; j++) {
                    flock(mChannel[j], LOCK_UN);
                }
                return false;
            }
            return true;
        }

        void unlock() const {
            for (unsigned i = 0; i < mCount; i++) {
                flock(mChannel[i], LOCK_UN);
            }
        }

        unsigned channelCount() const {
            return mCount;
        }

    private:
        std::mutex mMtx;
        std::condition_variable mCV;
        std::vector<int> mChannel;
        const unsigned mCount;
        int mIndex;
    };

    class DataMover {
    public:
        DataMover(unsigned index, unsigned count) : mWrite(index, count, std::ios_base::out),
                                                    mRead(index, count, std::ios_base::in) {}

        // TODO: Make pwrite64 and pread64 use RAII for the channel resource
        ssize_t pwrite64(const void* buf, size_t count, off64_t offset) {
            if(count == 0) // Nothing to do
                return 0;
            int fd = mWrite.acquireDMAChannel();
            ssize_t rc = pwrite(fd, buf, count, offset);
            mWrite.releaseDMAChannel(fd);
            return rc;
        }
        ssize_t pread64(void* buf, size_t count, off64_t offset) {
            if(count == 0) // Nothing to do
                return 0;
            int fd = mRead.acquireDMAChannel();
            ssize_t rc = pread(fd, buf, count, offset);
            mRead.releaseDMAChannel(fd);
            return rc;
        }
        // Like memset but using pwrite
        void pset64(const void* buf, size_t count, off64_t offset, unsigned rep) {
            if(count == 0) // Nothing to do
                return;
            int fd = mWrite.acquireDMAChannel();
            off64_t curr = offset;
            while (rep-- > 0) {
#ifndef RDI_COVERITY
# pragma GCC diagnostic push
# pragma GCC diagnostic ignored "-Wunused-result"
                pwrite(fd, buf, count, curr);
# pragma GCC diagnostic pop
                curr += count;
#endif
            }
            mWrite.releaseDMAChannel(fd);
        }
        bool isGood() {
            return (mWrite.isGood() && mRead.isGood());
        }

        int lock() {
            if (mWrite.lock() && mRead.lock())
                return true;
            unlock();
            return false;
        }

        void unlock() {
            mWrite.unlock();
            mRead.unlock();
        }

        unsigned channelCount() const {
            return mWrite.channelCount() + mRead.channelCount();
        }

    private:
        DMAChannelManager mWrite;
        DMAChannelManager mRead;
    };
}


#endif
