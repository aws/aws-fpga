/*
 * Copyright (C) 2015-2018 Xilinx, Inc
 * Xilinx SDAccel HAL userspace driver APIs
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

#ifndef _XCL_HAL2_H_
#define _XCL_HAL2_H_

#ifdef __cplusplus
#include <cstdlib>
#include <cstdint>
#else
#include <stdlib.h>
#include <stdint.h>
#endif

#if defined(_WIN32)
#ifdef XCL_DRIVER_DLL_EXPORT
#define XCL_DRIVER_DLLESPEC __declspec(dllexport)
#else
#define XCL_DRIVER_DLLESPEC __declspec(dllimport)
#endif
#else
#define XCL_DRIVER_DLLESPEC __attribute__((visibility("default")))
#endif


#include "xclperf2.h"
#include "xcl_app_debug2.h"
#include "xclerr.h"

#ifdef __cplusplus
extern "C" {
#endif

/**
 * DOC: Xilinx Accelerator Hardware Abstraction Library Interface Definitions
 *
 * Header file *xclhal2.h* defines data structures and function signatures exported by
 * Hardware Abstraction Library (HAL). HAL is part of software stack which is integrated
 * into Xilinx reference platform.
 */

/**
 * typedef xclDeviceHandle - opaque device handle
 *
 * A device handle of xclDeviceHandle kind is obtained by opening a device. Clients pass this
 * device handle to refer to the opened device in all future interaction with HAL.
 */
typedef void * xclDeviceHandle;

struct xclBin;
struct axlf;

/**
 * Structure used to obtain various bits of information from the device.
 */

struct xclDeviceInfo2 {
  unsigned mMagic; // = 0X586C0C6C; XL OpenCL X->58(ASCII), L->6C(ASCII), O->0 C->C L->6C(ASCII);
  char mName[256];
  unsigned short mHALMajorVersion;
  unsigned short mHALMinorVersion;
  unsigned short mVendorId;
  unsigned short mDeviceId;
  unsigned short mSubsystemId;
  unsigned short mSubsystemVendorId;
  unsigned short mDeviceVersion;
  size_t mDDRSize;                    // Size of DDR memory
  size_t mDataAlignment;              // Minimum data alignment requirement for host buffers
  size_t mDDRFreeSize;                // Total unused/available DDR memory
  size_t mMinTransferSize;            // Minimum DMA buffer size
  unsigned short mDDRBankCount;
  unsigned short mOCLFrequency[4];
  unsigned short mPCIeLinkWidth;
  unsigned short mPCIeLinkSpeed;
  unsigned short mDMAThreads;
  short mOnChipTemp;
  short mFanTemp;
  unsigned short  mVInt;
  unsigned short  mVAux;
  unsigned short  mVBram;
  float mCurrent;
  unsigned short mNumClocks;
  unsigned short mFanSpeed;
  bool mMigCalib;
  // More properties here
};

/**
 * xclMemoryDomains is for support of legacy APIs
 * It is not used in BO APIs where we instead use xclBOKind
 */
enum xclMemoryDomains {
    XCL_MEM_HOST_RAM =    0x00000000,
    XCL_MEM_DEVICE_RAM =  0x00000001,
    XCL_MEM_DEVICE_BRAM = 0x00000002,
    XCL_MEM_SVM =         0x00000003,
    XCL_MEM_CMA =         0x00000004,
    XCL_MEM_DEVICE_REG  = 0x00000005
};

/* byte-0 lower 4 bits for DDR Flags are one-hot encoded */
enum xclDDRFlags {
    XCL_DEVICE_RAM_BANK0 = 0x00000000,
    XCL_DEVICE_RAM_BANK1 = 0x00000002,
    XCL_DEVICE_RAM_BANK2 = 0x00000004,
    XCL_DEVICE_RAM_BANK3 = 0x00000008
};

/**
 * xclBOKind defines Buffer Object Kind which represents a fragment of device accesible
 * memory and the corresponding backing host memory.
 *
 * 1. Shared virtual memory (SVM) class of systems like CAPI or MPSoc with SMMU. BOs
 *    have a common host RAM backing store.
 *    XCL_BO_SHARED_VIRTUAL
 *
 * 2. Shared physical memory class of systems like Zynq (or MPSoc with pass though SMMU)
 *    with Linux CMA buffer allocation. BOs have common host CMA allocated backing store.
 *    XCL_BO_SHARED_PHYSICAL
 *
 * 3. Shared virtual memory (SVM) class of systems with dedicated RAM and device MMU. BOs
 *    have a device RAM dedicated backing store and another host RAM allocated backing store.
 *    The buffers are sync'd via DMA. Both physical buffers use the same virtual address,
 *    hence giving the effect of SVM.
 *    XCL_BO_MIRRORED_VIRTUAL
 *
 * 4. Dedicated memory class of devices like PCIe card with DDR. BOs have a device RAM
 *    dedicated backing store and another host RAM allocated backing store. The buffers
 *    are sync'd via DMA
 *    XCL_BO_DEVICE_RAM
 *
 * 5. Dedicated onchip memory class of devices like PCIe card with BRAM. BOs have a device
 *    BRAM dedicated backing store and another host RAM allocated backing store. The buffers
 *    are sync'd via DMA
 *    XCL_BO_DEVICE_BRAM
 */

enum xclBOKind {
    XCL_BO_SHARED_VIRTUAL = 0,
    XCL_BO_SHARED_PHYSICAL,
    XCL_BO_MIRRORED_VIRTUAL,
    XCL_BO_DEVICE_RAM,
    XCL_BO_DEVICE_BRAM,
    XCL_BO_DEVICE_PREALLOCATED_BRAM,
};

enum xclBOSyncDirection {
    XCL_BO_SYNC_BO_TO_DEVICE = 0,
    XCL_BO_SYNC_BO_FROM_DEVICE,
};

/**
 * Define address spaces on the device AXI bus. The enums are used in xclRead() and xclWrite()
 * to pass relative offsets.
 */

enum xclAddressSpace {
    XCL_ADDR_SPACE_DEVICE_FLAT = 0,     // Absolute address space
    XCL_ADDR_SPACE_DEVICE_RAM = 1,      // Address space for the DDR memory
    XCL_ADDR_KERNEL_CTRL = 2,           // Address space for the OCL Region control port
    XCL_ADDR_SPACE_DEVICE_PERFMON = 3,  // Address space for the Performance monitors
    XCL_ADDR_SPACE_DEVICE_CHECKER = 5,  // Address space for protocol checker
    XCL_ADDR_SPACE_MAX = 8
};

/**
 * Defines verbosity levels which are passed to xclOpen during device creation time
 */

enum xclVerbosityLevel {
    XCL_QUIET = 0,
    XCL_INFO = 1,
    XCL_WARN = 2,
    XCL_ERROR = 3
};

enum xclResetKind {
    XCL_RESET_KERNEL,
    XCL_RESET_FULL
};

struct xclDeviceUsage {
    size_t h2c[8];
    size_t c2h[8];
    size_t ddrMemUsed[8];
    unsigned ddrBOAllocated[8];
    unsigned totalContexts;
    uint64_t xclbinId[4];
};

struct xclBOProperties {
    uint32_t handle;
    uint32_t flags;
    uint64_t size;
    uint64_t paddr;
    xclBOKind domain; // not implemented
};

/**
 * DOC: HAL Device Management APIs
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 */

/**
 * xclProbe() - Enumerate devices found in the system
 *
 * Return: count of devices found
 */
XCL_DRIVER_DLLESPEC unsigned xclProbe();

/**
 * xclOpen() - Open a device and obtain its handle.
 *
 * @deviceIndex:   Slot number of device 0 for first device, 1 for the second device...
 * @logFileName:   Log file to use for optional logging
 * @level:         Severity level of messages to log
 *
 * Return:         Device handle
 */
XCL_DRIVER_DLLESPEC xclDeviceHandle xclOpen(unsigned deviceIndex, const char *logFileName,
                                            xclVerbosityLevel level);

/**
 * xclClose() - Close an opened device
 *
 * @handle:        Device handle
 */
XCL_DRIVER_DLLESPEC void xclClose(xclDeviceHandle handle);

/**
 * xclResetDevice() - Reset a device or its CL
 *
 * @handle:        Device handle
 * @kind:          Reset kind
*  Return:         0 on success or appropriate error number
 *
 * Reset the device. All running kernels will be killed and buffers in DDR will be
 * purged. A device may be reset if a user's application dies without waiting for
 * running kernel(s) to finish.
 */
XCL_DRIVER_DLLESPEC int xclResetDevice(xclDeviceHandle handle, xclResetKind kind);

/**
 * xclGetDeviceInfo2() - Obtain various bits of information from the device
 *
 * @handle:        Device handle
 * @info:          Information record
 * Return:         0 on success or appropriate error number
 */
XCL_DRIVER_DLLESPEC int xclGetDeviceInfo2(xclDeviceHandle handle, xclDeviceInfo2 *info);

/**
 * xclGetUsageInfo() - Obtain usage information from the device
 *
 * @handle:        Device handle
 * @info:          Information record
 * Return:         0 on success or appropriate error number
 */
XCL_DRIVER_DLLESPEC int xclGetUsageInfo(xclDeviceHandle handle, xclDeviceUsage *info);

/**
 * xclGetErrorStatus() - Obtain error information from the device
 *
 * @handle:        Device handle
 * @info:          Information record
 * Return:         0 on success or appropriate error number
 */
XCL_DRIVER_DLLESPEC int xclGetErrorStatus(xclDeviceHandle handle, xclErrorStatus *info);

/**
 * xclLoadXclBin() - Download FPGA image (xclbin) to the device
 *
 * @handle:        Device handle
 * @buffer:        Pointer to device image (xclbin) in memory
 * Return:         0 on success or appropriate error number
 *
 * Download FPGA image (AXLF) to the device. The PR bitstream is encapsulated inside
 * xclbin as a section. xclbin may also contains other sections which are suitably
 * handled by the driver.
 */
XCL_DRIVER_DLLESPEC int xclLoadXclBin(xclDeviceHandle handle, const xclBin *buffer);

/**
 * xclReClock2() - Configure PR region frequncies
 *
 * @handle:        Device handle
 * @region:        PR region (always 0)
 * @targetFreqMHz: Array of target frequencies in order for the Clock Wizards driving
 *                 the PR region
 * Return:         0 on success or appropriate error number
 */
XCL_DRIVER_DLLESPEC int xclReClock2(xclDeviceHandle handle, unsigned short region,
                                    const unsigned short *targetFreqMHz);

/**
 * xclLockDevice() - Get exclusive ownership of the device
 *
 * @handle:        Device handle
 * Return:         0 on success or appropriate error number
 *
 * The lock is necessary before performing buffer migration, register access or
 * bitstream downloads.
 */
XCL_DRIVER_DLLESPEC int xclLockDevice(xclDeviceHandle handle);

/**
 * xclUnlockDevice() - Release exclusive ownership of the device
 *
 * @handle:        Device handle
 * Return:         0 on success or appropriate error number
 */
XCL_DRIVER_DLLESPEC int xclUnlockDevice(xclDeviceHandle handle);

/*
 * Update the device BPI PROM with new image
 */
XCL_DRIVER_DLLESPEC int xclUpgradeFirmware(xclDeviceHandle handle, const char *fileName);

/*
 * Update the device PROM with new image with clearing bitstream
 */
XCL_DRIVER_DLLESPEC int xclUpgradeFirmware2(xclDeviceHandle handle, const char *file1, const char* file2);

/*
 * Update the device SPI PROM with new image
 */
XCL_DRIVER_DLLESPEC int xclUpgradeFirmwareXSpi(xclDeviceHandle handle, const char *fileName, int index);

/**
 * xclBootFPGA() - Boot the FPGA from PROM
 *
 * @handle:        Device handle
 * Return:         0 on success or appropriate error number
 *
 * This should only be called when there are no other clients. It will cause PCIe bus re-enumeration
 */
XCL_DRIVER_DLLESPEC int xclBootFPGA(xclDeviceHandle handle);

/*
 * Write to /sys/bus/pci/devices/<deviceHandle>/remove and initiate a pci rescan by
 * writing to /sys/bus/pci/rescan.
 */
XCL_DRIVER_DLLESPEC int xclRemoveAndScanFPGA();

/*
 * Get the version number. 1 => Hal1 ; 2 => Hal2
 */
XCL_DRIVER_DLLESPEC unsigned int xclVersion();

/* End HAL Device Management APIs */

/**
 * DOC: HAL Buffer Management APIs
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 *
 * Buffer management APIs are used for managing device memory and migrating buffers
 * between host and device memory
 */

/**
 * xclAllocBO() - Allocate a BO of requested size with appropriate flags
 *
 * @handle:        Device handle
 * @size:          Size of buffer
 * @domain:        Memory domain
 * @flags:         Specify bank information, etc
 * Return:         BO handle
 */
XCL_DRIVER_DLLESPEC unsigned int xclAllocBO(xclDeviceHandle handle, size_t size, xclBOKind domain,
                                            unsigned flags);

/**
 * xclAllocUserPtrBO() - Allocate a BO using userptr provided by the user
 *
 * @handle:        Device handle
 * @userptr:       Pointer to 4K aligned user memory
 * @size:          Size of buffer
 * @flags:         Specify bank information, etc
 * Return:         BO handle
 */
XCL_DRIVER_DLLESPEC unsigned int xclAllocUserPtrBO(xclDeviceHandle handle, void *userptr, size_t size,
                                                   unsigned flags);

/**
 * xclFreeBO() - Free a previously allocated BO
 *
 * @handle:        Device handle
 * @boHandle:      BO handle
 */
XCL_DRIVER_DLLESPEC void xclFreeBO(xclDeviceHandle handle, unsigned int boHandle);

/**
 * xclWriteBO() - Copy-in user data to host backing storage of BO
 *
 * @handle:        Device handle
 * @boHandle:      BO handle
 * @src:           Source data pointer
 * @size:          Size of data to copy
 * @seek:          Offset within the BO
 * Return:         0 on success or appropriate error number
 *
 * Copy host buffer contents to previously allocated device memory. ``seek`` specifies how many bytes
 * to skip at the beginning of the BO before copying-in ``size`` bytes of host buffer.
 */
XCL_DRIVER_DLLESPEC size_t xclWriteBO(xclDeviceHandle handle, unsigned int boHandle,
                                       const void *src, size_t size, size_t seek);

/**
 * xclReadBO() - Copy-out user data from host backing storage of BO
 *
 * @handle:        Device handle
 * @boHandle:      BO handle
 * @dst:           Destination data pointer
 * @size:          Size of data to copy
 * @skip:          Offset within the BO
 * Return:         0 on success or appropriate error number
 *
 * Copy contents of previously allocated device memory to host buffer. ``skip`` specifies how many bytes
 * to skip from the beginning of the BO before copying-out ``size`` bytes of device buffer.
 */
XCL_DRIVER_DLLESPEC size_t xclReadBO(xclDeviceHandle handle, unsigned int boHandle,
                                     void *dst, size_t size, size_t skip);

/**
 * xclMapBO() - Memory map BO into user's address space
 *
 * @handle:        Device handle
 * @boHandle:      BO handle
 * @write:         READ only or READ/WRITE mapping
 * Return:         Memory mapped buffer
 *
 * Map the contents of the buffer object into host memory
 * To unmap the buffer call POSIX unmap() on mapped void * pointer returned from xclMapBO
 */
XCL_DRIVER_DLLESPEC void *xclMapBO(xclDeviceHandle handle, unsigned int boHandle, bool write);

/**
 * xclSyncBO() - Synchronize buffer contents in requested direction
 *
 * @handle:        Device handle
 * @boHandle:      BO handle
 * @dir:           To device or from device
 * @size:          Size of data to synchronize
 * @offset:        Offset within the BO
 * Return:         0 on success or standard errno
 *
 * Synchronize the buffer contents between host and device. Depending on the memory model this may
 * require DMA to/from device or CPU cache flushing/invalidation
 */
XCL_DRIVER_DLLESPEC int xclSyncBO(xclDeviceHandle handle, unsigned int boHandle, xclBOSyncDirection dir,
                                  size_t size, size_t offset);

/**
 * xclExportBO() - Obtain DMA-BUF file descriptor for a BO
 *
 * @handle:        Device handle
 * @boHandle:      BO handle which needs to be exported
 * Return:         File handle to the BO or standard errno
 *
 * Export a BO for import into another device or Linux subsystem which accepts DMA-BUF fd
 * This operation is backed by Linux DMA-BUF framework
 */
XCL_DRIVER_DLLESPEC int xclExportBO(xclDeviceHandle handle, unsigned int boHandle);

/**
 * xclImportBO() - Obtain BO handle for a BO represented by DMA-BUF file descriptor
 *
 * @handle:        Device handle
 * @fd:            File handle to foreign BO owned by another device which needs to be imported
 * @flags:         Unused
 * Return:         BO handle of the imported BO
 *
 * Import a BO exported by another device.     *
 * This operation is backed by Linux DMA-BUF framework
 */
XCL_DRIVER_DLLESPEC unsigned int xclImportBO(xclDeviceHandle handle, int fd, unsigned flags);

/**
 * xclGetBOProperties() - Obtain xclBOProperties struct for a BO
 *
 * @handle:        Device handle
 * @boHandle:      BO handle
 * @properties:    BO properties struct pointer
 * Return:         0 on success
 *
 * This is the prefered method for obtaining BO property information.
 */
XCL_DRIVER_DLLESPEC int xclGetBOProperties(xclDeviceHandle handle, unsigned int boHandle, xclBOProperties *properties);

/*
 * xclGetBOSize() - Retrieve size of a BO
 *
 *
 * @handle:        Device handle
 * @boHandle:      BO handle
 * Return          size_t size of the BO on success
 *
 * This API will be deprecated in the future. New clients should use xclGetBOProperties instead
 */
inline XCL_DRIVER_DLLESPEC size_t xclGetBOSize(xclDeviceHandle handle, unsigned int boHandle)
{
    xclBOProperties p;
    return !xclGetBOProperties(handle, boHandle, &p) ? (size_t)p.size : -1;
}

/*
 * Get the physical address on the device
 *
 * This function will be deprecated in the future. New clinets should use xclGetBOProperties instead.
 *
 * @handle:        Device handle
 * @boHandle:      BO handle
 * @return         uint64_t address of the BO on success
 */
inline XCL_DRIVER_DLLESPEC uint64_t xclGetDeviceAddr(xclDeviceHandle handle, unsigned int boHandle)
{
    xclBOProperties p;
    return !xclGetBOProperties(handle, boHandle, &p) ? p.paddr : -1;
}

/* End HAL Buffer Management APIs */

/**
 * DOC: HAL Legacy Buffer Management APIs
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 *
 * Do *not* develop new features using the following 5 API's. These are for backwards
 * compatibility with classic HAL interface and will be deprecated in future. New clients
 * should use BO based APIs defined above
 *
 */

/**
 * xclAllocDeviceBuffer() - Allocate a buffer on the device
 *
 * @handle:        Device handle
 * @size:          Size of buffer
 * Return:         Physical address of buffer on device or 0xFFFFFFFFFFFFFFFF in case of failure
 *
 * Allocate a buffer on the device DDR and return its address. This API will be deprecated in future.
 * Use xclAllocBO() in all new code.
 */
XCL_DRIVER_DLLESPEC uint64_t xclAllocDeviceBuffer(xclDeviceHandle handle, size_t size);

/**
 * xclAllocDeviceBuffer2() - Allocate a buffer on the device on a specific DDR
 *
 * @handle:        Device handle
 * @size:          Size of buffer
 * @domain:        Memory domain
 * @flags:         Desired DDR bank as a bitmap.
 * Return:         Physical address of buffer on device or 0xFFFFFFFFFFFFFFFF in case of failure
 *
 * Allocate a buffer on a specific device DDR and return its address. This API will be deprecated in future.
 * Use xclAllocBO() in all new code.
 */
XCL_DRIVER_DLLESPEC uint64_t xclAllocDeviceBuffer2(xclDeviceHandle handle, size_t size,
                                                   xclMemoryDomains domain,
                                                   unsigned flags);

/**
 * xclFreeDeviceBuffer() - Free a previously buffer on the device
 *
 * @handle:        Device handle
 * @buf:           Physical address of buffer
 *
 * The physical address should have been previously allocated by xclAllocDeviceBuffe() or xclAllocDeviceBuffer2().
 * The address should point to the beginning of the buffer and not at an offset in the buffer. This API will
 * be deprecated in future. Use xclFreeBO() together with BO allocation APIs.
 */
XCL_DRIVER_DLLESPEC void xclFreeDeviceBuffer(xclDeviceHandle handle, uint64_t buf);

/**
 * xclCopyBufferHost2Device() - Write to device memory
 *
 * @handle:        Device handle
 * @dest:          Physical address in the device
 * @src:           Source buffer pointer
 * @size:          Size of data to synchronize
 * @seek:          Seek within the segment pointed to physical address
 * Return:         Size of data moved or standard error number
 *
 * Copy host buffer contents to previously allocated device memory. ``seek`` specifies how many bytes to skip
 * at the beginning of the destination before copying ``size`` bytes of host buffer. This API will be
 * deprecated in future. Use xclSyncBO() together with other BO APIs.
 */
XCL_DRIVER_DLLESPEC size_t xclCopyBufferHost2Device(xclDeviceHandle handle, uint64_t dest,
                                                    const void *src, size_t size, size_t seek);

/**
 * xclCopyBufferDevice2Host() - Read from device memory
 *
 * @handle:        Device handle
 * @dest:          Destination buffer pointer
 * @src:           Physical address in the device
 * @size:          Size of data to synchronize
 * @skip:          Skip within the segment pointed to physical address
 * Return:         Size of data moved or standard error number
 *
 * Copy contents of previously allocated device memory to host buffer. ``skip`` specifies how many bytes to skip
 * from the beginning of the source before copying ``size`` bytes of device buffer. This API will be
 * deprecated in future. Use xclSyncBO() together with other BO APIs.
 */
XCL_DRIVER_DLLESPEC size_t xclCopyBufferDevice2Host(xclDeviceHandle handle, void *dest,
                                                    uint64_t src, size_t size, size_t skip);

/* End HAL Legacy Buffer Management APIs */


/**
 * DOC: HAL Unmanaged DMA APIs
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~
 *
 * Unmanaged DMA APIs are for exclusive use by the debuggers and tools. The APIs allow clinets to read/write
 * from/to absolute device address. No checks are performed if a buffer was allocated before at the specified
 * location or if the address is valid. Users who want to take over the full memory managemnt of the device
 * may use this API to synchronize their buffers between host and device.
 */

/**
 * xclUnmgdPread() - Perform unmanaged device memory read operation
 *
 * @handle:        Device handle
 * @flags:         Unused
 * @buf:           Destination data pointer
 * @size:          Size of data to copy
 * @offset:        Absolute offset inside device
 * Return:         size of bytes read or appropriate error number
 *
 * This API may be used to perform DMA operation from absolute location specified. Users
 * may use this if they want to perform their own device memory management -- not using the buffer
 * object (BO) framework defined before.
 */
XCL_DRIVER_DLLESPEC ssize_t xclUnmgdPread(xclDeviceHandle handle, unsigned flags, void *buf,
                                          size_t size, uint64_t offset);

/**
 * xclUnmgdPwrite() - Perform unmanaged device memory read operation
 *
 * @handle:        Device handle
 * @flags:         Unused
 * @buf:           Source data pointer
 * @size:          Size of data to copy
 * @offset:        Absolute offset inside device
 * Return:         size of bytes written or appropriate error number
 *
 * This API may be used to perform DMA operation to an absolute location specified. Users
 * may use this if they want to perform their own device memory management -- not using the buffer
 * object (BO) framework defined before.
 */
XCL_DRIVER_DLLESPEC ssize_t xclUnmgdPwrite(xclDeviceHandle handle, unsigned flags, const void *buf,
                                           size_t size, uint64_t offset);

/* End HAL Unmanaged DMA APIs */

/*
 * DOC: HAL Register read/write APIs
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 *
 * These functions are used to read and write peripherals sitting on the address map.  OpenCL runtime
 * will be using the BUFFER MANAGEMNT APIs described above to manage OpenCL buffers. It would use
 * xclRead/xclWrite to program and manage peripherals on the card. For programming the Kernel, OpenCL
 * runtime uses the kernel control register map generated by the xocc compiler.
 * Note that the offset is wrt the address space.
 */

/**
 * xclWrite() - Perform register write operation
 *
 * @handle:        Device handle
 * @space:         Address space
 * @offset:        Offset in the address space
 * @hostBuf:       Source data pointer
 * @size:          Size of data to copy
 * Return:         size of bytes written or appropriate error number
 *
 * This API may be used to write to device registers exposed on PCIe BAR. Offset is relative to the
 * the address space. A device may have many address spaces.
 */

XCL_DRIVER_DLLESPEC size_t xclWrite(xclDeviceHandle handle, xclAddressSpace space, uint64_t offset,
                                    const void *hostBuf, size_t size);

/**
 * xclRead() - Perform register read operation
 *
 * @handle:        Device handle
 * @space:         Address space
 * @offset:        Offset in the address space
 * @hostbuf:       Destination data pointer
 * @size:          Size of data to copy
 * Return:         size of bytes written or appropriate error number
 *
 * This API may be used to read from device registers exposed on PCIe BAR. Offset is relative to the
 * the address space. A device may have many address spaces.
 */
XCL_DRIVER_DLLESPEC size_t xclRead(xclDeviceHandle handle, xclAddressSpace space, uint64_t offset,
                                   void *hostbuf, size_t size);

/* HAL Register read/write APIs */

/*
 * TODO:
 * Define the following APIs
 *
 * 1. Host accessible pipe APIs: pread/pwrite
 * 2. Accelerator status, start, stop APIs
 * 3. Context creation APIs to support multiple clients
 * 4. Multiple OCL Region support
 * 5. DPDK style buffer management and device polling
 *
 */

/**
 * DOC: HAL Compute Unit Execution Management APIs
 *
 * These APIs are under development. These functions will be used to start compute
 * units and wait for them to finish.
 */

/**
 * xclExecBuf() - Submit an execution request to the embedded (or software) scheduler
 *
 * @handle:        Device handle
 * @cmdBO:         BO handle containing command packet
 * Return:         0 or standard error number
 *
 * This API is EXPERIMENTAL in this release. Submit an exec buffer for execution. The exec
 * buffer layout is defined by struct ert_packet which is defined in file *ert.h*. The BO
 * should been allocated with DRM_XOCL_BO_EXECBUF flag.
 */
XCL_DRIVER_DLLESPEC int xclExecBuf(xclDeviceHandle handle, unsigned int cmdBO);

/**
 * xclExecWait() - Wait for one or more execution events on the device
 *
 * @handle:                  Device handle
 * @timeoutMilliSec:         How long to wait for
 * Return:                   Same code as poll system call
 *
 * This API is EXPERIMENTAL in this release
 * Wait for notification from the hardware. The function essentially calls "poll" system
 * call on the driver file handle. The return value has same semantics as poll system call.
 * If return value is > 0 caller should check the status of submitted exec buffers
 */
XCL_DRIVER_DLLESPEC int xclExecWait(xclDeviceHandle handle, int timeoutMilliSec);

/**
 * xclRegisterInterruptNotify() - register *eventfd* file handle for a MSIX interrupt
 *
 * @handle:        Device handle
 * @userInterrupt: MSIX interrupt number
 * @fd:            Eventfd handle
 * Return:         0 on success or standard errno
 *
 * Support for non managed interrupts (interrupts from custom IPs). fd should be obtained from
 * eventfd system call. Caller should use standard poll/read eventfd framework in order to wait for
 * interrupts. The handles are automatically unregistered on process exit.
 */
XCL_DRIVER_DLLESPEC int xclRegisterInterruptNotify(xclDeviceHandle handle, unsigned int userInterrupt, int fd);

/* HAL Compute Unit Execution Management APIs */

/**
 * @defgroup perfmon PERFORMANCE MONITORING OPERATIONS
 * ---------------------------------------------------
 *
 * These functions are used to read and write to the performance monitoring infrastructure.
 * OpenCL runtime will be using the BUFFER MANAGEMNT APIs described above to manage OpenCL buffers.
 * It would use these functions to initialize and sample the performance monitoring on the card.
 * Note that the offset is wrt the address space
 */

/* Write host event to device tracing (Zynq only) */
XCL_DRIVER_DLLESPEC void xclWriteHostEvent(xclDeviceHandle handle, xclPerfMonEventType type,
                                           xclPerfMonEventID id);

XCL_DRIVER_DLLESPEC size_t xclGetDeviceTimestamp(xclDeviceHandle handle);

XCL_DRIVER_DLLESPEC double xclGetDeviceClockFreqMHz(xclDeviceHandle handle);

XCL_DRIVER_DLLESPEC double xclGetReadMaxBandwidthMBps(xclDeviceHandle handle);

XCL_DRIVER_DLLESPEC double xclGetWriteMaxBandwidthMBps(xclDeviceHandle handle);

XCL_DRIVER_DLLESPEC void xclSetProfilingNumberSlots(xclDeviceHandle handle, xclPerfMonType type,
                                                            uint32_t numSlots);

XCL_DRIVER_DLLESPEC uint32_t xclGetProfilingNumberSlots(xclDeviceHandle handle, xclPerfMonType type);

XCL_DRIVER_DLLESPEC void xclGetProfilingSlotName(xclDeviceHandle handle, xclPerfMonType type,
                                                 uint32_t slotnum, char* slotName, uint32_t length);

XCL_DRIVER_DLLESPEC size_t xclPerfMonClockTraining(xclDeviceHandle handle, xclPerfMonType type);

XCL_DRIVER_DLLESPEC size_t xclPerfMonStartCounters(xclDeviceHandle handle, xclPerfMonType type);

XCL_DRIVER_DLLESPEC size_t xclPerfMonStopCounters(xclDeviceHandle handle, xclPerfMonType type);

XCL_DRIVER_DLLESPEC size_t xclPerfMonReadCounters(xclDeviceHandle handle, xclPerfMonType type,
                                                          xclCounterResults& counterResults);

XCL_DRIVER_DLLESPEC size_t xclDebugReadIPStatus(xclDeviceHandle handle, xclDebugReadType type,
                                                                           void* debugResults);

XCL_DRIVER_DLLESPEC size_t xclPerfMonStartTrace(xclDeviceHandle handle, xclPerfMonType type,
                                                        uint32_t startTrigger);

XCL_DRIVER_DLLESPEC size_t xclPerfMonStopTrace(xclDeviceHandle handle, xclPerfMonType type);

XCL_DRIVER_DLLESPEC uint32_t xclPerfMonGetTraceCount(xclDeviceHandle handle, xclPerfMonType type);

XCL_DRIVER_DLLESPEC size_t xclPerfMonReadTrace(xclDeviceHandle handle, xclPerfMonType type,
                                                       xclTraceResultsVector& traceVector);

/** @} */

#ifdef __cplusplus
}
#endif

#endif
