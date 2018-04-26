/**
 * Copyright (C) 2017-2018 Xilinx, Inc
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

#ifndef _XIL_XVC_IOCALLS_POSIX_H_
#define _XIL_XVC_IOCALLS_POSIX_H_

#ifndef _WINDOWS
// TODO: Windows build support
#include <linux/ioctl.h>
#endif

#define XIL_XVC_MAGIC 0x58564344  // "XVCD"

struct xil_xvc_ioc {
	unsigned opcode;
	unsigned length;
	unsigned char *tms_buf;
	unsigned char *tdi_buf;
	unsigned char *tdo_buf;
};

#define XDMA_IOCXVC	_IOWR(XIL_XVC_MAGIC, 1, struct xil_xvc_ioc)

#endif // _XIL_XVC_IOCALLS_POSIX_H_
// 67d7842dbbe25473c3c32b93c0da8047785f30d78e8a024de1b57352245f9689
