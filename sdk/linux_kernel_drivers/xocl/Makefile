# Amazon FPGA Hardware Development Kit
#
# Copyright 2016-2018 Amazon.com, Inc. or its affiliates. All Rights Reserved.
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

XOCL_DIR = $(shell pwd)

obj-m	+= xocl.o
ccflags-y := -Iinclude/drm

xocl-y := \
	xocl_sysfs.o \
	xocl_bo.o \
	xocl_drv.o \
	xocl_xdma.o \
	xocl_ioctl.o \
	xocl_test.o \
	xocl_ctx.o \
	xocl_xvc.o \
	xocl_exec.o \
	libxdma.o

CONFIG_MODULE_SIG=n
KERNELDIR ?= /lib/modules/$(shell uname -r)/build

PWD           := $(shell pwd)
ROOT          := $(dir $(M))
XILINXINCLUDE := -I$(SDACCEL_DIR)/userspace/include -I$(XOCL_DIR)
XILINXINCLUDE += -I$(XOCL_DIR)/../xdma/

all:
	echo "include: $(XILINXINCLUDE)"
	echo "sdaccel_dir: $(SDACCEL_DIR)"
	echo "ROOT: $(ROOT)"
	echo "XOCL_DIR: $(XOCL_DIR)"
	$(MAKE) -C $(KERNELDIR) M=$(PWD) modules

install: all
	$(MAKE) -C $(KERNELDIR) M=$(PWD) modules_install
	depmod -a
	install -m 644 10-xocl.rules /etc/udev/rules.d
	-rmmod -s xocl || true
	-rmmod -s xdma || true
	-rmmod -s edma_drv || true	
	-modprobe xocl

clean:
	rm -rf *.o *.o.d *~ core .depend .*.cmd *.ko *.ko.unsigned *.mod.c .tmp_versions *.symvers .#* *.save *.bak Modules.* modules.order Module.markers *.bin


CFLAGS_xocl_xdma.o := $(XILINXINCLUDE)
CFLAGS_xocl_sysfs.o := $(XILINXINCLUDE)
CFLAGS_xocl_bo.o := $(XILINXINCLUDE)
CFLAGS_xocl_drv.o := $(XILINXINCLUDE)
CFLAGS_xocl_ioctl.o := $(XILINXINCLUDE)
CFLAGS_xocl_test.o := $(XILINXINCLUDE)
CFLAGS_xocl_ctx.o := $(XILINXINCLUDE)
CFLAGS_xocl_exec.o := $(XILINXINCLUDE)
CFLAGS_xocl_xvc.o := $(XILINXINCLUDE)
CFLAGS_libxdma.o := $(XILINXINCLUDE)
