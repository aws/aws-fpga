# Copyright 2015-2017 Amazon.com, Inc. or its affiliates. All Rights Reserved.
#
# Licensed under the Apache License, Version 2.0 (the "License"). You may
# not use this file except in compliance with the License. A copy of the
# License is located at
#
#     http://aws.amazon.com/apache2.0/
#
# or in the "license" file accompanying this file. This file is distributed
# on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
# express or implied. See the License for the specific language governing
# permissions and limitations under the License.

obj-m += edma-drv.o

edma-drv-objs :=  \
        edma.o edma_dev.o

KERNEL_VERSION ?= $(shell uname -r)

KBUILD_CPPFLAGS+=-I$(PWD)/
KBUILD_CPPFLAGS+=-DDRV_MODULE_VERSION=\"1.0.0\"

INSTALLED_MOD_NAME=edma-drv

ifeq ($(BACKEND_MEMORY),1)
        KBUILD_CPPFLAGS+=-DBACKEND_MEMORY=1
        edma-drv-objs +=  edma_backend_memory.o
else
		KBUILD_CPPFLAGS+=-DSUPPORT_M2M=1
        edma-drv-objs +=  edma_backend_xdma.o libxdma.o
endif

ccflags-y += -Wfatal-errors

all:
	make -C /lib/modules/$(KERNEL_VERSION)/build M=$(PWD) modules
unit-test:
	make -C ./unit-test all
clean:
	make -C /lib/modules/$(KERNEL_VERSION)/build M=$(PWD) clean

install:
	echo $(INSTALLED_MOD_NAME) > /etc/modules-load.d/$(INSTALLED_MOD_NAME).conf
	cp edma-drv.ko /lib/modules/`uname -r`/$(INSTALLED_MOD_NAME).ko
	depmod

uninstall:
	rm -f /etc/modules-load.d/$(INSTALLED_MOD_NAME).conf
	rm -f /lib/modules/`uname -r`/$(INSTALLED_MOD_NAME).ko
	depmod
