obj-m += edma-drv.o

edma-drv-objs :=  \
        edma.o edma_dev.o

KERNEL_VERSION ?= $(shell uname -r)

KBUILD_CPPFLAGS+=-I$(PWD)/
KBUILD_CPPFLAGS+=-DDRV_MODULE_VERSION=\"alpha1\"

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
