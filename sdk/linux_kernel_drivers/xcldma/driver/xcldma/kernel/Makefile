obj-m += xcldma.o
xcldma-objs := xdma-core.o xdma-sgm.o xdma-ioctl.o xdma-bit.o

CONFIG_MODULE_SIG=n
KERNELDIR ?= /lib/modules/$(shell uname -r)/build

PWD       := $(shell pwd)

ROOT := $(dir $(M))
XILINXINCLUDE := -I$(ROOT)/include -I$(ROOT)../include

GCCVERSION = $(shell gcc -dumpversion | sed -e 's/\.\([0-9][0-9]\)/\1/g' -e 's/\.\([0-9]\)/0\1/g' -e 's/^[0-9]\{3,4\}$$/&00/')

GCC49 := $(shell expr $(GCCVERSION) \>= 40900)

all:
	$(MAKE) -C $(KERNELDIR) M=$(PWD) modules

install: all
	$(MAKE) -C $(KERNELDIR) M=$(PWD) modules_install
	depmod -a
	install -m 644 10-xcldma.rules /etc/udev/rules.d
	-rmmod -s xcldma || true
	-modprobe xcldma

clean:
	rm -rf *.o *.o.d *~ core .depend .*.cmd *.ko *.ko.unsigned *.mod.c .tmp_versions *.symvers .#* *.save *.bak Modules.* modules.order Module.markers *.bin

# there are variables, functions and labels in the code, often disabled by #if #endif
# but sometimes enabled during debugging. We do not want warnings if simply unused.
CFLAGS_xdma-core.o := -Wno-unused-variable -Wno-unused-function -Wno-unused-label $(XILINXINCLUDE)

ifeq ($(GCC49),1)
	CFLAGS_xdma-core.o += -Wno-error=date-time
endif

CFLAGS_xdma-bit.o := $(XILINXINCLUDE)
CFLAGS_xdma-ioctl.o := $(XILINXINCLUDE)
