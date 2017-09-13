EXENAME := xbsak

CXX_EXT := cpp
CL_EXT := cl

AR := ar
CXX := g++

CXXFLAGS := -Wall -Werror -std=c++11

ROOT = $(SDACCEL_DIR)
HAL_INC := -I../../include -I$(ROOT)/userspace/include

CXXFLAGS += $(HAL_INC)

ifeq ($(ec2),1)
AWSBM_HAL_LIBNAME := $(ROOT)/userspace/src/libawsxcldrv.a
else
AWSBM_HAL_LIBNAME := $(ROOT)/userspace/src/libawsbmdrv.a
endif

ifeq ($(debug),1)
	CXXFLAGS += -g -D_DEBUG
else
	CXXFLAGS += -O2 -DNDEBUG
endif

SRCS := $(wildcard *.$(CXX_EXT))
OBJS := $(patsubst %.$(CXX_EXT), %.o, $(SRCS))

-include $(OBJS:.o=.d)

AWS_FPGA_MGMTLIB := fpga_mgmt
AWS_FPGA_MGMTLIB_DIR := $(SDK_DIR)/userspace/lib

ifeq ($(ec2),1)
LDFLAGS += -L$(AWS_FPGA_MGMTLIB_DIR)
LDLIBS += -l$(AWS_FPGA_MGMTLIB)
endif

all : $(EXENAME)

%.o: %.$(CXX_EXT)
	$(CXX) $(CXXFLAGS) $(MYCFLAGS) $(MYCXXFLAGS) -c $< -o $@
	$(CXX) $(CXXFLAGS) $(MYCFLAGS) $(MYCXXFLAGS) -c -MM $< -o $(patsubst %.o, %.d, $@)

$(EXENAME): $(OBJS) $(AWSBM_HAL_LIBNAME)
	$(CXX) -o $@ $(OBJS) $(AWSBM_HAL_LIBNAME) $(LDFLAGS) $(LDLIBS) -lrt

clean:
	rm -rf *.o *.d $(EXENAME)

.PHONY: all

.DEFAULT_GOAL := all
