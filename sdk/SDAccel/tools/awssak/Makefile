EXENAME := awssak

CXX_EXT := cpp
CL_EXT := cl

AR := ar
CXX := g++

CXXFLAGS := -Wall -Werror -std=c++0x

#ROOT1 = $(dir $(dir $(CURDIR)))
#ROOT = $(ROOT1)/..

ROOT = $(SDK_DIR)/SDAccel
HAL_INC := -I$(ROOT)/userspace/include

CXXFLAGS += $(HAL_INC)

AWSBM_HAL_LIBNAME := $(ROOT)/userspace/src/libawsbmdrv.a

ifeq ($(debug),1)
	CXXFLAGS += -g -D_DEBUG
else
	CXXFLAGS += -O2 -DNDEBUG
endif

SRCS := $(wildcard *.$(CXX_EXT))
OBJS := $(patsubst %.$(CXX_EXT), %.o, $(SRCS))

-include $(OBJS:.o=.d)

LDFLAGS := -lstdc++

#$(error $(ODIR))
#$(error $(DIR))
#$(error $(ROOT))

all : $(EXENAME)

%.o: %.$(CXX_EXT)
	$(CXX) $(CXXFLAGS) $(MYCFLAGS) $(MYCXXFLAGS) -c $< -o $@
	$(CXX) $(CXXFLAGS) $(MYCFLAGS) $(MYCXXFLAGS) -c -MM $< -o $(patsubst %.o, %.d, $@)

$(EXENAME): $(OBJS) $(AWSBM_HAL_LIBNAME)
	$(CXX) -o $@ $(OBJS) $(LDFLAGS) $(AWSBM_HAL_LIBNAME)

clean:
	rm -rf *.o *.d $(EXENAME)

.PHONY: all

.DEFAULT_GOAL := all
