#
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
#

TOP = ../..
include $(TOP)/common.mk

INCLUDES = -I. -I$(TOPINC_PATH)
CFLAGS += -fPIC

# The FPGA_CMD_UNSUPPORTED_FLAGS are unsupported flags that are ignored in F2.
# Uncomment the following line to acknowledge that your application does not depend on the flags.
#IGNORE_DEPRECATION=-DUNSUPPORTED_OPTIONS_ACKNOWLEDGED
CPPFLAGS += $(IGNORE_DEPRECATION)

SRC = $(wildcard *.c)
OBJ = $(SRC:.c=.o)
FPGAMGMTLIB_SO = $(LIB_SO_PATH)/libfpga_mgmt.so.1.0.0
FPGAMGMTLIB = $(LIB_PATH)/libfpga_mgmt.a

LDLIBS = -lrt -lpthread

FPGAAUXLIBS = $(LIB_PATH)/libfpga_pci.a
FPGAAUXLIBS += $(LIB_PATH)/libutils.a
FPGAAUXLIBS += $(LIB_PATH)/libfpga_dma.a
FPGAAUXLIBS += $(LIB_PATH)/libfpga_clkgen.a

# Scratch directory for objects extracted from the auxiliary archives.
AUXOBJ_DIR = .auxobj

all: $(FPGAMGMTLIB) $(FPGAMGMTLIB_SO)

# The auxiliary archives are folded into this output, so a change to any of them must rebuild it.
$(FPGAMGMTLIB): $(OBJ) $(FPGAAUXLIBS)
	mkdir -p $(LIB_PATH)
	rm -rf $(AUXOBJ_DIR)
	mkdir -p $(AUXOBJ_DIR)
	set -e; for library in $(FPGAAUXLIBS); do \
		( cd $(AUXOBJ_DIR) && $(AR) -x ../$$library ); \
	done
	rm -f $(FPGAMGMTLIB)
	$(AR) rcs $(FPGAMGMTLIB) $(OBJ) $(AUXOBJ_DIR)/*.o
	rm -rf $(AUXOBJ_DIR)

$(FPGAMGMTLIB_SO): $(OBJ) $(FPGAAUXLIBS)
	mkdir -p $(LIB_SO_PATH)
	$(CC) -o $(FPGAMGMTLIB_SO) -shared $(OBJ) -Wl,-soname,libfpga_mgmt.so.1 -Wl,--whole-archive $(FPGAAUXLIBS) -Wl,--no-whole-archive $(LDFLAGS) $(LDLIBS)
	ln -sf libfpga_mgmt.so.1.0.0 $(LIB_SO_PATH)/libfpga_mgmt.so.1
	ln -sf libfpga_mgmt.so.1 $(LIB_SO_PATH)/libfpga_mgmt.so

clean:
	rm -rf $(AUXOBJ_DIR)
	rm -f *.o *.d
	rm -f $(FPGAMGMTLIB) $(FPGAMGMTLIB_SO)
	rm -f $(LIB_SO_PATH)/libfpga_mgmt.so $(LIB_SO_PATH)/libfpga_mgmt.so.1

-include $(DEPS)
