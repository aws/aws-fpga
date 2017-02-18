#
# Copyright 2015-2016 Amazon.com, Inc. or its affiliates. All Rights Reserved.
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
TOPINC_PATH = $(TOP)/include
UTILINC_PATH = $(TOPINC_PATH)/utils
UTILLCDLIB_PATH = $(TOP)/utils
FPGAHALINC_PATH = $(TOPINC_PATH)/hal
FPGAHALLIB_PATH = $(TOP)/hal/lib

INCLUDES = -I$(UTILINC_PATH) -I$(FPGAHALINC_PATH) -I$(TOP)/include -I../. -I.

#OPT=-O2
CFLAGS=$(OPT) -g  -Wall -W -Wno-parentheses -Wstrict-prototypes -Wmissing-prototypes $(INCLUDES)

LDFLAGS = -L$(UTILLCDLIB_PATH) -L$(FPGAHALLIB_PATH) 
LDLIBS = -lutils -lfpga_hal_mbox -lfpga_hal_reg -lfpga_hal_plat -lrt -lpthread

UTILLCDLIB = $(UTILLCDLIB_PATH)/libutils.a
FPGAHALLIB = $(FPGAHALLIB_PATH)/libfpga_hal_mbox.a $(FPGAHALLIB_PATH)/libfpga_hal_reg.a $(FPGAHALLIB_PATH)/libfpga_hal_plat.a
LIBS=$(UTILLCDLIB) $(FPGAHALLIB)

SRC = $(wildcard *.c)
OBJ = $(SRC:.c=.o)
BIN = fpga-local-cmd

all: $(BIN)

$(BIN): $(OBJ)
	$(CC) -o $@ $^ $(LDFLAGS) $(LDLIBS) 

clean:
	rm -f *.o *.a $(BIN)
