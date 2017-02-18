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

TOP = ../../..
TOPINC_PATH = $(TOP)/include
UTILLIB_PATH = $(TOP)/util
MGMTLIB_PATH = ../lib
FPGAPCILIB_PATH = $(TOP)/fpga_libs/fpga_pci/lib

INCLUDES = -I$(TOPINC_PATH) -I/usr/include

#OPT=-O2
CFLAGS=$(OPT) -g  -Wall -W -Wno-parentheses -Wstrict-prototypes -Wmissing-prototypes $(INCLUDES)

SRC = $(wildcard *.c)
OBJ = $(SRC:.c=.o)
FPGAMGMTLIB = $(MGMTLIB_PATH)/libfpga_mgmt.a
FPGAPCILIB = $(FPGAPCILIB_PATH)/libfpga_pci.a

$(FPGAMGMTLIB): $(OBJ)
	mkdir -p $(MGMTLIB_PATH)
	ar rcs $(FPGAMGMTLIB) $(OBJ) $(FPGAPCILIB)

clean:
	rm -f *.o $(FPGAMGMTLIB)
