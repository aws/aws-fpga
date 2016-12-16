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

TOP = ../../../../..
HALTOP = ../../../..
TOPINC_PATH = $(TOP)/include
FPGADINC_PATH = $(TOP)/fpgad/include
UTILINC_PATH = $(TOP)/utils/include
UTILLIB_PATH = $(TOP)/utils/libs/lcd
HALINC_PATH = $(HALTOP)/include
HALLIB_PATH = $(HALTOP)/lib

INCLUDES = -I. -I$(HALINC_PATH) -I$(TOPINC_PATH) -I$(FPGADINC_PATH) -I$(UTILINC_PATH) -I$(UTILLIB_PATH) -I/usr/include

#OPT=-O2
CFLAGS=$(OPT) -g  -Wall -W -Wno-parentheses -Wstrict-prototypes -Wmissing-prototypes $(INCLUDES)

SRC = fpga_hal_mbox.c 
OBJ = $(SRC:.c=.o)
FPGAHALLIB = $(HALLIB_PATH)/libfpga_hal_mbox.a

all: $(FPGAHALLIB)

$(FPGAHALLIB): $(OBJ)
	mkdir -p $(HALLIB_PATH)
	ar rcs $(FPGAHALLIB) $(OBJ)

clean:
	rm -f *.o $(FPGAHALLIB)
