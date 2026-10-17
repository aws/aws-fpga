#
# Copyright 2020 Amazon.com, Inc. or its affiliates. All Rights Reserved.
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

SRC = $(wildcard *.c)
OBJ = $(SRC:.c=.o)
FPGADMALIB = $(LIB_PATH)/libfpga_dma.a

all: $(FPGADMALIB)

$(FPGADMALIB): $(OBJ)
	mkdir -p $(LIB_PATH)
	$(AR) rcs $(FPGADMALIB) $(OBJ)

clean:
	rm -f *.o *.d $(FPGADMALIB)

-include $(DEPS)
