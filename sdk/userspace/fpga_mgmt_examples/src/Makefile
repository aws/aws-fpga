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
include $(TOP)/common.mk

INCLUDES = -I$(FPGAHALINC_PATH) -I$(TOPINC_PATH) -I../. -I.

LDFLAGS_SHARED = $(LDFLAGS) -L$(LIB_SO_PATH)
LDLIBS = -lfpga_mgmt

# flags for compiling a statically linked version
LDFLAGS_STATIC = $(LDFLAGS) -L$(LIB_PATH)
LDLIBS_STATIC = -lfpga_mgmt -lrt -lpthread

BINS = clear_single_fpga clear_multiple_fpga load_single_fpga load_multiple_fpga prefetch_multiple_afi
STATIC_BINS = $(addprefix static_,$(BINS))
# Direct compile-and-link rules write target-named dependency files.
DEPS = $(addsuffix .d,$(BINS) $(STATIC_BINS))

all: $(BINS) $(STATIC_BINS)

$(BINS): %: %.c
	$(CC) $(CPPFLAGS) $(CFLAGS) -o $@ $^ $(LDFLAGS_SHARED) $(LDLIBS)

$(STATIC_BINS): static_%: %.c
	$(CC) $(CPPFLAGS) $(CFLAGS) -o $@ $^ $(LDFLAGS_STATIC) $(LDLIBS_STATIC)

clean:
	rm -f *.o *.d *.a $(BINS) $(STATIC_BINS)

-include $(DEPS)
