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

TOP = ..
include $(TOP)/common.mk

INCLUDES = -I. -I$(TOPINC_PATH)
CFLAGS += -fPIC

UTILLIB = $(LIB_PATH)/libutils.a

# sh_dpi_tasks.c is deliberately excluded from libutils.a.
SRC = io.c log.c logger-kmsg.c
OBJ = $(SRC:.c=.o)

all: $(UTILLIB)

$(UTILLIB): $(OBJ)
	mkdir -p $(LIB_PATH)
	$(AR) rcs $(UTILLIB) $(OBJ)

clean:
	rm -f *.o *.d $(UTILLIB)

-include $(DEPS)
