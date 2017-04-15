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

TOP = ..
INCLUDES = -I. -I../include -I/usr/include
LIB_PATH = $(TOP)/lib

#OPT=-O2
CFLAGS=$(OPT) -g -std=gnu99 -fPIC -Wall -Werror -W -Wno-parentheses -Wstrict-prototypes -Wmissing-prototypes $(INCLUDES)

UTILLIB = $(LIB_PATH)/libutils.a

#SRC = $(wildcard *.c)
SRC = io.c log.c logger-kmsg.c
OBJ = $(SRC:.c=.o)

$(UTILLIB): $(OBJ)
	mkdir -p $(LIB_PATH)
	ar rcs $(UTILLIB) $(OBJ)

clean:
	rm -f *.o *.a $(UTILLIB)
