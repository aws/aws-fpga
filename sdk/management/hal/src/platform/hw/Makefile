TOP = ../../../..
HALTOP = ../../..
TOPINC_PATH = $(TOP)
UTILINC_PATH = $(TOP)/utils/include
UTILLIB_PATH = $(TOP)/utils/libs/lcd
HALINC_PATH = $(HALTOP)/include
HALLIB_PATH = $(HALTOP)/lib

INCLUDES = -I. -I$(HALINC_PATH) -I$(TOP)/include -I$(UTILINC_PATH) -I$(UTILLIB_PATH) -I/usr/include

#OPT=-O2
CFLAGS=$(OPT) -g  -Wall -W -Wno-parentheses -Wstrict-prototypes -Wmissing-prototypes $(INCLUDES)

SRC = $(wildcard *.c)
OBJ = $(SRC:.c=.o)
FPGAHALLIB = $(HALLIB_PATH)/libfpga_hal_plat.a

$(FPGAHALLIB): $(OBJ)
	mkdir -p $(HALLIB_PATH)
	ar rcs $(FPGAHALLIB) $(OBJ)

clean:
	rm -f *.o $(FPGAHALLIB)
