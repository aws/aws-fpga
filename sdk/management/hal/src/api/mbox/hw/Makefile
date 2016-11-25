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
