TOP = ../..
TOPINC_PATH = $(TOP)
UTILINC_PATH = $(TOP)/utils/include
UTILLCDLIB_PATH = $(TOP)/utils/libs/lcd
FPGAHALINC_PATH = $(TOP)/hal/include
FPGAHALLIB_PATH = $(TOP)/hal/lib

INCLUDES = -I$(UTILINC_PATH) -I$(UTILLCDLIB_PATH) -I$(FPGAHALINC_PATH) -I$(TOP)/include -I../. -I.

#OPT=-O2
CFLAGS=$(OPT) -g  -Wall -W -Wno-parentheses -Wstrict-prototypes -Wmissing-prototypes $(INCLUDES)

LDFLAGS = -L$(UTILLCDLIB_PATH) -L$(FPGAHALLIB_PATH) 
LDLIBS = -llcd -lfpga_hal_mbox -lfpga_hal_reg -lfpga_hal_plat -lrt -lpthread

UTILLCDLIB = $(UTILLCDLIB_PATH)/liblcd.a
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
