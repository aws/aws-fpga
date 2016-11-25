INCLUDES = -I. -I../../include -I/usr/include

#OPT=-O2
CFLAGS=$(OPT) -g -std=gnu99  -Wall -W -Wno-parentheses -Wstrict-prototypes -Wmissing-prototypes $(INCLUDES)

LCDLIB = liblcd.a

#SRC = $(wildcard *.c)
SRC = io.c log.c logger-kmsg.c
OBJ = $(SRC:.c=.o)

$(LCDLIB): $(OBJ)
	ar rcs $(LCDLIB) $(OBJ)

clean:
	rm -f *.o *.a 
