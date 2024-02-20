CC=gcc

# Attempt to work with either sail from opam or built from repo in SAIL_DIR
ifneq ($(SAIL_DIR),)
# Use sail repo in SAIL_DIR
SAIL:=$(SAIL_DIR)/sail
export SAIL_DIR
else
# Use sail from opam package
SAIL_DIR:=$(shell opam config var sail:share)
SAIL:=sail
endif

all: armv9

armv9: armv9.c
	$(CC) -O2 -DHAVE_SETCONFIG armv9.c $(SAIL_DIR)/lib/*.c -lgmp -lz -I $(SAIL_DIR)/lib/ -o armv9

armv9.c: armv9.c.gz
	rm -f armv9.c
	gunzip -k armv9.c.gz

clean:
	rm -f armv9
