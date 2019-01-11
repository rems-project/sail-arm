DEVICES = no_devices.sail
MAIN = elfmain.sail

AARCH64_FLAGS = -non_lexical_flow -no_lexp_bounds_check -memo_z3 -no_warn
AARCH64_SRCS  = model/prelude.sail model/$(DEVICES) model/aarch64.sail model/aarch64_decode.sail model/$(MAIN)

.PHONY: clean check

check: model/*.sail
	sail -just_check -verbose 1 $(AARCH64_FLAGS) $(OPTS) $(AARCH64_SRCS)

aarch64.c: model/*.sail
	sail -c -O -Oconstant_fold $(AARCH64_FLAGS) $(OPTS) $(AARCH64_SRCS) 1> aarch64.c.tmp
	mv aarch64.c.tmp aarch64.c

aarch64: aarch64.c
	gcc -O2 aarch64.c $(SAIL_DIR)/lib/*.c -lgmp -lz -I $(SAIL_DIR)/lib/ -o aarch64

clean:
	-rm -f aarch64.c.tmp
	-rm -f aarch64.c
	-rm -f aarch64
