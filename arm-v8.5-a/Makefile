DEVICES = no_devices.sail
MAIN = elfmain.sail

AARCH_FLAGS  = -non_lexical_flow -no_lexp_bounds_check -memo_z3 -no_warn
AARCH64_SRCS = model/aarch64.sail model/aarch64_float.sail model/aarch64_vector.sail
AARCH32_SRCS = model/aarch32.sail
AARCH_SRCS   = model/prelude.sail model/$(DEVICES) model/aarch_types.sail model/aarch_mem.sail $(AARCH64_SRCS) $(AARCH32_SRCS) model/aarch_decode.sail model/$(MAIN)
AARCH_COQ_SRCS   = model/prelude.sail model/$(DEVICES) model/aarch_types.sail model/aarch_mem.sail $(AARCH64_SRCS) $(AARCH32_SRCS)

.PHONY: clean check

check: model/*.sail
	sail -just_check -verbose 1 $(AARCH_FLAGS) $(OPTS) $(AARCH_SRCS)

aarch64.c: model/*.sail
	sail -c -O -Oconstant_fold $(AARCH_FLAGS) $(OPTS) $(AARCH_SRCS) 1> aarch64.c.tmp
	mv aarch64.c.tmp aarch64.c

aarch64.v: model/*.sail
	sail -verbose 1 -coq -dcoq_undef_axioms -undefined_gen -coq_lib aarch64_extras -o aarch64 $(AARCH_FLAGS) $(AARCH_COQ_SRCS) coq_termination.sail
	patch -p0 < coq.patch

aarch64: aarch64.c
	gcc -O2 aarch64.c $(SAIL_DIR)/lib/*.c -lgmp -lz -I $(SAIL_DIR)/lib/ -o aarch64

aarch64.lem: model/*.sail
	sail -verbose 1 $(AARCH_FLAGS) $(OPTS) -lem -lem_lib Aarch64_extras model/prelude.sail model/no_devices.sail model/aarch_types.sail model/aarch_mem.sail model/aarch64.sail -o aarch64

clean:
	-rm -f aarch64.c.tmp
	-rm -f aarch64.c
	-rm -f aarch64
	-rm -f aarch64.lem
	-rm -f aarch64_types.lem
	-rm -f aarch64.v aarch64_types.v
	-rm -f aarch64.vo aarch64_types.vo aarch64_extras.vo
	-rm -f aarch64.glob aarch64_types.glob aarch64_extras.glob
	-rm -f .aarch64.aux .aarch64_types.aux .aarch64_extras.aux
