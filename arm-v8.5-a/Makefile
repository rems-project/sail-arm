ifeq ($(SAIL_DIR),)
SAIL_DIR:=$(shell opam config var sail:share)
ifeq ($(SAIL_DIR),\#undefined)
$(error Environment variable SAIL_DIR is unset. This variable should either point at the root directory of the Sail repository, or be `opam config var sail:share` if Sail was installed via OPAM)
endif
endif
$(warning SAIL_DIR is $(SAIL_DIR))

DEVICES = no_devices.sail
MAIN = elfmain.sail

AARCH_FLAGS  = -non_lexical_flow -no_lexp_bounds_check -memo_z3 -no_warn -dno_cast
AARCH64_SRCS = model/aarch64.sail model/aarch64_float.sail model/aarch64_vector.sail
AARCH32_SRCS = model/aarch32.sail
AARCH_SRCS   = model/prelude.sail model/aarch_types.sail model/$(DEVICES) model/aarch_mem.sail $(AARCH64_SRCS) $(AARCH32_SRCS) model/aarch_decode.sail model/$(MAIN)
LEM_FLAGS    = -const_prop_mutrec AArch64_TakeException -const_prop_mutrec AArch32_SecondStageTranslate -const_prop_mutrec AArch64_SecondStageTranslate -undefined_gen

.PHONY: clean check

default: aarch64

check: model/*.sail
	sail -just_check -verbose 1 $(AARCH_FLAGS) $(OPTS) $(AARCH_SRCS)

aarch64.c: model/*.sail
	sail -c -O -Oconstant_fold $(AARCH_FLAGS) $(OPTS) $(AARCH_SRCS) 1> aarch64.c.tmp
	mv aarch64.c.tmp aarch64.c

aarch64_128.c: model/*.sail
	sail -c -O -Ofixed_int -Oconstant_fold $(AARCH_FLAGS) $(OPTS) $(AARCH_SRCS) 1> aarch64_128.c.tmp
	mv aarch64_128.c.tmp aarch64_128.c

interactive: model/*.sail
	sail -i -undefined_gen $(AARCH_FLAGS) $(OPTS) $(AARCH_SRCS)

aarch64.smt_model: model/*.sail
	sail -smt_serialize $(AARCH_FLAGS) $(OPTS) $(AARCH_SRCS) -o aarch64

aarch64: aarch64.c
	gcc -O2 aarch64.c $(SAIL_DIR)/lib/*.c -DHAVE_SETCONFIG -lgmp -lz -I $(SAIL_DIR)/lib/ -o aarch64

aarch64_128: aarch64_128.c
	gcc -O3 -flto aarch64_128.c -lgmp -lz -I $(SAIL_DIR)/lib/int128bv64/ -o aarch64_128

aarch64.lem: model/*.sail
	sail -verbose 1 $(AARCH_FLAGS) $(LEM_FLAGS) $(OPTS) -lem -lem_lib Aarch64_extras -o aarch64 model/prelude.sail model/$(DEVICES) model/aarch_types.sail model/aarch_mem.sail $(AARCH64_SRCS) $(AARCH32_SRCS)

translate_address.c: model/*.sail translate_address.isail
	sail -is translate_address.isail

aarch64.ir: model/*.sail signext.sail
	../../isla/isla-sail/isla-sail -v 1 $(AARCH_SRCS) -splice signext.sail -o aarch64

clean:
	-rm -f aarch64.c.tmp
	-rm -f aarch64.c
	-rm -f aarch64
	-rm -f aarch64_128.c.tmp
	-rm -f aarch64_128.c
	-rm -f aarch64_128
	-rm -f aarch64.lem
	-rm -f aarch64_types.lem
	-rm -f translate_address.c
