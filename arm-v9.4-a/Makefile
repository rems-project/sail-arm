LEM=lem
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

ISLA_SAIL=isla-sail
ISLA_PREPROCESS=isla-preprocess
ISLA_PREPROCESS_CONFIG=../../isla/configs/armv9p4.toml

DEVICES=devices.sail
DEVICES_PATH=src/$(DEVICES)

SAIL_SRCS=src/prelude.sail src/decode_start.sail src/builtins.sail src/v8_base.sail src/sysregs_autogen.sail src/sysregs.sail src/instrs64.sail src/instrs64_sve.sail src/instrs64_sme.sail src/instrs32.sail src/interrupts.sail src/reset.sail src/fetch.sail src/interface.sail $(DEVICES_PATH) src/impdefs.sail src/mem.sail src/decode_end.sail src/map_clauses.sail src/event_clauses.sail src/stubs.sail
SAIL_MAIN=src/elfmain.sail
ISLA_MAIN=src/isla_main.sail
ISLA_SPLICE=src/isla_splice.sail
LEM_SPLICES=$(wildcard src/lem-patches/*.sail)
SAIL_FLAGS=
SAIL_C_FLAGS = -O -Oconstant_fold
# Extra monomorphisation splits
SAIL_LEM_FLAGS = $(file < sail-lem-flags)

all: lem.stamp isabelle.stamp coq.stamp

.PHONY: all clean interactive gen_c gen_isabelle

lem lem.stamp: $(SAIL_SRCS) $(LEM_SPLICES) lem/prelude.lem
	mkdir -p isabelle
	$(SAIL) -dprofile -verbose 1 -memo_z3 -grouped_regstate \
	        -lem -lem_output_dir lem -isa_output_dir isabelle -o armv9 -lem_lib Prelude \
	        -lem_mwords -mono_rewrites -auto_mono -undefined_gen \
	        $(foreach splice,$(LEM_SPLICES),-splice $(splice)) \
	        $(SAIL_SRCS) $(SAIL_LEM_FLAGS) $(SAIL_FLAGS)
	sed -i '/open import Sail2_monadic_combinators/a open import Prelude' lem/armv9_types.lem
	sed -i -f src/lem-patches/ldr1ron_ty0_fixup.sed lem/armv9.lem
	touch lem.stamp

lem/prelude.lem: src/lem-patches/prelude.lem
	mkdir -p lem
	cp $^ lem

gen_isabelle isabelle isabelle.stamp: lem.stamp
	mkdir -p isabelle
	$(LEM) -isa -outdir isabelle -lib Sail=$(SAIL_DIR)/src/gen_lib \
	    lem/prelude.lem lem/armv9_types.lem lem/armv9.lem
	touch isabelle.stamp

gen_coq coq coq.stamp: $(SAIL_SRCS) src/coq_termination.sail
	$(SAIL) -dprofile -verbose 1 -memo_z3 \
	        -coq -dcoq_undef_axioms \
	        -coq_output_dir coq -o armv9 -coq_lib arm_extras \
	        -undefined_gen \
	        $(SAIL_SRCS) $(SAIL_FLAGS) \
	        src/coq_termination.sail
	touch coq.stamp

c/armv9.c: $(SAIL_SRCS) $(SAIL_MAIN)
	mkdir -p c
	$(SAIL) -dprofile -verbose 1 -memo_z3 \
		-c $(SAIL_C_FLAGS) $(SAIL_FLAGS) $(SAIL_SRCS) $(SAIL_MAIN) > c/armv9.c.temp
	mv c/armv9.c.temp c/armv9.c

gen_c c c.stamp: c/armv9.c
	$(CC) -O2 -DHAVE_SETCONFIG c/armv9.c $(SAIL_DIR)/lib/*.c -lgmp -lz -I $(SAIL_DIR)/lib/ -o c/armv9
	touch c.stamp

gen_ir ir/armv9.ir: $(SAIL_SRCS) $(SAIL_MAIN) $(ISLA_MAIN) $(ISLA_SPLICE)
	mkdir -p ir
	$(ISLA_SAIL) -v 1 -mono_rewrites $(SAIL_SRCS) $(SAIL_MAIN) $(ISLA_MAIN) -splice $(ISLA_SPLICE) -o ir/armv9

gen_irx ir/armv9.irx: ir/armv9.ir
	$(ISLA_PREPROCESS) -A ir/armv9.ir -C $(ISLA_PREPROCESS_CONFIG) -o ir/armv9

interface_types.sail: $(SAIL_SRCS)
	$(SAIL) --slice-instantiation-types -o interface_types.sail.in $(SAIL_SRCS) $(SAIL_FLAGS)
	grep -v '^\(\$$\|default Order\|infix\)' interface_types.sail.in > interface_types.sail
	rm interface_types.sail.in

interactive:
	$(SAIL) -i -memo_z3 -verbose 1 \
	        $(SAIL_SRCS) $(SAIL_FLAGS) \
	        src/coq_termination.sail

clean:
	rm -f lem.stamp lem/arm.lem lem/arm_types.lem
	rm -f isabelle.stamp isabelle/Arm_lemmas.thy isabelle/Arm.thy isabelle/Arm_types.thy \
	  isabelle/Prelude.thy isabelle/ArmAuxiliary.thy
	rm -f coq.stamp coq/{arm_extras,armv9,armv9_types}.{v,vo,vok,vos,glob}
	rm -f ir/armv9.ir
	rm -f interface_types.sail
