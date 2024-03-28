# Armv9-A Sail specification (Sail concurrency interface edition)

This repository contains a Sail version of the [Armv9-A ISA
specification][ARM_ARM],
patched to use the sail concurrency interface.

The file `v8_base.sail` in the `src` directory contains the Sail translation of
the shared pseudocode in [Arm's ASL specification][ARM_ASL], and the files
`instrs{32,64}*.sail` contain specifications of the AArch32 instructions, the
AArch64 base instructions, as well as the AArch64 SVE and SME instructions.

These Sail files are derived from the 2023-03 version of [Arm's ASL
specification][ARM_ASL] using the automatic [ASL-to-Sail][asl_to_sail]
translation tool. This was done using a snapshot of ASL files provided by Arm;
compared to the version of the specification [available on the Arm
website][ARM_ASL], this snapshot consists of plain ASL files rather than XML
files, and it contains automatically generated glue code connecting system
register accessors and system operations to the instruction semantics (e.g.
`AArch64_AutoGen_SysRegRead` in `sysregs_autogen.sail`).

It also contains code that is not part of the official architecture, but allows
the generation of an executable emulator. In particular, `fetch.sail` contains
a simple top-level fetch-decode-execute function, and `impdefs.sail` and
`reset.sail` contain some default choices for implementation-defined behaviour
and initial values of system registers.

There are also handwritten Sail files that were not translated from ASL, like
the `devices.sail` file providing the timer interrupts required by the Linux
kernel, or the `mem.sail` and `interface.sail` files connecting ASL's memory
accessor functions to the Sail memory interface.

## Concurrency interface patch

In order to support the sail concurrency interface and its new outcomes,
we add the `src/interface.sail` file, which provides
instantiations for the various Sail outcomes.

We update `v8_base.sail` to use these interfaces,
adding the outcomes and patching the memory events.
This also involves moving some of the type definitions out of `v8_base.sail`
and we place them in `src/types.sail` so they can be loaded first.

Additionally, we patch some places to allow emulator termination in Isla.

## Building

To build artifacts derived from the Sail specification, make sure that a recent
version of [Sail][sail] is installed (last tested using Sail version 0.17.1),
and use the Makefile target `gen_c` to generate an emulator, and `gen_isa` or
`gen_coq` to generate a model for the Isabelle or Coq theorem prover,
respectively.

The `boot/boot.sh` script downloads, builds, and runs a version of the Linux
kernel above the C emulator.

## License

The files in this repository are licensed under the BSD 3-Clause Clear license
in `LICENSE`.

Copyright (c) 2023 Arm Limited (or its affiliates), Thomas Bauereiss, Brian
Campbell, Alasdair Armstrong, Alastair Reid, Peter Sewell

## Funding

This project has received funding from the European Research Council (ERC)
under the European Union’s Horizon 2020 research and innovation programme
(grant agreement No 789108, ELVER).
This work was supported by the UK Industrial Strategy Challenge Fund (ISCF)
under the Digital Security by Design (DSbD) Programme, to deliver a DSbDtech
enabled digital platform (grant 105694).
This work was supported by Arm and Google.

[ARM_ARM]: https://developer.arm.com/documentation/ddi0487/latest
[ARM_ASL]: https://developer.arm.com/downloads/-/exploration-tools
[asl_to_sail]: https://github.com/rems-project/asl_to_sail
[sail]: https://github.com/rems-project/sail
