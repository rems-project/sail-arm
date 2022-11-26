# Armv9-A Sail specification

This repository contains a Sail version of the [Armv9-A ISA
specification][ARM_ARM].

The files `instrs{32,64}.sail` and `v8_base.sail` in the `src` directory
contain the AArch32 and AArch64 instruction specifications of Armv9-A and the
necessary auxiliary functions, respectively.  These Sail files are derived from
the 2021-12 version of [Arm's ASL specification][ARM_ASL] using the automatic
[ASL-to-Sail][asl_to_sail] translation tool.  This was done using a snapshot of
ASL files provided by Arm; compared to the version of the specification
[available on the Arm website][ARM_ASL], this snapshot consists of plain ASL
files rather than XML files, and it contains automatically generated glue code
connecting system register accessors and system operations to the instruction
semantics (e.g.  `AArch64_AutoGen_SysRegRead`).

In addition, the `src` directory in this repository contains a number of Sail
files (handwritten, not derived from ASL and not part of the official
specification) that allow the generation of an executable emulator.  In
particular, `step.sail` contains a simple top-level fetch-decode-execute
function, and `impdefs.sail` and `map_clauses.sail` contain some default
choices for implementation-defined behaviour.

## Building

To build artifacts derived from the Sail specification, make sure that a recent
version of [Sail][sail] is installed (last tested using revision `b785601e`),
and use the Makefile target `gen_c` to generate an emulator, and `gen_isa` or
`gen_coq` to generate a model for the Isabelle or Coq theorem prover,
respectively.

The `boot/boot.sh` script downloads, builds, and runs a version of the Linux
kernel above the C emulator.

## License

The files in this repository are licensed under the BSD 3-Clause Clear license
in `LICENSE`, except for the snapshots of the Lem and Sail theorem prover
libraries in the `snapshots` directory, which come with their own license files
in their respective subdirectories.

Copyright (c) 2022 Arm Limited (or its affiliates), Thomas Bauereiss, Brian
Campbell, Alasdair Armstrong, Alastair Reid, Peter Sewell

## Funding

This project has received funding from the European Research Council (ERC)
under the European Union’s Horizon 2020 research and innovation programme
(grant agreement No 789108, ELVER).
This work was supported by the UK Industrial Strategy Challenge Fund (ISCF)
under the Digital Security by Design (DSbD) Programme, to deliver a DSbDtech
enabled digital platform (grant 105694).
This work was supported by Google.

[ARM_ARM]: https://developer.arm.com/documentation/ddi0487/latest
[ARM_ASL]: https://developer.arm.com/downloads/-/exploration-tools
[asl_to_sail]: https://github.com/rems-project/asl_to_sail
[sail]: https://github.com/rems-project/sail
