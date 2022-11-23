# Sail Arm-v8.5-A

This is a [Sail](https://www.cl.cam.ac.uk/~pes20/sail/) model for a substantial fragment of the Armv8.5-A
instruction-set architecture, based on the Arm XML release (version Arm v8.5 00bet8) at:

https://developer.arm.com/products/architecture/cpu-architecture/a-profile/exploration-tools

(with additional glue code and system register material needed to boot
an OS). The Sail version currently contains all 32-bit and 64-bit instructions.

## Building

This currently requires at least Sail 0.8 from our opam repository, see [here](https://github.com/rems-project/sail/wiki/OPAMInstall) for installation instructions. If building the latest Sail from github note that the default branch which should be used is called `sail2` not `master`.

```
make aarch64
```

will build an executable version of the model by compiling it to C. Due to the size of the model this initial build can be *very* slow, especially as it has optimizations enabled. By default Sail will create a file `z3_problems` which caches queries to z3. This greatly improves the performance on subsequent builds.

## Booting Linux

Linux can be booted on the model. The shell script `boot.sh` contains
commands for automatically doing so

First, it downloads the
[sail-arm-boot](https://github.com/Alasdair/sail-arm-boot) repository,
and uses it to build a tiny bootloader (derived from u-boot), the
device tree blob, and a minimal initramfs. This repository also
contains a config file for the kernel.

Then it downloads Linux 4.14.92 from kernel.org, and builds it using
the previously downloaded config.

To boot linux the Sail model must be built with a file containing a
minimal implementation of the Arm generic interrupt controller (GIC)
which is just sufficient for the timer interrupt, as well as a Sail
init function that loads the device tree blob, kernel, and bootloader
in the model's memory. To do this the model must be compiled as

```
make DEVICES=devices.sail MAIN=mail.sail aarch64
```

Otherwise, the model is configured to load and run elf binaries. The
`boot.sh` script will prompt to re-build the model if necessary.

## Funding

This software was developed by Arm and the University of
Cambridge Computer Laboratory (Department of Computer Science and
Technology) under DARPA/AFRL contract FA8650-18-C-7809 ("CIFV").

This project has received funding from the European Research Council
(ERC) under the European Union’s Horizon 2020 research and innovation
programme (grant agreement No 789108, ELVER).

This software was developed by Arm, the University of Cambridge, and
the University of Edinburgh within the Rigorous Engineering of
Mainstream Systems (REMS) project, partly funded by EPSRC grant
EP/K008528/1.
