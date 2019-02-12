# Sail Arm-v8.5-A

This is a [Sail](https://www.cl.cam.ac.uk/~pes20/sail/) model for a substantial fragment of the Armv8.5-A
instruction-set architecture, based on the Arm XML release (version Arm v8.5 00bet8) at:

https://developer.arm.com/products/architecture/cpu-architecture/a-profile/exploration-tools

(with additional glue code and system register material needed to boot
an OS). The Sail version currently contains all 64-bit instructions.

## Building

This currently requires the latest [Sail from github](https://github.com/rems-project/sail). Note that the default branch which should be used is called `sail2` not `master`.

```
make aarch64
```

will build an executable version of the model by compiling it to C.

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
