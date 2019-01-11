# Sail Arm-v8.5-A

This is a Sail model for a substantial fragment of the Armv8.5-A
instruction-set architecture, based on the Arm XML release at:

https://developer.arm.com/products/architecture/cpu-architecture/a-profile/exploration-tools

It currently contains all 64-bit instructions.

## Building

This currently requires the very latest [Sail from github](https://github.com/rems-project/sail). Some language features required for this model have not yet been merged into the main sail2 branch, so `git checkout asl_flow2` is required before building Sail.

```
make aarch64
```

will build an executable version of the model by compiling it to C.
