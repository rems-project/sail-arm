# Snapshot of HOL4 definitions of 64 bit ARMv8.5-A

These theories are a snapshot of the generated files for the Sail ARMv8.5-A
model, translated to HOL4 via Lem.  The snapshot covers the base fragment of
the [ARM v8.5](aarch64/) specification, currently excluding 32 bit, floating
point, and vector instructions.  This snapshots is provided for convenience,
and is not guaranteed to be up-to-date.

They only require HOL4; the necessary Lem library files are included.  A recent
checkout of HOL4 from the repository at
<https://github.com/HOL-Theorem-Prover/HOL/> is required.  This snapshot was
successfully built with commit `a0c4fc9e5`, for example.  Some older versions
will fail with a Holdep error due to a lexer bug in HOL that has now been
fixed.
