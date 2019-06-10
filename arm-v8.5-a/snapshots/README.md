# Snapshots of theorem prover definitions

This directory contains snapshots of definitions generated from the Sail
ARMv8.5-A specification in the Lem language, as well as definitions for the
Isabelle and HOL4 theorem provers generated from Lem.  These snapshots are
provided for convenience, and are not guaranteed to be up-to-date.

These snapshots currently cover the base 64 bit instruction set, excluding
floating point, vector, and 32 bit instructions.  The definitions target the
machine word libraries of the provers (via Sail's partial monomorphisation
feature for bitvector lengths).
