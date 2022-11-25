#!/bin/sh

set -ex

make -C bbv-1.3
make -C sail-lib BBV_DIR=../bbv-1.3/src/bbv
for f in arm_extras.v armv9_types.v armv9.v; do
  coqc -Q bbv-1.3/src/bbv bbv -Q sail-lib Sail $f
done
