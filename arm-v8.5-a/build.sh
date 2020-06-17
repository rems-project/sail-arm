#!/bin/bash
set -ex
coqc -Q ../../sail/lib/coq Sail aarch64_extras.v
coqc -Q ../../sail/lib/coq Sail aarch64_types.v
env time coqc -time -Q ../../sail/lib/coq Sail aarch64.v 2>&1 | tee time.log

