Note that building the Coq bytecode requires a considerable amount of memory.
It should build on a 96GB machine.  It may be possible to build most of the
model on a smaller machine if the decode functions are removed.

To build it, check out a copy of https://github.com/mit-plv/bbv in this
directory and run `./build`.  It has been successfully tested with Coq 8.9.0.

The Coq files were produced with
* `sail` commit `4bcdbbe`, and
* `sail-arm` commit `041c3c9` from the `coq-experimental` branch, which has
  some manual changes that we will add to our ASL translation in future.
