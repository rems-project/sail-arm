Note that building the Coq bytecode requires a considerable amount of memory.
It should build on a 40GB machine.  It may be possible to build most of the
model on a smaller machine if the decode functions are removed.

Install a copy of <https://github.com/mit-plv/bbv> (e.g., by installing the
`coq-bbv` coq opam package).  If it's built but not installed, set the
`BBV_DIR` environment variable to the directory containing the built files.
Then run `./build`.

The Coq files were produced with
* `sail` commit `2e892823`, and
* `sail-arm` commit `16ebc4e` from the `coq-experimental` branch, which has
  some manual changes that we will add to our ASL translation in future,
and checked against bbv version 1.1 and coq 8.9.1.
