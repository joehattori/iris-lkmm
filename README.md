# iris-lkmm

Rocq/Iris foundations for compositional reasoning about Linux-kernel
concurrency under a selected Linux Kernel Memory Model fragment.

## Development setup

The project uses a repository-local opam switch. The checked-in lock file pins
the development baseline to OCaml 5.2.1, Rocq 9.1.0, stdpp 1.13.0, and Iris
4.5.0.

```sh
opam switch create . ocaml-base-compiler.5.2.1 --no-install
opam repository add rocq-released https://rocq-prover.org/opam/released --switch . --rank=2
opam repository add iris-dev git+https://gitlab.mpi-sws.org/iris/opam.git --switch . --rank=1
opam install . --deps-only --locked
make
```

Run commands through `opam exec -- ...`, or activate the switch in the current
shell with:

```sh
eval "$(opam env)"
```

Useful checks:

```sh
make check
opam list --locked
```

## Feasibility-gate status

The first normal-RCU graph kernel and incremental grace-period prototype are
mechanized, but the gate is **not yet passed**.  The recursive RCU law and a
constructive certificate formulation are equivalent, and the incremental
machine proves snapshot safety without consulting a final graph.  Full
soundness/completeness against the CAT-style `rb` constraint and an Iris
reclamation rule remain open.  See [`docs/feasibility.md`](docs/feasibility.md).

The broad package constraint supports Rocq 9.0.x and 9.1.x. The lock file is
the reproducible, tested development configuration and should be updated
deliberately.
