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

## Current status

LKMM-Core execution uses normal-RCU snapshot waiting and an incremental
graph builder. The builder maintains all five selected LKMM consistency
conditions. Completed coupled runs yield a program graph and LKMM consistency
under explicit `rf`/`co` well-formedness obligations. Conversely, every consistent
program graph has a completed coupled execution up to event-ID renaming, by
[coupled completeness](docs/semantics.md#coupled-operational-completeness).

The Iris layer supports resource tracking and composition of local WP proofs
along accepted executions, with fractional ownership of emitted write histories
and load/store rules that permit reads from later-emitted writes. A client RCU
protocol recovers protected ownership after retirement and a grace period.
[Completed-execution adequacy](theories/logic/adequacy.v) extracts pure trace
and final-state properties from closed program proofs. Safety for arbitrary
prefixes remains open. See the
[WP design](docs/wp-design.md), [semantic architecture](docs/semantics.md), and
[scope](docs/scope.md).

The broad package constraint supports Rocq 9.0.x and 9.1.x. The lock file is
the reproducible, tested development configuration and should be updated
deliberately.
