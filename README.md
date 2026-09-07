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
under explicit `rf`/`co` well-formedness obligations. Candidate scheduling is
relative to a compatible completed machine run; unrestricted operational
completeness remains open.

Core replay is proved for individual agents and for whole programs serialized
in any enumeration of their agents. The serialized execution is a completed
Core run, with the original per-agent actions and a single event-ID renaming
preserving the whole final Core state, RMW pairs, dependencies, and RCU
matching. Reconstructing completed snapshot-machine runs remains a separate
completeness obligation.

The relational RCU recursion is proved equivalent to an independent finite
chain. Completed machine grace periods also support a framed Iris completion
update; primitive WP rules and adequacy remain future work. See
[`docs/semantics.md`](docs/semantics.md) for the architecture and proofs, and
[`docs/scope.md`](docs/scope.md) for the current scope and remaining work.

The broad package constraint supports Rocq 9.0.x and 9.1.x. The lock file is
the reproducible, tested development configuration and should be updated
deliberately.
