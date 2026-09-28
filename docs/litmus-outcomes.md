# Litmus outcome validation

The suite checks four message-passing outcome claims with Rocq proofs about
the transcribed LKMM model. Both locations start at zero. The producer
writes `data = 1` and then `flag = 1`; the consumer reads the flag into `r0`
and unconditionally reads the data into `r1`. The tested condition is
`r0 = 1 /\ r1 = 0`.

| Variant | Flag store | Flag load | Proved outcome |
| --- | --- | --- | --- |
| `MP-once-once` | ONCE | ONCE | Possible |
| `MP-release-once` | Release | ONCE | Possible |
| `MP-once-acquire` | ONCE | Acquire | Possible |
| `MP-release-acquire` | Release | Acquire | Forbidden |

The release/acquire case follows upstream's
[`MP+pooncerelease+poacquireonce.litmus`](https://github.com/torvalds/linux/blob/v6.18/tools/memory-model/litmus-tests/MP%2Bpooncerelease%2Bpoacquireonce.litmus).
The Core programs explicitly initialize memory, rename `buf` to `data`, and include
three variants that remove one or both ordering annotations. There are no
branches, fences, RMWs, or dependencies in these programs.

## Running the checks

After installing the repository's locked Rocq dependencies:

```sh
opam exec -- make check
```

This builds all Rocq files, including the graph witnesses and whole-test
Hoare specifications below. CI runs the same checks. No external outcome
comparison is performed, and herdtools7 is not a build dependency.

## Rocq correspondence

`theories/examples/message_passing_code.v` defines the four Core programs.
Locations 0 and 1 are `data` and `flag`; the consumer loads `flag` into
register 0 and `data` into register 1. Both loads are unconditional.

The forbidden outcome is verified through Iris in
`theories/examples/message_passing_wp.v`:

- `producer_wp` and `consumer_wp` apply the shared-location protocol rules to
  each operation. They work for all four combinations of access modes.
- `mp_closed` allocates the location invariants from initialized memory,
  supplies both thread WPs for every consistent candidate, and combines their
  operation receipts using `publication_observed`.
- `mp_release_acquire_adequate` applies `wp_adequacy`: for every accepted
  completed operational execution, the actual final registers satisfy
  `r0 = 1 -> r1 = 1`. This excludes the litmus condition `r0 = 1 /\ r1 = 0`.

### Whole-test Hoare specifications

[`message_passing_hoare.v`](../theories/tests/message_passing_hoare.v) gives
each test an outcome specification over the entire concurrent program.
The trailing-`?` triples state the existential property directly:

```coq
Theorem mp_once_once_possible :
  {{{ True }}} program StoreOnce LoadOnce
  {{{ result, RET result; registers_are result 1%Z 0%Z }}}?.
```

The program includes `data = 0`, `flag = 0`, and both P0/P1 bodies.
`registers_are` reads the actual final registers `1:r0` and `1:r1`; `RET`
returns the trace and final state. With precondition `True`, the proof must
supply an execution from that initialized program.

For release/acquire, the corresponding claim is refuted:

```coq
Theorem mp_release_acquire_not_possible :
  ~ ({{{ True }}} program StoreRelease LoadAcquire
     {{{ result, RET result; registers_are result 1%Z 0%Z }}}?).
```

Their assertions are ordinary Rocq propositions. With a true precondition,
each positive proof supplies a completed operational run, its final `rf`/`co`
obligations, and the final-register outcome. The four variants have these
theorems:

| Variant | Rocq theorem | Outcome claim |
| --- | --- | --- |
| `MP-once-once` | `mp_once_once_possible` | `(1,0)` has a completed execution |
| `MP-release-once` | `mp_release_once_possible` | `(1,0)` has a completed execution |
| `MP-once-acquire` | `mp_once_acquire_possible` | `(1,0)` has a completed execution |
| `MP-release-acquire` | `mp_release_acquire_not_possible` | The `(1,0)` existential triple is false |

The final theorem follows from `mp_release_acquire_never`, which directly
uses the existing `mp_release_acquire_adequate` Iris theorem. Its universal
guarantee `r0 = 1 -> r1 = 1` rules out the litmus condition.

The location protocols constrain emitted writes. They do not assume a latest
readable value, a favorable schedule, or that a reads-from source has already
been emitted. The library in `theories/logic/wp_publication.v` interprets the
receipts at completion using the reusable LKMM publication law in
`theories/lkmm/publication.v`. The universal client proof does not enumerate graphs or
invoke a whole-program forbidden-outcome theorem.
`theories/tests/message_passing_allowed.v` retains the three existential
regressions `mp_once_once_allowed`, `mp_release_once_allowed`, and
`mp_once_acquire_allowed`. Each constructs a `program_graph` with the bad
outcome satisfying every conjunct of `lkmm_consistent`. These tests import
no Iris modules. Operational completeness establishes that consistent program
graphs are realizable up to event-ID renaming; read values are preserved.
The `mp_*_possible` triples reuse these witnesses. An additional Iris receipt
proof connects the generated reads to final registers, so the existential
postconditions concern exactly `1:r0` and `1:r1`, not only graph labels.

The WP result concerns accepted completed executions with the final `rf`/`co`
obligations. It does not claim prefix safety or termination. The protocols
establish this single-writer publication value guarantee; they are not an
API for transferring arbitrary Iris resources through release/acquire.

The tests prove whether this one outcome is possible in the Rocq model.
The allowed proofs give witnesses; they do not enumerate all outcomes.
The upstream-litmus-to-Core transcription remains manual and unverified.
There is no extracted checker or verified litmus parser.

Rocq checks establish properties of the transcribed model; they do not
independently validate its correspondence with upstream. The pinned sources
are linked in [model version](model-version.md), and the manual CAT/Bell
transcription is documented in [the source mapping](cat-mapping.md).
There is no proof of upstream equivalence, and independent transcription
review remains outstanding.
