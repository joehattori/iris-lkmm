# Feasibility-kernel CAT mapping

This is the manual mapping for the normal-RCU subset exercised by the
feasibility gate.  Upstream line numbers refer to Linux v6.18 at commit
`7d0a66e4bb9081d75c82ec4957c50034cb0ea449`.

| Upstream source | Definition | Rocq definition | Treatment |
| --- | --- | --- | --- |
| `linux-kernel.bell:56-68` | nested `rcu-rscs` matching | `critical_section`, `rcu_rscsi` | The graph stores already-matched, nested pairs; reproducing Bell's matching algorithm is future work. |
| `linux-kernel.cat:134` | `rcu-gp = [Sync-rcu]` | `is_gp` | Direct label test, additionally requiring membership in the finite event set. |
| `linux-kernel.cat:136` | `rcu-rscsi = rcu-rscs^-1` | `rcu_rscsi` | Direct inverse orientation: unlock to matching lock. |
| `linux-kernel.cat:144` | `po? ; hb* ; pb* ; prop ; po` | `rcu_link` | Direct relational decomposition using reflexive-transitive closures. |
| `linux-kernel.cat:154-163` | recursive `rcu-order` | `rcu_order` | The six normal-RCU disjuncts are constructors. All SRCU disjuncts are excluded. |
| `linux-kernel.cat:164` | `po ; rcu-order ; po?` | `rcu_fence` | Direct relational decomposition. |
| `linux-kernel.cat:169` | `prop ; rcu-fence ; hb* ; pb* ; [Marked]` | `rb` | Direct relational decomposition. The prototype's `Marked` is restricted to its read/write labels. |
| `linux-kernel.cat:171` | `irreflexive rb` | `rcu_consistent` | Direct predicate. |

The operational graph layer does not redefine these relations.
`link_commitment` stores the four intermediate event identifiers of the
existing `rcu_link` decomposition, and `link_valid_sound`/
`link_valid_complete` prove correspondence in both directions.  The builder's
`bs_seen_rb` monitor is proved extensionally equal to the existing `rb` at
every reachable state; `completed_builder_run_rb_irreflexive` therefore
establishes the same `rcu_consistent` predicate rather than a separate
operational approximation.

`rcu_segment` is an early proof-oriented certificate that retains CAT's
recursive composition structure.  The independent formulation is
`rcu_chain_order` in `theories/lkmm/rcu_obligations.v`.  It contains:

- a nonempty finite list of valid GP or inverse-RSCS atoms;
- an `rcu-link` edge between every pair of adjacent atoms; and
- a signed final balance, with GP worth `+1` and inverse RSCS worth `-1`,
  required to be nonnegative.

`rcu_order_chain_equiv` proves this list/counter predicate equivalent to
`rcu_order`.  Its proof uses a generic word theorem showing that CAT's six
normal-RCU recursive cases recognize exactly the nonempty words whose final
balance is nonnegative.

This mapping has been compiler-checked only as Rocq code.  It has not yet been
differentially tested with `herd7` and has not received independent review.
