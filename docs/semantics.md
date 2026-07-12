# Incremental RCU prototype semantics

The prototype language has fixed agents and five instructions: `read`,
`write`, `rcu_read_lock`, `rcu_read_unlock`, and `synchronize_rcu`.
It is intentionally smaller than the planned LKMM-Core language.

Each ordinary instruction appends a fresh event.  Lock events are pushed onto
a per-agent stack; unlock events pop the stack and append a matched critical
section.  This handles nested read-side sections syntactically, without alias
analysis.

`synchronize_rcu` has two internal transitions:

1. **Begin** snapshots the lock-event identifiers currently open on the fixed
   agent set.  It emits no graph event and does not advance the program
   counter.
2. **Finish** is enabled when every identifier in that immutable snapshot has
   appeared as the lock endpoint of a closed critical section.  It emits the
   grace-period event, advances the program counter, and stores a certificate.

A reader that starts after Begin is not in the snapshot and therefore cannot
delay that grace period.  A nested reader already open at Begin is a separate
captured obligation.

The proved invariant `operational_soundness` says that every stored
grace-period certificate refers only to sections that have closed.
`finish_gp_complete` proves that discharging the captured obligations is
sufficient to take the finish transition.  Neither theorem invokes
`rcu_consistent` or inspects a completed graph.

## Deliberate limitations

- Reads and writes emit labels but do not yet choose values or construct
  `rf`, `co`, dependency, `hb`, `prop`, or `pb` edges.
- The machine's grace-period certificates are not yet proved equivalent to
  the graph kernel's recursive `rcu_order`.
- There is no whole-graph operational completeness theorem.
- Grace-period liveness is out of scope; a pending grace period may remain
  pending forever.
