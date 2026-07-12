# Prototype scope

The feasibility kernel includes finite event identifiers, read/write labels,
normal-RCU lock/unlock and grace-period labels, program order, abstract
`hb`/`prop`/`pb`, matched nested critical sections, `rcu-link`,
`rcu-order`, `rcu-fence`, `rb`, and `rb` irreflexivity.

The incremental prototype includes fixed concurrent agents and the five
gate-language instructions.  It deliberately excludes values, locations,
`rf`, `co`, `fr`, barriers, dependencies, RMWs, SRCU, locks, the full
LKMM consistency predicate, Iris WP, and the `percpu_ref` case study.
