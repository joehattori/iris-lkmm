# Project guidance

The [project roadmap](docs/roadmap.md) defines the goals, scope, model
boundary, semantic architecture, main theorems, feasibility gate, validation
plan, and case-study direction. Read it before changing the model, semantics,
logic, or case studies, and follow its scope, trust boundaries, and
feasibility requirements.

# Repository Layout

```text
theories/
  lkmm/
  lang/
  operational/
  logic/
  examples/
  case_studies/percpu_ref/

docs/
  roadmap.md
  scope.md
  model-version.md
  cat-mapping.md
  semantics.md
  trusted-boundary.md
  percpu-ref-mapping.md
```

Move detailed design notes into `docs/` as they stabilize.

# Proof and Engineering Rules

- Keep the relational LKMM model independent of Iris.
- Make every trust assumption explicit.
- Avoid definitions that make soundness or completeness true by construction.
- Preserve dependency provenance syntactically; do not rely on alias analysis.
- Treat CAT-to-Rocq and source-to-core correspondence as separate trusted boundaries.
- Record every deviation from Linux `v6.18`.
- Add a litmus or regression test for every semantic rule.
