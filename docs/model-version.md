# Model version

The model boundary is Linux tag **v6.18**, whose annotated tag object is
`f7b88edb52c8dd01b7e576390d658ae6eef0e134` and whose peeled source commit is
`7d0a66e4bb9081d75c82ec4957c50034cb0ea449`.

Pinned LKMM sources mapped by the current prototype:

- [`tools/memory-model/linux-kernel.def`](https://github.com/torvalds/linux/blob/v6.18/tools/memory-model/linux-kernel.def)
- [`tools/memory-model/linux-kernel.cat`](https://github.com/torvalds/linux/blob/v6.18/tools/memory-model/linux-kernel.cat)
- [`tools/memory-model/linux-kernel.bell`](https://github.com/torvalds/linux/blob/v6.18/tools/memory-model/linux-kernel.bell)

The prototype covers the selected memory and normal-RCU definitions listed
in `docs/cat-mapping.md`, including the mapping from Linux operations to
LKMM-Core instructions. The complete memory model and the `percpu_ref` sources
remain outside the current implementation. No machine-checked CAT translation
or Linux source-to-Core correspondence is claimed.
