# Model version

The model boundary is Linux tag **v6.18**, whose annotated tag object is
`f7b88edb52c8dd01b7e576390d658ae6eef0e134` and whose peeled source commit is
`7d0a66e4bb9081d75c82ec4957c50034cb0ea449`.

Pinned sources used by the feasibility prototype:

- [`tools/memory-model/linux-kernel.cat`](https://github.com/torvalds/linux/blob/v6.18/tools/memory-model/linux-kernel.cat)
- [`tools/memory-model/linux-kernel.bell`](https://github.com/torvalds/linux/blob/v6.18/tools/memory-model/linux-kernel.bell)

The prototype transcribes only the normal-RCU definitions listed in
`docs/cat-mapping.md`.  It does not yet use `linux-kernel.def`, the complete
memory model, or the `percpu_ref` sources.  No machine-checked CAT
translation is claimed.
