# Shared writer closure and actual recursive rank

This packet checks the complete affected import frontier. It fixes the
source hashes before and after the build. Audit adds the new modules and
preserves all prior bytes. Every new source packet checks each public
theorem with warnings as errors and records the source hash and axioms.

Run with the existing serial 4 GiB heavy-management cap:

```sh
python3 lean/restart-evidence/20261109-shared-writer-closure-compatibility/check.py
```

The checker locates the repository from its own path. It also runs from
/tmp. memory.max and memory.high must equal 4294967296 bytes.
memory.swap.max must equal zero. The Lean compiler uses one thread.

The actual shared recursive progress measure excludes busy collisions.
Closed inputs exclude references. Weak valid node links exclude absence.
The combined initialized worker succeeds or exhausts outer fuel under
the current resource reservation and nine lower bounds. Sufficient outer
fuel, original-input shared completion, full enumeration, native capacity
and Haskell correspondence remain separate obligations.
No production Haskell source changes occur.
