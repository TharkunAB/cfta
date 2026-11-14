# Explicit occurrence index repair

Status: UNCOMPILED. The root agent owns validation.

The original private check stopped at line 120. Lean could not resolve the
index type for `written[occurrence]?` in the public theorem statement.

This packet makes exactly one source replacement:

```
∀ occurrence sc, written[occurrence]? = some sc →
```

becomes:

```
∀ (occurrence : Nat) (sc : Suspended), written[occurrence]? = some sc →
```

All other source bytes are unchanged. All proof bytes are unchanged. Each
other index used with `getElem?` already has type `Nat` in its binder.
No premise, conclusion, endpoint, provider, or linter setting was added.
The original statement did not elaborate. This repair makes its intended
list occurrence index and element types explicit.

The source and target audit remains in the original frozen packet:

`lean/restart-evidence/20261114-current-prepared-shared-written-path-origins-draft/NOTES.md`

The public candidate remains:

`MicroCFTA.SourcePruningEnumerationSharedSelectedContinuations.ChildDispatch.prepared_terminal_child_written_path_origins`

The full original emitted-root finite completion and compatible assignment
target remains open. Historical clear preservation remains open. This
candidate covers one actual prepared child and its actual shared write.
No Haskell defect or change was established.

No compiler, live source, Git, board, Haskell, or temporary evidence was
changed. The original packet remains unchanged.
