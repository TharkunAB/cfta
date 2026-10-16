# Validation of current forest language composition

Frozen source SHA256: `48aaa8d47760e71ac145a7814f811178ea503ad5535f3a8642808ccc054a53d4`.

The focused pinned Lake target completed with exit 0 and 1398 jobs:

```
/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lake -d lean build MicroCFTA.SourceCurrentAllocatedPartialForestLanguage
```

`forest-build-1.log` retains raw output. The only warning is the existing
unused `inputs` warning in InternedFreshOrdinaryClosedCompletion. There
are no new warnings. The canonical slot was released to root immediately.

The imported direct probe also completed with exit 0 and no warnings:

```
LEAN_PATH=lean/.lake/build/lib/lean /home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean lean/restart-evidence/20261016-current-mutual-caller/forest-public.lean
```

Eight public endpoint axiom checks and full signatures pass:
node_unchanged, node_empty, node_union, rows_nil, rows_cons, RowsLaw.exact,
descendants, and ordinary. Five external integrations also pass:
unchanged empty and union branches under inherited contradiction, actual
edge_verified reconstruction followed by the descendant compositor,
actual modify_verified reconstruction followed by the ordinary compositor,
and two literal ordered source rows with both descendant calls.

All 13 axiom probes use only propext, Classical.choice, and Quot.sound.
The printed signatures preserve the exact child trace and constructor
receipt indices. No parent result language law appears among their inputs.

`forest-direct-1.log` preserves the first failed elaboration (union key
type, reserved local identifier, explicit section arguments).
`forest-direct-2.log` is the clean source check. The concatenated source
and independent probes also pass in `forest-public-direct-1.log`.
`forest-source.frozen.lean.txt` preserves the final checked source.

See forest-scope.md for the exact law and remaining recursive obligations.
No older proof, Haskell source, Audit, docs, or Git state was edited.
No compiled artifacts were written in this evidence directory.
