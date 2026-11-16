# Selected staged child incidence

Status: UNCOMPILED. Root owns all compilation and publication.

The candidate adds `SharedInvocationTrace.selected_staged_child_invocation`.
It consumes a concrete complete selected invocation, its literal preparation
singleton, and an indexed lookup in that same staged list. It returns the actual
child invocation at that position and the actual remaining tuple invocation.
The completed fragment prefix has the original position as its length.
The result retains the child entry caller, cache, queries, both child indices,
the final tuple endpoint, the assembled fragment, and the final residual cache.

The proof aligns the preparation singleton with the singleton recovered by
`selected_complete_invocation` at line 49. The actual
owner namespace is `SourcePruningEnumerationSharedInvocationTrace`. It then
splits the original staged list and applies `children_done_prefix_invocation`
at line 118 of `SourcePruningEnumerationStagedChildInvocation.lean`.
Both invocations come from the same derivation. The proof does not select a
second occurrence by output equality. Repeated input values retain their
original positions.

The premise on `CachedOwn.prepare` records an actual observed call. The theorem
adds no source, resource, model, callback-result, or future-state premise. It
keeps the policy, all five primitive fuels, width, output type, and reason type.
The action field remains in the staged split. The existing selected interpreter
passes the corresponding node and bucket to `visitChildren`.

The conclusion applies to a complete selected receipt. It does not assert that
unvisited children ran on a stopped path. It does not prove raw alias transport,
target typing, same-position assignment compatibility, or joint historical
completion. Those require separate actual same-branch producers.

`PUBLIC-HEADER.lean.txt`, `SPLIT-HEADER.lean.txt`, and `PROBES.lean.txt` were frozen
before the proof. Their hashes remain equal to `HEADER-FREEZE.json`.
`SOURCE-PINS.json` pins the normal public dependencies. The candidate uses
`autoImplicit false` and the default proof limits. Its probes are appendable.
No compiler, Source edit, Git command, board action, or temporary file was used.
