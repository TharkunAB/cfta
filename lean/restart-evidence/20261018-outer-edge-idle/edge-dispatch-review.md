# Exact edge-memo fault dispatch

## Frozen source and selected checks

The production module is `lean/MicroCFTA/SourceCurrentOuterEdgeMemoFailure.lean`.
Its SHA-256 is `8066eec5ed6361cb00437bd8f1ef4a938cb526a176ef1a65096c537056288bbb`.
The selected immutable source is `edge-dispatch-direct-2.source.lean`.
Its executed strict log has zero bytes and exit code zero.
`edge-dispatch-canonical-1` completed successfully with 1778 jobs.
Its only warning is the unchanged imported warning from `InternedFreshOrdinaryClosedCompletion`.

`edge-dispatch-public-1` independently imports the sole public theorem `failed`.
It prints the complete statement, proof, and axiom report with `#check @` and all eight explicit required linter and printer options.
The hardened checker accepts the pair without omission or printer failure.
The axiom report uses only the standard permitted axioms.
All selected checks record effective MemoryMax and MemoryHigh of 4294967296 bytes and MemorySwapMax of zero.
The runner enforces a five-minute limit and executes immutable numbered snapshots directly.

## Actual contract

The input is a literal outer phase run that fails with `.edgeMemo handle observation` at the exact full caller `after`.
The handle is arbitrary.
The observation is any `FlatMemoThunk.Observation EdgeRequest Edge`.
The result supplies remaining outer fuel, inherited payload, original row, original row suffix, and captured row-entry caller.
It supplies the literal `ExecutionAncestry.Reached` prefix from the original phase to that nonempty row phase.
It also supplies the exact first edge call at that row phase that fails with the SAME handle, observation, and full caller.

No initial semantic Context, physical Good, node validity, edge validity, idle table, completed graph, Reads, or supplied prefix is required.
The proof follows the six literal phase workers by strong induction on outer fuel.
The first failed edge call in an ordered row is the extracted site.
A failure inside descendants prepends the exact completed earlier edge call.
A failure in a row suffix prepends both exact completed earlier calls.
A failure in a walk suffix prepends the exact completed earlier child node call.
Node evaluation prepends the actual evaluating-owner demand.
Other immediate node, binder, inherited, terminal, and exhaustion branches have different outcomes or diagnostic tags.
A failed bind does not enter a finish continuation, so its complete returned caller remains exact.

## Limits

The result extracts a fault site. It does not exclude that fault or prove general outer completion.
It does not infer that every failed outcome retains an idle edge table.
In particular, a failing Parent body can retain an evaluating edge owner while propagating its Parent diagnostic.
The separate successful-prefix idleness producer can be combined with this extractor at its derived row entry.
That later combination also needs the separate edge-dispatch validity argument for absent observations.
This component makes no host scheduling or Haskell execution claim.

## Preserved attempts and evidence ownership

Attempt 1 retains its immutable failed source, full raw log, metadata, and effective resource readback.
It records missing implicit edge-handle arguments in private predicates.
Attempt 2 makes those fixed handle and width arguments explicit and is the strict-clean selected source.
The public theorem keeps the handle implicit and infers it directly from the observed fault.

The manifest uses an explicit allowlist of files.
It pins this source, frozen imported worker and ancestry definitions, and owned `edge-dispatch-*` evidence only.
It does not include root working fixtures, shared selection files, root runner files, or other components' evidence.
No constructed scenario is counted in this fault-extraction component.
