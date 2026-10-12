# Nested constructor execution and normalized-erasure replay

## Full finite nested syntax

`InternedNestedConstruction.Syntax` permits ordinary nodes, unions, scoped
variables, and arbitrary nested smart or raw Mu constructors. An inner
body can read its own variable and each enclosing variable. `build` runs
both normalized probes, reads the actual canonical key, reserves a fresh
identity on a miss, compiles the real body, and completes the record.
The `smart` flag selects source `createMu` cleanup.

The executor uses the existing `makeEdge`, `makeNode`, `makeUnion`, and
`withoutSelfReference` functions. A canonical identity with no completed
payload produces `Outcome.pending`. It does not reconstruct that pending
body or assume that the request is safe. `build_pending` proves that every
such outcome names a real installed identity and absent payload. The
executor terminates by finite syntax recursion; a pending result records
the source readback obligation rather than proving Haskell productivity.

`InternedNestedConstructionGrowth.build_correct` derives canonical cache
validity and growth for every outcome. It includes all nested probe and
body computations and does not require successful completion.

`InternedNestedConstructionReplay.build_replay` proves exact replay for
every successful nested execution after its tables grow. It returns the
same complete immutable record and makes no further state change. The
proof derives both probe replays from the body syntax. A repeated complete
Mu request then reads its earlier record without evaluating the body.
The theorem has no supplied whole-callback stability or key equality law.
`empty_replay` derives the initial cache-validity premise directly.

The initial successful outcome remains explicit. These theorems do not
yet prove that every closed nested input avoids pending-key readback.

## A derived normalized-erasure case

`InternedErasedEdgeReplay.extension` adds an outer-dependent edge whose
other child is EmptyNode. The surviving edge templates are arbitrary.
`makeEdge_references` derives the actual readback's ordered children.
`makeNode_erases` proves that source normalization removes the added edge.

`extension_replay` permits the outer value to change after the earlier
request completes. It derives equality of the complete surviving record.
`normalized_replay` includes the current root self-union filter.
`probes_replay` then derives equality of both actual key probes.
`completed_probe_readback` proves that the repeated key has the earlier
complete payload before body evaluation. `internMu_replay` and
`createMu_replay` return that exact record.

The discarded edge can acquire a new canonical edge key. Thus these
erased-edge theorems preserve the returned records, while permitting
allocations for discarded edges. They do not claim full state equality
when the outer input changes.

This closes the direct empty-child erasure family. It does not establish
all erasure caused by nested binder cleanup, union collapse, or arbitrary
prepared substitution. The general first-execution theorem still needs to
show that a fresh-dependent inner request either retains the fresh outer
reference or reuses a completed request from the earlier probe schedule.

## Checked examples and source comparison

`InternedNestedConstructionExamples` executes three closed programs in the
kernel. The first retains the outer reference in an inner node. The second
erases its outer-dependent edge. Both return closed nodes of Mu depth two.
The third normalizes two nested root self unions to EmptyNode. Their exact
record identities and both counters are checked. `complete_summary_replays`
connects each successful execution to arbitrary later cache growth.

The focused Haskell probe `/tmp/mcfta-nested-constructor-replay.hs` passed in
the repository Nix environment. It checks these three closed programs.
It also prepares an open Mu record, changes its outer binding, and then
replaces another free child with EmptyNode. Both changed bindings return
the same canonical Mu. An enclosing closed construction completes with
Mu depth two. This is executable source evidence, not an extraction proof.

Pinned Lean 4.34.1 builds the examples and exact replay theorem. The isolated
axiom audit permits only `propext`, `Classical.choice`, and `Quot.sound`.
There are no admitted proofs or native-evaluation axioms. No Haskell source
or committed tests changed.
