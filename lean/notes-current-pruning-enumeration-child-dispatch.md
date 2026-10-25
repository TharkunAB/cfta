# Native child dispatch and terminal protection

## Current source

`SourcePruningEnumerationChildDispatch` adds 174 lines.
Proof: `3a01c37c06b74d313f509b38166671fb7e9d83dd`.
`SourcePruningEnumerationCachedFoldCompletion`, `CachedTerminal` and
`CachedTerminalAdapter` have stronger proof receipts.
Proof: `ea425d8d9076ee8f1d09698c6ee508134a20289d`.
No existing runtime definition changes.

The checkout starts clean at the pushed `8172ef15a` checkpoint.
`git pull --ff-only` reports Already up to date. Main stays
`9d4e4d584aa7a681f075790e98466afe7531838a`.
Native Haskell sources and all earlier evidence remain unchanged.
The Haskell repair handoff stays first in root `FINDINGS.md`.
No new Haskell repair or runtime test suite is added.

## One-child dispatch

`observe` rejects Empty before partition or effects. Otherwise it uses the
actual ordered terminal partition. A nonterminal bucket uses the existing
`ShallowChild.prepareChild` action. A terminal bucket uses `Terminal.run`,
with only the descendant partition as the incoming suspended list.

`run` follows the same dispatch. The nonterminal branch observes the original
action once and attaches a `CachedPrepare` candidate. A missing candidate
does not remove or change the observation. The terminal branch delegates
once to `CachedTerminalAdapter.run` at the current caller and cache.
The partition retains order and duplicates.

`erase` preserves the complete original observation at every fixed bound,
without admission or success premises. `terminal` identifies the complete
terminal adapter result at every fixed bound, including Empty. `empty`
records the early rejection. `nonterminal_complete` derives the original
singleton raw result, fresh child and maintained cache invariants from
genuine input coherence, availability, closedness, storage, realization,
roots, counts, flags, variable bounds and nonterminality.

Existing `CachedStages`, `CachedEdge` and `CachedBranches` retain their
partial behavior. They stop at unsupported terminal children. Their old
fixed-heap and unchanged-forest theorems do not describe the new terminal
path. The new dispatcher is the one-child operation for a richer traversal.

## Terminal fold frame and safety

`CachedFoldCompletion.complete` now also gives exact value equality for
every slot outside the processed source list and different from the target.
Its existing proof already has the actual two-slot assimilation effect.
No-op and rejection cases use identity. Recursion composes the two frames.
The proof keeps its original dispatcher completion per head and its one
recursive completion. It adds no desired endpoint premise.

`CachedTerminal.complete` derives the outside-recorded frame from the
winner's membership in the recorded list. Successful folding restores
`Safe` from the original `Safe` state and actual prefix/fold receipts.
The proof treats the winner, recorded losing roots and unrelated slots
separately. It uses actual loser elimination and the exact merged root map.

`CachedTerminalAdapter.complete` transports the frame through compression
and the winner-only incoming write. It gives `Safe resultCache.core` when
the raw terminal result is nonempty. It uses the actual after-write cache.
The outer read state and moved waiting table remain separate observations.
Incoming Empty writes handle zero before rejection. It is separate from
fold rejection. The latter can retain live losing slots after prefix unions,
so no unconditional safety result is asserted for every rejected cache.

`CachedTerminalAdapter.protects` derives `EnumerationDriver.Protected` from
the recorded-root equation, winner membership, exact merged root map and
outside-recorded value frame. Initial held-root identity and `Avoids` show
that the held root is absent from the recorded list. The result keeps the
held slot, its root and its complete equivalence class. Completion exports
this result for every separate held root at the actual result cache.
It applies in both the fold-rejection and completed-fold branches.

Every earlier completion premise and conclusion remains. In particular,
current conditional numeric-range admission remains. The proofs add no
`Graph` correspondence, final safety assumption, native query or second
completion producer.

## Verification

All source checks use Lean 4.34.1 with `warningAsError=true` and
`linter.all=true`, under serial 4 GiB caps with no swap.
Child dispatch, the strengthened fold and the terminal consumer each pass
their first strict check with an empty log. The adapter's initial safety/
frame extension also passes. Adding held-root protection then fails on a
reserved identifier and two missing explicit contradiction steps.
The corrected final adapter passes strict attempt 3 with an empty log.
All complete failed and successful Lean inputs and raw logs remain.

The first installed child build passes with 1322 jobs. After strengthening
its dependencies, the final installed build also passes with 1322 jobs.
These are different dependency states, not repeated checks of one state.
The focused fold and terminal installations pass with 1314 and 1316 jobs.

The first public wrapper has a Python parenthesis error before Lean starts.
Its source remains. The corrected wrapper passes, but its initial display
omits deeply nested type output. A separate readback enables `pp.deepTerms`
and raises only the pretty-printer step limit. The full public log has
1271 lines and 136083 bytes, with no display omission. It includes ten
public declarations. All actual axiom sets are subsets of `propext`,
`Classical.choice` and `Quot.sound`. The new `protects` theorem uses only
`propext` and `Quot.sound`. Production proof limits stay unchanged.

The aggregate Audit passes with 3734 jobs and 76553 theorem dependency
checks. The older unused `inputs` warning remains unchanged. Independent
source reviews accept the child dispatch, stronger fold and terminal
receipts, and final held-root protection. Evidence is retained under
`lean/restart-evidence/20261025-child-dispatch-terminal-protection`.

## Next target and limits

Build the ordered child traversal around the new dispatcher. Recurse at
the successful raw-row core and the post-child cache, with reached caller,
queries, roots and waiting. The outer observation is a staging receipt.
It can retain the before/read core and before/moved waiting. Using it as
the next child state can remove a write or retain stale waiting counts.

A missing cache candidate must not become rejection or permit continuation
with stale waiting. Admitted completion provides a cache. An arbitrary-bound
continuation needs an explicit partiality or recovery policy. Alternatives
must start at the same parent state. Record residual obligations after
all children succeed.

Compose held-root protection across allocations, ordinary children and
terminal children. Derive safety and later-child input admissibility on
successful paths. Then connect `Finalize.complete` to the original captured
raw target. Do not substitute the terminal winner as the finalization target.
The audited nonterminal stored-bucket history is still a proposed global
invariant. It is not needed as an extra premise of the new terminal result.

H6 remains `SourceCurrentColdFiniteWarmCalls.constructed_node_calls`.
Covered closed construction, a valid initial constraint cache and original
allocation history support prescribed finite modeled node-call rounds with
empty inherited payload, at derived sufficient mathematical bounds. The
final available value has exactly the original finite-tree language under
the formal formula and entailment semantics. Arbitrary mixed calls,
initial-only numeric admission, whole typing/pruning, concrete solvers,
extraction, physical maps and machine integers, practical resources,
convergence and full driver/Haskell correspondence remain open.
