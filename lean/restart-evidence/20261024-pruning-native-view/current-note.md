# Actual interned-node narrowing and emptiness

Updated: 2026-10-24. Baseline: `4c52896ccff16f4fbf479ac33746b6dbdf438e35`.
Main: `74250bd889685da436cdbfe32ac4b5a0878ffd09`, incorporated.
Proof: `0e231e740dd20edc97b9cdcc49c73f4d4f25132e`.

`SourcePruningNativeView` adds the concrete node view used by pruning.
Its three functions preserve the full symbol, refinement, guard and children
of each retained edge. They use the repaired interned reader and the actual
smart constructor. They retain the actual intermediate and final caches.

The edge filter follows Pruning.hs. A four-child app or two-child filter
tests its annotation only when the complete symbol has the Top refinement.
A one-child edge tests its annotation and complete symbol. Other edges remain.
The theorem treats fits and admits as the source's supplied Boolean functions.
It does not prove a semantic law for either function.

`narrowAt` reads the input, filters those actual rows, then runs makeNode in
the cache returned by that read. Unresolved, pending and exhausted results
retain distinct failure tags and their actual caches.

`narrowAt_complete` assumes initial Ready, Available and no free references.
It derives a finite fuel, the actual exposed rows and intermediate cache,
the actual smart-constructor result and final cache, and successful narrowing.
The final cache remains valid and preserves growth and issued-name history.
The result remains available, closed and ordinary. Its literal rows are exactly
canonicalEdges of surviving selected rows. Every second read returns those
literal rows and the same final cache, including a read with zero fuel.
Larger initial read fuel gives the same narrowing result and complete cache.

The result is empty exactly when every original exposed row fails the filter.
The literal row-isEmpty flag has the same equivalence. The proof uses actual
reader liveness to exclude dead children. It uses the final proper-record
invariant and residency to exclude an invalid ordinary node with no stored rows.
It does not assume the desired empty flag, successful read, final node or cache.

`emptyAt` returns false immediately for Mu and retains its complete input cache.
Every other constructor, including union, follows actual narrowing and a SECOND
actual read on its result and returned cache. `emptyAt_complete` derives the
actual Boolean completion for closed available non-Mu inputs. It retains the
same exposed rows, narrowing result and final cache as its narrowing witness.
`emptyAt_mu` gives the separate literal Mu equation at every fuel.

The final module has 177 lines, three definitions and three theorems.
Strict Lean 4.34.1 checking passes with all linters and warnings as errors.
The installed build passes 557 jobs. Aggregate Audit passes 3679 jobs and
76089 theorem dependency checks. Its one warning is the older unused inputs
warning in InternedFreshOrdinaryClosedCompletion. No new-source warning occurs.
All six elaborated public signatures and three actual axiom reports were read.
Only propext, Classical.choice and Quot.sound occur. Independent declaration,
whole-source and public readback reviews cover the retained contracts.

The original frozen owner proposal has five public names and 75 payload files.
It remains unchanged. A separate declaration gate accepted emptyAt_complete
before its body. Removing its 23-line block recovers the successful 154-line
base source exactly. No earlier executable definition or statement changes.
Two earlier source attempts fail on local-let elaboration and the strict linter.
Their inputs, raw logs and reports remain. The first public readback fails on
an unsupported display option; the successful second attempt removes only that
option. These failures are not reported as successful checks.

H6 remains the strongest combined result. Covered closed construction, valid
initial cache and original guard allocation history derive sufficient mathematical
width and fuel for any finite number of modeled node-call rounds. Empty inherited
payload gives exact finite-tree language equivalence between the input and final
result. The theorem does not include withoutRedundantEdges or assert convergence.
The new narrowing result does not extend that theorem's language claim.

Next connect enumeration node IDs to stored interned Values and cache histories.
Then compose the actual outer type-membership narrow wrapper, holeKey/typing
interpretation and per-call memo2 behavior with typedTypes. The existing callback
and observation proofs do not establish that complete execution by themselves.
Native Text/Formula/interning extraction, practical Int width and resource use,
global helper canonicality, canonical mutation histories, selected-current
protection, cached-driver composition, semantic pruning, phase 4, runtime/solver
correspondence and convergence remain open. H23 stays queued. The full goal is
active and incomplete. Older constructor and equality targets remain preserved.

No Haskell source changes occur in this checkpoint. FINDINGS keeps its external
repair index first. All six recorded Haskell repairs are already on main.
No additional external patch remains for those six defects. Their counterexamples,
original failures, repairs and validation remain available to external work.

Evidence is in restart-evidence/20261024-pruning-native-view. It retains the
frozen proposal, both declaration gates, all source/readback attempts, complete
reviews, capped resource receipts, exact baseline and prior publication receipts.
The verifier checks every baseline blob and mode, nine exact documentation
insertions and one Audit import. Earlier sealed evidence, proofs, counterexamples,
repairs, drafts and the optimized interned core remain unchanged.
