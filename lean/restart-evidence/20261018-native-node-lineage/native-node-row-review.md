# Returned native node row and child lineage

The new module is `SourceCurrentNativeNodeRowLineage`.
The final production SHA256 is `a079b1a2040b24b0180f0063319f67d7f27c8b2fe70c5a349f7825f984ec0064`.
No older production source or frozen evidence changed.

## Exact producer and observation boundary

`Lineage` retains one captured node owner, body entry, body return, and body fuel.
It retains initial Good, NodeReady, the exact original request, and the evaluating handle.
It retains both the actual compileNode trace and its exact compileRows trace.
It retains the evaluating owner at body return and the protected finish trace.
Both captured heaps grow into the actual final reader heap.
Retained maps ready native cells from body return into that reader.

For a selected returned row and ordered child, Lineage retains indexed source rows in both captured operands.
It retains the historical edge writer at the exact edge handle.
It retains the full result symbol and literal conjoined full guard.
Both source child values occupy the same selected child index.
Their historical requestNode call has exact before/after states, fuel, Good at both states, and growth into the reader.
It does not assert that this historical child call occurred inside the current node owner.
A warm edge may have completed its children before that owner started.

`ordinary` consumes an actual returned node cell and the existing causal History.
The captured operands must have their explicit node payloads.
The literal source decision must select the ordinary branch.
The theorem obtains the exact protected writer from WriterReadyRetention.writers.
It reduces compileNode at that branch to compileRows on the captured node rows.
It then invokes NativeReaderRowLineage.rows_child with the writer's actual trace and Retained.
The caller supplies no compileRows trace, internal History, child-origin law, or desired output relation.

`ordinary_body` covers actual ordinary compiler bodies without a node-cell premise.
It consumes an actual completed compileNode trace, initial Good, final-reader History, and exact Retained.
It derives the row compiler trace by the same literal branch reduction.
This endpoint can consume a direct-key request body. It does not prove that such a request completes.

`warm` consumes actual lookupNode memoized and demandNode ready equations.
Physical Good, NodeReady, and KeySafe identify the complete captured request.
The proof excludes a newly inserted suspended cell.
It derives that both chosen and running native states equal the original reader.
It then applies ordinary to that reader's exact returned cell.
No separate key-collision or desired writer assumption is added.

## Own constructed chain

The fixture builds its own closed source with an ordinary leaf and a productive Mu child.
It constructs the cold checked edge trace and its two ordered child self-requests.
It allocates an extra edge and an ordinary parent with an extra unmatched symbol.
The original and wider parents have distinct physical identities.
Their actual node request selects the ordinary branch, consumes the old warm edge, and returns the original parent.
The fixture constructs this full four-step node request and its protected finish.

The first selected child uses ordinary on the newly returned node cell.
The second selected child uses warm with literal lookup/demand equations.
Both yield full Lineage into the exact final reader.
A further one-step warm node request returns the same value and exact full state.
The fixture proves strict physical node and edge allocation from its original constructed heap.
It assumes no caller-supplied future trace, History, completed node, or origin law.
The selected Mu child is a productive stored value, but its historical self-request does not unfold it.
The fixture therefore does not validate recursive Mu body correspondence.

## Verification

The final strict source is direct-4, exit 0, with a raw log of exactly 0 bytes.
Canonical-1 passes 1173 jobs. It replays the unchanged old ClosedCompletion warning.
Public-1 checks all four public declarations with explicit signatures, full proofs, and axioms.
Kernels-2 checks one constructed theorem with its full signature, proof, and axioms.
Both selected groups use all eight required linter/printer settings and #check @.
Neither selected log has diagnostics, printer omissions, or printer failures.
Only propext, Classical.choice, and Quot.sound occur.
Every worker records effective memory.max and memory.high of 4 GiB and memory.swap.max of 0.
The largest recorded peak is 748 MiB in the failed first fixture attempt.
The final fixture peak is 727 MiB.

All source snapshots and raw logs remain unchanged.
Direct-1 and direct-2 failed during namespace and branch-reduction plumbing.
Direct-3 exited 0 but had a nonempty declaration-style warning log. It is not a strict-clean result.
Direct-4 removes that warning without a linter disable.
Kernels-1 failed on a symbol type annotation and an exact heap cast.
Kernels-2 fixes those two fixture statements without a production source change.

## Remaining scope

The returned-cell endpoint is an actual completed-writer consumer.
The direct-body endpoint is an actual completed-body consumer.
Neither endpoint supplies arbitrary native completion or outer recursion termination.
They do not assume NoDeep, a global finite Cap, or whole-forest closure.
Their row relation permits canonical removal and reordering. It does not claim an injective source-row map.
The guard law is literal conjunction of full guards. It does not infer raw equality-field nonemptiness from live guard syntax.
General recursive Mu result alignment and compatibility with all active outer node owners remain separate obligations.
