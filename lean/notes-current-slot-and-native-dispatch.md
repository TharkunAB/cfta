# Actual dispatch, changed-slot transport and fold certificates

Dispatch source: `14e7fa6d7494e65a301d9f0b5fc6bc64d6292160`.
Slot source: `bcd4a68303df554b8efe05839ac218c597a42e47`.
Fold source: `a5a174707fe610082b61e1fb501f74f99b7d351d`.
Branch: `formalize`. Main: `bd5a406a6a3f84b7e3ae0906082783911509df83`.
The full original-input objective remains open. Work continues.

## Actual dispatch

SourceCurrentAllocatedNativeStoredDispatch exports dispatch_native_stored.
It covers the literal Dispatch.dispatch result for every native fuel, p and h,
both checkEmpty settings, all source/target slots and every actual outcome.
Its entry gates are current ClassScan.Ready, PendingRealized, Fits/Room and
separate native Stored. It needs no supplied operand availability or closedness.
Both actual decoded operands get those properties from their original slot
lookups and PendingRealized. Fits.room gives the three current counter bounds.
The actual empty-domain query uses the checked execute_stored law.
All five native outcomes retain their own reached state certificate.
A private after_query_stored lemma handles the exact optional EnabledEmpty
continuation and Caller.advance. No future Trace, Ranges, WordRanges,
output Stored, completion receipt or postcondition supplier is added.

## Actual false check and changed slot action

SourcePruningNarrowSlotTransport exports two laws.
checkRepeated_false_frame derives the complete Frame from an actual successful
false recursion check and current UnionFind.Total. It covers every fuel.
The check's slot-writing branch returns true and cannot satisfy this observation.

prepare_changed_success_stores_normal follows these EXACT observed endpoints:

1. getValue succeeds on before and returns a pending old handle at readAfter.
2. checkRepeated succeeds with false from readAfter to checked.
3. The old handle actually decodes to value in heap.
4. prepare actually returns result, some action, and nextHeap.
5. result actually encodes to newHandle, and newHandle differs from oldHandle.
6. That action succeeds on checked and returns final.

Current RequiredCache.Ready, PendingRealized and UnionFind.Total remain inputs.
The actual read, false check, decoded, prepared, newEncoded, changed and succeeded
equations remain inputs. They are observed facts about these stages.
The theorem does not extract those equations from a final runPrefix result.

The proof derives OLD availability, closedness and encoding internally.
It derives the read frame, false-check frame and representative reread frame.
It derives the same allocated representative and the actual old slot there.
It follows the exact changed action and proves the final setValue shape.
The final slot contains the returned newHandle with the captured SCS list.
The new heap retains Keeps, and result is available, closed, ordinary and
physically Normal. Its new handle reads back to exactly that result.
Every remaining complete edge passes the actual root filter.
If the OLD source root is ordinary, every new complete edge is an old edge.
Ordinary here permits recursive children. It restricts only the root.
PendingRealized holds for the final enumeration state in the new heap.

Result Normal derives from changed preparation and actual returned control.
OLD input Normal is neither assumed nor proved.
No historical makeNode, supplied Frame, old encoding or future Trace is needed.
The actual action starts at the false-check output. No writer is omitted
between those two supplied endpoints.

The literal runPrefix singleton-action-success branch uses this same endpoint.
The theorem stops at its observed action state BEFORE narrow adaptation,
index-cache attachment and Right recording.
It does not prove global source lineage or a whole-worker numeric bound.
Other branches can replace the source and need their own laws.

## Every actual fold outcome

SourceCurrentAllocatedNativeStoredFold exports fold_native_stored.
It covers the actual Fold.run result for every n, p and h, both checkEmpty
settings, every supplied finite source list and every returned outcome.
Its entry gates are the existing current Seed, Formulas/Entailment/Inventory,
Context, PendingRealized, pending target, selected PendingOrEliminated sources,
Fits, Reserved over sources.length, known alphabet heap, and entry native Stored.
Reserved is the existing numeric Room condition over the finite forecast prefix.
It is not a future output certificate, Ranges or Trace supplier.
The theorem does not derive that reservation from every original public input.

The induction cases the actual dispatch result and derives reachedStored BEFORE
it splits the result tag. Every early return uses that same reached state.
This covers dispatch error, no action, empty action results, an error first
result, and multiple action results.
Only an actual singleton-success action result recurses.
Existing observed_singleton derives successor Context, Realized, pending target,
selected tail, Fits, known heap and query relation for that ACTUAL successor.
The existing reservation supplies its own tail.
The induction uses those derived entry facts and the head's derived native
Stored. No future Ranges, per-step Stored, function supplier or completion
witness is added. Context.stored still concerns the separate merge memo.

## Meaning of native Stored

Stored is the existing conditional structural property of returned memo cells.
If a request has seen=[] and both operands are recursively finite ordinary
values, its returned result has that domain and height at most each operand.
The domain excludes Mu, Union and references at every descendant.
A false antecedent is vacuous only for that request's certificate.
These laws preserve the reached caller's native tables.
They give no unrestricted returned-root semantics, full caller table invariant,
inner worker certificate, or Haskell correspondence.

## Repairs and Haskell findings

The dispatcher draft needed two local reductions before nested case splits.
Its public and private header text remains exact.
The slot draft used rfl patterns that removed a state name used later.
Root retained explicit get-success equations and rewrote the actual continuation.
Root added open InternedEdgeResidency so nodeEdges resolves to the intended
canonical complete-row function. Its source header TEXT remains exact.
The failed original V1 had no valid elaborated header. It must not be described
as an already typed contract. Public output confirms the canonical constant
and contains no spurious nodeEdges argument.
Root also replaced the deprecated if_neg alias and renamed a constructor-like
unit binder. A Root indentation mistake in the second probe was repaired.
The Fold draft passed its first strict probe without proof changes.
Installed sources remove only their historical source-only status lines.
All failed probes, original drafts and checked repairs remain.
The independent review recovered a multiline-header extraction failure.
That metadata incident changed no source or theorem.

No Haskell source changed. No native command ran.
No new Haskell defect, fix or candidate is established.
All 835 native input hashes remain exact.
All older conditional FINDINGS entries remain complete.

## Strongest whole-worker statement and remaining work

For each supplied finite recursive depth under the original entry and resource
gates, both modeled workers have a stable actual outcome, exact forecasts and
actual paths in one finite original carrier independent of that depth.
Work bounds, forecasts and Reserved can depend on depth. Exhaustion is allowed.
No common successful outcome over all depths is established.
The seed alphabet remains a subset of the original alphabet.
The original-carrier, recording, memo, replay, Normal and local numeric
changed-filter results remain exact.

Sufficient ORIGINAL depth for the intended ordered finite prefix remains the
largest gap. Cover every earlier alternative and staged child under the
configured order and stops. Extract the observed stages from the actual worker.
Compose actual filter histories across adaptation and recording.
Bound source replacements, incoming/dispatch intersections, Prepared Mu/Union
work, slot creation, unchanged calls and raw SCS multiplicity and work.
These local transport laws do not yet give the complete worker bound.

The next native target is actual Terminal.run with its existing current entry
gates plus native Stored. Existing prefix/fold post and resource producers
supply the later entry facts; no future supplier should replace them.
A complete 152-line source draft remains UNCOMPILED in next-terminal-review.
Its SHA256 is cf9f3fc9a74c60782ada2c68bc3c85abb2a0c847cbefbfbab739d02210e09bc6.
A complete 63-line adapter corollary remains UNCOMPILED in next-slot-adapter-review.
Its SHA256 is 8f6888be0194b85f6e03414e775e5a8c2b5337f080f80d6c0c32339ca12a8258.
It transports the current slot postconditions to the actual attached core.
Existing adapt_core already supplies that exact core identity.
Existing recordTypes_inr is pure and does not reset that core.
The adapter None branch stops the narrowed prefix before candidate/Right stages.
It is not a restart. Actual final-prefix observation extraction remains open.

Keep original public inputs, sound outputs, both workers, the optimized core,
Prefix/table/count/checkpoint/public adapters and Haskell correspondence.
Keep constructor/equality, exact node counts, size order and rank/unrank.
Haskell Word64, interner, container, laziness and warm-CAF correspondence remain.
No completion percentage or date is established.

## Verification and restart evidence

Default and strict Audit pass: 4,758 jobs and 83,054 dependency checks.
Nineteen serial compiler commands remain: fifteen pass and four repaired
candidate probes fail. All 52 input snapshots remain.
All three sources and Audit match their final strict snapshots.
Installed strict source logs are empty. Lean4.34.1 uses warningAsError and
linter.all. Every command verifies 4 GiB maximum/high, zero swap and five minutes.
Default Lake replays only the existing unused-input warning.
No cap, queue, heartbeat or service setting changed.

Public readback passes 1,223 checks and 118 definition prints.
All four new axiom reports use standard axioms.
All prior 4,895,021 output bytes remain an exact prefix.
The intermediate 4,902,860-byte output also remains an exact prefix.
The final new tail has 10,211 bytes and 137 lines.
Full output has 4,905,232 bytes, SHA256
`880a139e02bcad10fe1275f5927c2ff0565bd4f74f37038a28502df382b847ab`.
All 556 prior protected and 835 native inputs remain exact.
There are now 559 protected inputs and 4,758 Lean files.
Three Audit imports precede the complete prior body.
Root and independent review read all 413 source lines and 137 public lines.
All public signatures match their intended source contracts.
Complete owners, reused providers, provenance and failed versions remain.

Evidence: /tmp/mcfta-slot-and-native-dispatch-control-20261031.
Archive: lean/restart-evidence/20261031-slot-dispatch-fold-control.
Use safe extraction into a fresh directory and remove restored write bits.
Give metadata verifiers a writable output directory.
All previous root documents remain complete exact suffixes.
The backend marker remains blocked despite user-resumed verified work.
No pause or completion is claimed. Work continues.
