# Independent construction, exposure, and Required/Merge review

Reviewed at 2026-10-17T01:39:49.238962+02:00. Result: PASS. No material defect was found. This review made no production change.

The reviewed production files are `SourceCurrentHereditaryConstruction.lean`, `SourceCurrentHereditaryExposure.lean`, and `SourceCurrentHereditaryRequiredMerge.lean`. The manifest records their exact bytes and the supporting source files that this review used.

`Construction.MuStored` is a conditional representation invariant for each completed Mu record. It links the stored body to both exact stored probes. It does not require all resident guards to satisfy the annotation predicate. Physical Facts alone do not establish this invariant for an arbitrary earlier Mu. `Construction.closed` constructs the invariant from its own allowed source build.

Fresh construction derives the actual body annotation before it publishes a candidate. The completion proof splits the current keep-first table into an earlier record and the new candidate. An earlier winner uses its own stored law. Both warm lookup and completion use `InternedProfileHeap.stored_probes` to recover the complete stored probes from physical Facts and availability. They do not identify bodies from numeric IDs alone. Smart cleanup then returns the stored body, Empty, or the same Mu through `finish_annotated`.

The request proof preserves the actual pending state. A reserved key without a completed payload does not supply a result annotation or a successful execution. The source callback runs only on a miss. Its smaller syntax builds and self-reference filter produce their own annotations. No callback result law is an initial premise. Stored substitution uses the actual repaired lexical inputs and replacement environment. Mu unfolding annotates the stored body and the exact self replacement. It does not require either physical probe to be annotated merely to project that body.

`Exposure.collect` follows the supplied completed read. Mu and union visited checks use their actual ordered worklist. A fresh Mu visit constructs the deterministic primitive unfold from the legitimate current semantic and physical facts. Its literal equation identifies the intermediate heap of the supplied read. This primitive construction does not assert completion of the enclosing read. `nodeEdges` preserves the literal ordinary-head fast path. Its fallback uses the original Mu at the returned heap. `head` then applies the actual node constructor to those resident rows.

The local head theorem explicitly requires an available closed queried value. The Required node, children, rows, and requireAll endpoints also require closed queried inputs. They do not prove annotation preservation for arbitrary open Required inputs. Rejected rows disappear. Kept rows retain the original full guard and receive the annotations of their actual returned children. The ordered child and row proofs carry semantic readiness, costs, availability, and the conditional Mu store through the same intermediate heaps.

`RequiredMerge.merge` uses `reads.graph`, which erases the same current memo-aware read graph. The supporting Merge producer derives each candidate's conditional annotation law from the same smaller body Run before publication. It rereads the winner from the current returned memo. An earlier winner uses its own law after exact physical owner readback. The endpoint preserves the physical Merge store and conditional Merge laws. It does not itself claim global memo validity, MuStored retention through Merge, or worker completion.

The annotation premises are local. The proofs do not substitute `Heap P` for local annotations. Uses of `Heap (fun _ => True)` recover existing physical effects without restricting unrelated guard records. Existing semantic, cost, and causal cache invariants remain explicit initial facts.

Validation used the final canonical imports. All 27 public declarations have `#print axioms` and fully explicit `#check @` probes. Six definitions or structures have no axiom dependencies. The other 21 declarations use only the standard Lean dependencies. The final public log contains no warning, error, sorryAx, or truncated signature.

Three imported integration kernels pass with full signatures, proof printing, universe printing, deep terms, and a 10,000,000 pretty-print step limit:

1. `constructed_head_required` starts with allowed source syntax and a finite Needed trie. It constructs its own source build, Head, Required graph, and literal worker StableRun. It derives the final local annotation, conditional Mu store, semantic readiness, costs, availability, and closedness. It has no initial Context, completed graph, callback, or final-result premise.
2. `pending_identity_binder` evaluates the literal raw identity-binder syntax against an initially reserved key with no completed record. It proves the exact pending key and unchanged state. It excludes a successful outcome and retains the stopping Mu store.
3. `actual_required_then_merge` starts with supplied sequential requireAll and Merge reads. Required derives the selected returned input annotation and its physical availability at the same middle heap. The initial physical Merge store grows through that actual prefix. Merge consumes the exact interim global bundle. The result records the composed physical effect and final Merge laws. No global guard heap or desired output annotation is supplied.

The final kernel log has no diagnostics or sorryAx. Failed draft sources and logs remain as diagnostic evidence. The final successful kernel log is `construction-review-kernels-3.log`.

Canonical evidence copies record Construction 1081 jobs, Exposure 1082 jobs, and final RequiredMerge 1110 jobs. The aggregate Audit copy records 2723 jobs and 61833 dependency checks. Those canonical logs replay a historical dependency warning. The three final strict production logs and both imported final probe logs are clean.

These are local construction and completed-read annotation results. The constructive kernel uses existing finite closed head and Required completion theorems. It does not prove general recursive intersection termination, selected-edit completion, full outer completion, machine capacity, a GHC lazy evaluation schedule, or whole-library correspondence. No new Haskell behavior defect was established.
