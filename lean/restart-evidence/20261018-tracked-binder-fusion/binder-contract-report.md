# Exact binder contract counterexample

The current all-Context binder conjecture is false. The selected kernel proof refutes both `SourceCurrentBoundedFilteredFusion.Fusion 0 (.binder true body)` and `SourceCurrentTrackedFilteredFusion.Fusion 0 (.binder true body)`. It also proves the tracked law for the strict ordinary source body and the vacuous uniform hypothesis at every rank below zero. No production definition or theorem was changed.

This countermodel is an artificial cache admitted by the current hypotheses. It does not assert that the cache can arise from actual source construction from empty. It does not identify a Haskell defect. Existing checked empty, variable, node, union, writer-conditional, and BinderFree theorems remain intact.

## Exact checked construction

The source body is `node [7(false)[var1,var2]]`. It ignores the binder local. Its first two external captures are sentinel references 10 and 11. Actual source callbacks construct the canonical Depth and ordinary probes `node [7(false)[ref10,ref11]]`.

A fresh Mu reservation uses that real probe pair. Actual ordinary source construction separately constructs the body with two rows `7(false)[ref10]` and `7(false)[ref11]`. The generic `complete` operation installs that body under the reserved Mu key. This is the single non-source-owned combination. The complete body's original opaque profile, free-name set, depth, deep-name set, and open depth satisfy every decoded heap invariant required by Context and Ready. Cache coherence constrains the Mu entry and probe key but does not constrain the body's source origin.

Every required Ready field is proved: Facts/coherence/cached children/linked rows, Live/Flat/proper/nonempty-member invariants, ProfileHeap, FreeHeap, DepthHeap, complete coverage, and OpenDepthReadback. The free and deep summaries compare sets, so the duplicate reference occurrences in the decoded probes are harmless. These are derived local invariants, not Ready assumptions.

The actual first smart binder call hits the resident Mu and returns the two-row ordinary body. The second actual smart binder call uses external sentinels 20 and 21 and constructs its genuine one-row body. Both keys coexist in the same cache. This avoids the invalid approach of transporting conflicting complete payloads for the same key into one common reader.

The first map resolves 10 to Empty and 11 to bare reference 30. The second resolves 20 to Empty and 21 to that same bare reference 30. Both maps satisfy Replacements. The two symbolic lexical slots satisfy the original Paired Empty contract. Source-scoped aliases and self tests are proved, with common root-filter name uninterned 1000. Both actual raw smart results have depth zero.

Two literal stored executions run sequentially. The first retains row `7(false)[ref30]`; the second returns Empty. Their derived Keeps receipts produce a common final Ready reader. Literal replay makes both stored calls warm there. The raw builds, raw-to-reader growth, source Contexts, raw availability, root filters, maps, Paired slots, and all remaining exact Fusion premises are proved. Applying the conjectured old bounded law would give false=true. The tracked law is refuted through its checked exact `to_empty` adapter.

The public constructed theorem contains no future result, source history, desired observation, or output Empty premise. It proves that a strict-body source law and all lower original-depth laws do not suffice for the current unrestricted binder contract.

## Missing causal input

`SourceCurrentConstrainedCapSourceHistory.Context` at lines 23-27 contains only the earlier semantic Context and DepthHeap. The earlier Context at `InternedFreshOrdinaryContext` lines 19-23 contains Normal, Values, ProfileHeap, and FreeHeap. Source origin is a separate `SourceCurrentConstrainedCapSourceHistory.Heap` at lines 87-89. Its source preservation theorem requires that heap initially. Ready adds complete coverage and open-depth readback, but adds no origin or issued path.

`SourceCurrentNativeMuIssuedWriters.writers` at lines 60-65 explicitly returns either initial presence or an actual Written receipt. A path from an arbitrary Context heap cannot eliminate initial presence. `from_empty` at line 109 eliminates it only for a real issued path rooted at empty. The current Fusion contract contains no such path. Grows retains complete records; it does not create writer provenance or preserve orphan issued entries by itself.

A sufficient input for the selected-writer route is a final-reader `Nonempty (NativeMuIssuedHistory.Path empty reader)`, or an appropriate actual Written-to-reader receipt for each selected Mu key. Then actual request inversion and forward raw-heap-to-reader growth transport the complete selected record to that reader. `from_empty` recovers its actual earlier writer. A bare Origin predicate alone retains no reader growth or issued suffix and does not directly supply the existing writer replay adapter.

This is a proposed causal contract, not a silent strengthening of the existing definition. The counterexample remains a checked negative result for the exact old and tracked definitions.

## Minimum remaining proof chain after an explicit causal repair

1. Invert both actual binder source calls into Depth/ordinary callbacks, selected request record, and literal smart finish. Keep both original raw results, captured environments, full probe fields, and exact states.
2. Derive actual selected earlier writers at the common reader from causal input. Use `Written.raw_contexts` or `TrackedWriterFusion.publication` to derive full lexical reader Contexts, actual raw/filter warm calls, availability, and issued suffixes. Keep earlier writer syntax independent of the current requester.
3. Choose one available marker absent from the finite resolved leaf profiles. Extend the marker list and derive local slot relations under the shared sparse maps. A freshness or result-profile law cannot be assumed for future outputs.
4. Apply genuine source-body and chronological writer induction to relate each selected stored body under its own marker substitution to its actual ordinary probe under the corresponding marker substitution. Relate the current requester ordinary probes through the strict current source-body hypothesis. Exact selected ordinary probe fields connect the current requester to the earlier writer.
5. Handle raw closed Mu literals separately: their stored encode shortcut remains literal and opaque. For open Mu plans use `StoredMuTrackedProfile.complete/open_execute` to construct strict-body calls and obtain the full profile after marker erasure. Compose exact mask/erase transport. This step retains the outer lower operation.
6. Derive smart used/unused, bare-self, and root-filter branches from actual decoded/source facts. Do not substitute RootMatch or metadata equality for the needed reconstruction relation.

There is a second rank obstruction even after adding causal provenance. Smart-unused finish can return an ordinary raw result of depth zero while the selected candidate Mu has depth one and its original stored body has depth zero. Thus the earlier writer body depth need not be strictly below the returned raw depth bound. The current syntax-body hypothesis covers the current body, not an arbitrary earlier writer body of different syntax. A chronological selected-writer induction or another explicitly proved stronger invariant is needed for that case. A candidate Mu's body-depth decrease alone does not solve it.

## Source pins

- Exact tracked Fusion contract: `SourceCurrentTrackedFilteredFusion.lean`, SHA256 `dd4f3b302ff195290b80f92f35e6141ab5fd9beff7f37c14c86e2f26b051e7cf`.
- Context versus separate source-origin Heap: `SourceCurrentConstrainedCapSourceHistory.lean`, SHA256 `123cae4b1815144531954e1e2ed246963f0325d54a06a5039d09694326e4a315`.
- Ready fields: `SourceEqualityRequiredCache.lean`, SHA256 `7cfdad372cba5716c4dc32a7097af8060a27e903fe334f89a2062757b664a733`.
- Actual issued writer recovery: `SourceCurrentNativeMuIssuedWriters.lean`, SHA256 `76596c03925f0a27bd41ffb50572114363a452e58e1ce9ae07603f0b914e1697`.
- Conditional writer fusion: `SourceCurrentTrackedWriterFusion.lean`, SHA256 `62996854bc5214574ea5c8a8b2f07b45f4c9cda44f1a2a6fc027b30e548d587b`.
- Exact open Mu profile and marker erasure: `SourceCurrentStoredMuTrackedProfile.lean`, SHA256 `a523e6d07c746744bbb800806f681c17ff77ef1ef35213cc8201470debd84812`.

The manifest pins these and the other reviewed frozen dependencies. It pins only owned evidence and explicit immutable sources.

## Validation

Selected strict `binder-contract-direct-5` completed with exit zero and a zero-byte log. Its source SHA256 is `3886140429687b018358d1d8d6656b2137cad06b3ec3a78adc37c37f8af0108e`. Selected `binder-contract-public-1` prints the one public constructed statement, its complete proof, and axioms with all eight required print options. It completed with exit zero and passed the hardened check. Its source SHA256 is `5723df3de80ff9bd4039efefa951e90ca63177cb853dbe82f894d159ab9d59ed`. Only propext, Classical.choice, and Quot.sound are permitted. The Lean jobs use version 4.34.1, memory.max=memory.high=4 GiB, swap.max=0, and the five-minute cap.

Failed strict attempts 1-4 remain unchanged. Attempt 1 contains the incomplete helper type and duplicate-set proof goals. Attempt 2 retains a tactic rewrite failure. Attempt 3 proves the full hostile Ready infrastructure. Attempt 4 contains one extra tactic after the contradiction was already solved. The final selected attempt is 5. There is no new production module and no canonical build target for this evidence-only theorem.
