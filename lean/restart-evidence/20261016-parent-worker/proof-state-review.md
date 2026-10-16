# Independent proof-state review

Reviewed 2026-10-16 14:22 CEST. Read-only; no builds or repository mutations. Source main is c0cc8a05, merged at 896b0a1c. Current local HEAD is ade9584d6817.

## Target and strongest result

The target is correspondence between independent mathematical specifications and the CURRENT Haskell library. Exact accepted terms by node-count size, finite execution, counts, ordered ranks and both inverses, probability laws, and transformation semantics are separate contracts. Accepting runs, distinct terms, and decoded values remain different objects. No whole-library theorem is complete (`lean/notes-current-local-worker.md:5–10`). Exact listing/counting/ranking use the explicit FTA boundary; interned construction and transformation require their own transfers (`docs/adr/0004-explicit-graph-boundary.md:19–44`).

`SourceCurrentAllocatedPartialActual.root_exact:280–297` proves full independent PCS language equality at the SAME completed return. Its explicit premises are:

- an actual completed `NodeCall budget ⟨.live identity [], value⟩ before result after` and strict `NodeCallReads` for that call;
- reached `Checks`, initial `Context`, a ready allocated empty inherited equality value, and available input.

It returns a computed next Inventory, full Post, available result, and `∀ ambient term, meaning holds ambient result term ↔ meaning holds ambient value term`. It does not prove that the completed call exists for arbitrary inputs. It is one-pass language preservation, not general completion or unconditional Haskell runtime correctness.

The eight `PartialActual` endpoints (`:228–279`) derive physical and language invariants by actual mutual strict-read induction. Smaller actual calls discharge child laws. `PartialInvariant.Context:25–35` retains Ready/At, warm outer semantic laws, merge Stored/CacheCovers, fourth Correct, global Valid, and ProbeHeap. `Post:38–44` returns the actual next Context, physical effects, and merge/fourth extensions. `PartialChecks.Checks:142–144` supplies reached live edge-body range plans but is indexed by an already completed Trace. It cannot establish that Trace's existence.

Other strong components include exact raw validated FTA row/readback, canonical order, trimming, public size-query transfers, and rank inverses (`lean/notes-sized-finite-keys.md:114–158`). The optimized rank endpoint still states scan/product premises and a lazy-runtime boundary (`:173–178`). These components are not whole-library correspondence.

## New uncommitted progress

Current status lists seven new proof modules: ParentWorker/Completion/Stability/Actual and PartialWorker/Completion/Stability. Parent and eight-family outer definitions now exist and have independent public/source/kernel reviews. They preserve exact failure states, winning request owners, same-handle completion, returned-edge descendants, inherited-first prefix, indexed descent, and literal raw reconstruction.

`ParentWorkerActual.finite:80` constructs stable parent execution, graph, strict Reads, receipt, and Post from initial Context+LiveInputs. `resident_finite:182` derives original fields and child residency from a resident edge. `sound:143` and `resident_verified:224` retain those legitimate initial facts for supplied successes. A raw `.done` alone does not supply the full physical graph.

`PartialWorkerCompletion.nodeCall_complete:73` and its seven companions derive ten sufficient bounds from a SUPPLIED finite completed graph, preserving the same result/full Caller. This is finite-graph realizability, not general outer completion. PartialWorkerStability now contains eight successful-stability and eight uniqueness endpoints, and its canonical olean exists. This read-only audit does not independently rerun them or certify the pending aggregate Audit/publication.

## Main missing areas

1. Finish current outer literal-success → same graph/strict Reads/full initial-Context receipt integration and publish its validation. Preserve computed inventories and all actual tables/states; do not substitute historical native execution.
2. Establish general constrained outer termination, or an exact limited domain. Unequal-length classes can move constrained structure deeper (`cfta/src/Data/CFTA/Equality/Operations.hs:129–141`). Bounded worker totality, successful monotonicity, and finite-graph stable completion do not solve this. Busy exclusion needs independent progress. Repeated-pass convergence is separate; public reducePartially performs one pass (`:68–70`).
3. Transfer serial logical schedules to Haskell forcing, publication/black holes/concurrency, concrete containers/identities/machine widths, global events, and the noConstraint CAF. Reads validity is not a host event trace.
4. Complete current frontend validation/name/codec/callback adapters and full-pipeline composition, including changed drawn fields, typing inputs/binder bounds, LTA/GHC paths, solver and random-source contracts. Existing Sized/rank/probability components keep their own premises.

Theorem counts, green audits, and passing examples do not measure end-to-end completion.

## External fix handoff and documentation cautions

FINDINGS begins with the requested external Haskell repair registry (`:3`). It supplies current source/merge, failure, files, repair commits, repro commands/artifacts, validation, and upstream status. PR65/b9219b9e rejects the Chain field-pool input with `FieldAtomOnDatatype "Next" 0` (`:33–54`); standalone holds remains opaque. The negative-bound, named-measure, finite metadata, constructor-probe, and constrained-endpoint entries remain. This meets the handoff requirement. No older repair text is edited.

The new uncommitted `lean/notes-current-parent-worker.md:12–28,98–120` states the intended end-to-end reduction endpoint and these remaining gaps correctly. Two older presentation issues affect a current status answer:

- NEXT-PROMPT:57–62, HANDOFF/lean README first sections, and local-worker note:122–128 still say implement parent/eight families next. They describe the last published checkpoint; those definitions now exist uncommitted. The new parent-worker note updates this stale next-step wording. Report new progress without claiming completed publication/integration.
- The old FINDINGS "confirmed, unfixed" field-pool bullet (`:74`) and older "Current" headings are historical. The opening registry marks that case repaired. Preserve the historical text and use the opening status when reporting present bugs.

Audit2464/58403 and Haskell798+golden are the last recorded local-worker checkpoint. New focused proofs do not silently update the aggregate Audit count. Haskell is unchanged, so those suite results remain reusable. The live root_exact signature supports the conditional claims above.
