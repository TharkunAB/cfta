# Independent review of current plain rows

Timestamp: 2026-10-16 15:52 CEST.

No material defect was found in the reviewed source.

Reviewed source hashes:

- `SourceCurrentAllocatedPartialPlainRows.lean`: `ce1cbd359c464233e57e41a3b0ae2ce15848958a4c094a22a6498d2b95c06e2b`.
- `SourceCurrentAllocatedPartialPlainRecursionDefs.lean`: `a382c5f9b8960195558b9ff3d2c2b7f999acc8b7df9e5a7191f8b9b78e0ef0c2`.
- `SourceCurrentAllocatedPartialPlainNode.lean`: `f0215ebd5409c623b1cdee268dcd098421ebd079d6e53709c1c6269ac6979164`.

`PlainRows.descendants` at line 33 constructs the resident inherited-first prefix before any child. It derives child availability from the actual resident edge and initial physical invariants. It calls the live child helper at the exact prefix state and uses the exact allocated combined payload. The actual raw rebuild retains the current caller and returned edge table. The strict actual-read theorem derives its full `Post` and resident result.

`PlainRows.rows` at line 64 follows edge call, returned-edge descendants, then suffix. Each stage starts at the previous stage's actual return. The original row's effective empty own payload follows by physical readback inversion, rather than a supplied local range plan. The finite edge call derives its own parent completion and structural shape. `Shape.regions` transfers child Regions to the actual returned edge. `Shape.height`, the strict child-to-edge rank lemma, and the original row bound establish smaller node ranks even for erased or singleton-Empty results. Completed edge and descendant frames restore the initial active-owner bound before later work. The suffix uses retained residency and equality readiness at its actual current state.

The source order matches `cfta/src/Data/CFTA/Equality/Operations.hs`: the ordinary node branch composes `reduceEdgeIntersection` before `reduceChildren` at lines 80–96. The latter combines inherited and returned own constraints before indexed child descent. Lines 143–145 erase children for contradiction and otherwise descend at each original index. Full residual guards remain in the model. This review does not equate empty effective equalities with a literal empty stored field or a true full guard.

The `NodeResult` and `Below` definitions at lines 28 and 37 retain actual graph indices and strict read receipts. They contain no assertion that completion holds. `PlainNode.finite` at line 117 discharges `Below` by strong induction at lines 132–139. It handles initial warm hits through actual stored owners. The evaluating branch derives owner-value equality and pushes a strictly lower active bound. Its ordinary body uses the exact original row rank bound. This gives finite one-pass execution in the stated Region from initial invariants. It does not require a public successful-execution premise, future range plan, or completion callback.

## External checks

`rows-review-checks-2.log` passed with exit code 0. It contains no errors, warnings, or `sorryAx`. It has four public axiom/full-signature pairs: the two row helpers and the two interface definitions. It has four additional integration theorem pairs:

1. Resident returned-edge descendants construct an actual graph, strict reads, reached checks, full `Post`, result residency, returned-domain preservation, language law, restored active bound, and sufficient literal worker bounds. The private adapter derives every smaller completion by calling the proved `PlainNode.finite`; the public integration theorem has no `Below` premise.
2. A finite row list constructs the corresponding actual graph and sufficient literal bounds. It derives the union language law, exact row count, output residency, full `Post`, returned-domain preservation, and restored ancestor active bound. Again, no completion callback is a public premise.
3. Each child of an actual three-way parent shape retains its Region and has smaller node rank than the original edge. The result does not require equal arity.
4. Empty rows return the original complete caller at every ten-bound tuple, including all zeros. The actual empty graph and strict read receipt are inverted after construction. No successful prefix or child completion is supplied.

The first external check records a failed definitional reduction of the well-founded worker. The final check uses its literal defining equation. The final log has no temporary elaboration placeholder. No proof source changed during review.

Root-managed canonical logs show: RecursionDefs 1507 jobs, Rows 1510 jobs, and Node 1512 jobs. Each passed. The older `InternedFreshOrdinaryClosedCompletion` unused-variable warning remains the only warning in these build logs. This review ran direct Lean only.

## Scope

The established completion is one current pass through `PlainRegion`: ordinary traversed edges have empty effective equality payloads; Mu and explicit union branches are opaque. Initial `Context`, ready inherited allocation, operand residency, the structural returned-edge domain, and active-owner rank bounds remain explicit. The row helper additionally takes a finite structural rank ceiling. The integration kernels discharge only the completion hypothesis, not those initial facts.

General constrained caller termination, repeated fixpoint completion, concrete noConstraint CAF forcing, pending publication, GHC evaluation order, machine identity correspondence, and runtime SMT behavior remain separate. This result does not replace those obligations with an older eager or scoped execution theorem.
