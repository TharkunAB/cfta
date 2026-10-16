# Yielded recursive request classification

Date: 2026-10-17 01:10 CEST. Source: `SourceCurrentAllocatedRecursiveRequestStep.lean`, 113 lines, SHA256 `0666a41b86d8bb4579966d722309467f7e8f1b9ea561b04ff5ba6f870eaecc0e`.

Two public theorems classify one actual current yielded instruction. Inputs are current physical native Valid, NodeReady or EdgeReady, current Words, and the literal yielded-step equation. No semantic Completes, ActiveAbove, successful body, future WordRanges, or annotated PhysicalTrace is an input.

Both conclusions retain exact machine equality and equality-operation equality outside the branch disjunction. Publication and demand can change native memo tables; the theorem does not silently reset or equate those tables in evaluating cases.

`node_yielded` has three alternatives. Direct lookup emits the original requested compileNode body bound to the caller continuation, and the entire checked state equals the input state. A ready demand emits the actual returned value's continuation and supplies availability at that exact returned state. An evaluating demand emits the requested compileNode body bound to the captured finishNode continuation. Its actual returned node table has that handle evaluating the exact requested record.

`edge_yielded` has two alternatives. Ready emits the actual returned row continuation and derives residency at the returned state. Evaluating emits the current `.edgeBody request` with its captured finishEdge continuation and the exact evaluating edge cell. The theorem does not substitute the older eager compileEdge body.

The proofs inspect literal lookup and demand outcomes. They use PhysicalCache.node_ready/edge_ready for current returned residency and node_started/edge_started for exact request recovery from checked machine keys. Native demand-evaluate observations provide the actual running cells. An absent or busy observation conflicts with the supplied yielded equation. This does not assert that arbitrary busy states are impossible or prove whole-query progress. No completed semantic memo provenance is required by physical classification.

## Imported integration

Three kernel pairs passed:

- `fresh_node_frame` starts from an actual absent node-key table entry. It derives literal publication and demand of the original request, the captured finish continuation, the evaluating owner, and unchanged machine/operations before any recursive body executes. It supplies no result-law or body-success premise.
- `warm_edge_continuation` derives a literal ready step from an actual physically valid published returned cell. It returns the existing resident row and the exact unchanged checked state without replaying an edge body.
- `direct_node_state` checks the optional-key bypass. It retains the original compiled request and the whole checked state.

## Validation

Pinned Lean 4.34.1 source direct1 passed with all linters and no diagnostics. Root's `receipt-control-request-build.log` passed1131jobs; this component was target1131. The shared log has a historical dependency warning; this source has no new warning.

Final imported checks passed two public axiom/full-signature pairs and three integration pairs. Both standalone sources include all linters and complete explicit proof/universe/deep-term/name printing with one million print steps. Final logs returned exit0 without warning, error, `sorryAx`, omission, or truncation markers.

The first public attempt had a mistyped toolchain executable path and returned127 before Lean started. Kernel attempt1 had two proof-tactic closing issues, preserved with its exact source. Kernel attempt2 fixed only those evidence proofs. Production passed on its first direct check and was unchanged throughout.

Only the owned new source and uniquely prefixed evidence were written. No older source/evidence, Haskell, Audit, Git state, or root documentation was changed. No canonical build was started by this component owner. Whole arbitrary-prefix physical admission and WordRanges remain root's separate target.
