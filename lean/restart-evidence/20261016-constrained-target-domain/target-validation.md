# Finite ordinary target validation

Validated on 2026-10-16 at 16:47 CEST.

Source: `lean/MicroCFTA/SourceCurrentAllocatedFiniteOrdinaryTarget.lean`.
SHA256: `6a97fe6add9e84f2f6708ae9cd0ba66e5abd29703248939c1e76cb2fafbcf33f`.
The source has 196 lines and five public theorems.

`target-direct-3.log` records direct pinned Lean exit 0 with no warnings.
Root observed canonical terminal exit 0 in `target-worker-build-1.log`.
The combined Target and MergeWorker build passed 1298 jobs. Its only warning
is the historical unused-input dependency warning.
`target-checks-4.log` records final canonical-imported Lean exit 0 with no warnings.
It contains five public axiom/full-signature pairs and four integration pairs.
All dependencies use only `propext`, `Classical.choice`, and `Quot.sound`.
No final declaration uses `sorryAx`.

Public APIs: forest_closed, operand, fold, target, finite.
forest_closed is generic in Symbol and Guard. It derives every signed path's
existing ForestClosed domain from an available finite ordinary captured forest.
The current target APIs use the actual source Symbol and Guard.

Operand uses the actual projection graph and exact merged result. Initial
native certificates survive its literal constructor-only advance. The current
memo-aware merge derives output structure and preserves both result tables.
Fold induction uses ordered concrete current receipts. It runs the head
operand, then the tail, then verifies the exact Step.run physical trace with
Execution.node_trace. Intermediate Ready and inventory facts are constructed
by current verified endpoints, not supplied as future-state premises.

Verification endpoints accept the actual Operand/Fold/Target graph and initial
Ready, At, captured availability/domain, physical merge Stored, structural
merge Stored, native Stored, semantic merge coverage, global validity, and
actual-prefix ranges where native calls occur. They return the existing full
receipt and reads plus structural merge Stored, native Stored, and result Node.
The finite endpoint constructs the actual Target and reads from these initial
facts. It has no supplied completed graph, recursive callback, result-domain
law, selected-path support, or closedness premise. Guards and equality classes
remain unrestricted. No target height bound is claimed.

Integration checks derive arbitrary signed support, verify empty-target state
identity with warm certificates, construct a root-only target with no native
range obligation, and construct two real targets in sequence. The first result
is the second target's captured forest. The second uses the first receipt's
computed inventory, Ready, availability, physical Stored, semantic coverage,
global validity, and both derived structural cache invariants. No future result
or completion premise is added.

This is current target domain preservation and finite completion under the
existing actual-prefix range and semantic admission contracts. It does not
complete structural class edits or general constrained recursive reduction.
Mu, references, and explicitUnion remain outside the captured structural domain.

Earlier logs retain corrected elaboration errors. target-direct-1/2.log record
local syntax and request inference corrections. target-checks-1/2.log record
external section-variable inclusion errors and warnings. target-checks-3.log
passed against an isolated object; target-checks-4.log passes the exact final
source through canonical imports. The production source stayed unchanged after
its direct green result. No older source, Audit, documentation, Haskell, or Git
state was edited. This task ran no Lake command. No compiled artifact is stored
in this evidence directory.
