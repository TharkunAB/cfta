# Original-row cluster control

Updated: 2026-10-22 06:27 CEST. Proof checkpoint: `272cb31f5ff5d60c9396a931931aea1297759cad`. Start: `4f7a7e064f17a66367618dc2bc360f0755503b1a`.

Control stores cluster, scan and comparison phases. It reuses the complete H7 State.
Outcome retains the actual state with yielded, done, failed, constraintError or blocked.
The comparison phase forwards one existing H7 step and retains the scan frame.
Yield and blockage retain the exact inner residual control.
Failure and constraint error retain the reason and state. They add no continuation.
execute zero yields the exact input control and state. A successor advances one step.

comparison_lift consumes an actual H7 execute done equation.
It derives some used with 0 < used <= supplied H7 fuel.
At that exact prefix, the outer runner yields the inline resume at the SAME after.
The candidate identity test precedes the pivot identity test.
Promotion resumes candidate :: (reverse incomparableReversed ++ tail).
The common result selects the branch only. It never becomes a later operand.
The supplied upper fuel bound can exceed the consumed prefix.
This theorem does not produce a completed comparison or a genuine-input cluster run.
It derives no semantic law, native readiness, global Trace law or new capacity result.
H7 and the new control are noncomputable. No compiled runtime is claimed.
Haskell refinement remains open.

H15 remains the checked fixed-source comparison and domain-capacity foundation.
H6 constructed_node_calls remains the strongest combined semantic theorem.
Genuine-packet cluster completion is the next proof obligation.
Physical pruning iff, grouping, generated parents, source/model rebase,
public Mu unfolding/kept-body, full traversal, practical width, solver contracts,
convergence and the public pass remain open. The goal stays incomplete.

Selected source: 129 lines, SHA `37bcce3d4b04310f6e3c1e394e27a875baf98547f4078d1b3be7252c47d0a5f7`.
Selected clean strict: `original-row-cluster-control-strict-2`. Selected FULL: `original-row-cluster-control-public-1`.
Strict has a literal-empty log. Declaration limits remain unchanged.
FULL retains 646402 raw bytes. Complete check/print TYPE bytes agree.
comparison_lift TYPE: 136 logical lines, 135 LF, 9947 bytes, 9943 characters.
comparison_lift actual axioms: Classical.choice, Quot.sound, propext.
Root and an independent reviewer read the complete checked public TYPE.
The printed TYPE is byte-identical. No second manual TYPE read is claimed.
All four private markers and recorded helper names are absent from TYPE.
The whole proof body is retained and checked programmatically.
No whole manual body read is claimed.

The ledger records four Lean/Lake commands: three source checks and one Audit.
One source check failed. No source check passed with warnings.
No PUBLIC TYPE output was rejected. Every actual input and raw log remains.
Metadata work adds no proof command. Audit has 3,633 jobs and 75,432 theorem dependencies.
This record does not claim seal or publication success.

Preservation covers 86577 starting files/modes and 3631 older non-Audit Lean sources.
All 298 baseline Haskell files, 207 active package files, old proofs,
drafts, counterexamples and optimized code remain.
Additional H16 Haskell archives must match baseline source bytes under H16.
Every old document has an exact inverse. The original Audit has 3121
lines and SHA 8587e6d6e10773d7e626ad5a51d3ba5f5739d731673616129765104b2a2af1f6.
Its only edit is the new module import.
FINDINGS keeps the external repair index FIRST. PR #65 and PR #97 stay fixed.
No Haskell repair or runtime change is added.

The preceding 4f7a7e064 checkpoint is LOCAL_ONLY. Earlier automatic approval
review rejected pushes. Continuing the goal is not fresh user approval.
The local publisher keeps seal, staging and filesystem/index/HEAD checks.
It records PENDING_USER_APPROVAL and performs no network command.

The exact next contract is in lean/restart-evidence/20261022-original-row-cluster-control/NEXT-TARGET.md.
Only a context, public header and helper-statement proposal is authorized next.
The hard source stop is350 lines. Bodies and checks need separate complete review.

Strict1 failed at two PairOutcome.done constructor references.
The exact two-reference repair uses the public constructor namespace.
The original source, amended header, failed log and patch remain in source-repair-v2.
Metadata diagnostics and corrections remain in the checkpoint's metadata-repairs.md.
