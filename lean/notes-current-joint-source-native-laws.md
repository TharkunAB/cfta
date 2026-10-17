# Current library proof status and joint source laws

Checked at proof commit 1a0ad30e. This checkpoint starts at published 0ebb832d.
The proof commits are ad5c409b, bd85cd40, 86d2c5f1, and 1a0ad30e.
Source main remains c0cc8a05, merged locally at 896b0a1c.

## Top-level target

Prove the intended contracts of the complete library. Then prove that the
current public Haskell operations implement those contracts. For each public
operation P, the schematic target is:

`Valid(input) ∧ Supported_P(input) ⇒ runHaskell(P, input) terminates with result ∧ Spec_P(input, result)`.

This is a family of target theorems. The complete implementation theorem
does not exist yet. Support must describe initial inputs and explicit
resources. It must not assume future successful execution or the desired
result. Documented errors and validation order are observable results.

The contracts include exact distinct accepted terms per node-count size,
counts, enumeration order, both rank/unrank inverses, transformation language
relations, generation coverage, and sampling laws. Distinct terms, accepting
runs, and generated members remain separate. Exact transformations require
language equality. Over-approximations require inclusion. Representative
selection has its own restriction contract.

## Current proof map

| Area | Established result | Remaining boundary |
| --- | --- | --- |
| Exact Sized queries | Exact size classes, counts, original explicit row order, size-major enumeration, and both rank/unrank inverses. Validated graph keys supply a finite carrier. | Concrete host and solver adapters and complete public composition. |
| Interned construction | Finite modeled repaired closed construction, including Mu and unions. Actual source execution produces exact guard observations and causal body/probe equality. | Concrete lazy publication, interning, and runtime correspondence. |
| Recursive intersection | Every successful bounded source call derives cap, ranked occurrence, scope, and heap laws. Exact generic native meaning transfers these laws. Closed inputs construct a finite generic cold return under explicit WordRanges. | General initial numerical range production, the current checked equality-cache control lift, and finite full warm callers. |
| Ordinary constrained reduction | Initial profiles and constructor headroom derive a resource Plan. A complete modeled pass retains guarded language and stores. | The ordinary domain excludes Mu, references, and unions in every descendant. |
| Mixed outer tables | Plain whole nodes and descendant walks construct finite execution in certified tables with other constrained owners. | General constrained node completion and initial production of active and stored certificates. |
| Rich editor and successive classes | Actual executions retain causal stores, original signed masks, caps, and physical/language receipts. Required execution constructs its finite return. | Current closed captured hereditary-leaf support is smaller than the source gate. General class existence remains open. |
| Other components | Language, equality, arithmetic, union-find, memo, ranking, generation, sampling, and restricted source-driver proofs remain preserved. | Remaining current adapters and complete public pipelines. |

Some theorems construct finite execution. Others verify supplied actual
returns or local continuation laws. Their premises differ. The theorem
count does not give a meaningful completion percentage.

## New joint source induction

KernelJoint.Context retains physical validity, SemanticHeap, GuardHeap,
growth from the same immutable source, and issued history. Checked requires
this context and the stated laws at every actual successful return.
KernelJointEffects retains this context through literal edge, node, and
union construction. These effects do not add a new Mu record.

KernelJointRows proves actual ordered row and child walks and both union
directions. Each smaller actual return supplies its own cap, source-indexed
occurrence bound, and reference scope. The literal ordered child zip supplies
its budget. KernelJointDecision handles the selected reset and repeated-pair
branches with their actual original operands and sorted numeric pair.

KernelJointCalls handles Mu entry and reference reads. Actual domain
extension retains original source bindings. The smaller body request returns
the joint laws at its actual machine. Its scope excludes Depth and uninterned
probes. At positive rank, NativeBinderReturn uses the exact earlier probes
and final selected record. At rank zero, the same smaller body execution
also runs under cap zero and derives hereditary cleanup. An unused global
decidable instance was removed; no linter is disabled.

KernelJointExecution.execute_joint discharges the recursive Calls interface
by induction on actual source fuel. It handles every onNode branch. It does
not assume successful smaller calls or future result laws. A failed or
exhausted bounded call has no successful result to certify. A separate
KernelGuardHeap theorem retains GuardHeap at all stopping states. The
NativeGuardHeap adapter retains it through actual native work and traces.

Nonplain pair rank alone does not prove termination. A mixed Mu body call
can keep the same positive rank and sorted numeric pair. The domain's
repeated-pair branch can then return locally. The source induction uses
actual fuel. Existing semantic completion supplies a separate progress
argument for generic finite native execution.

## Native composition and its exact boundary

NativeJointClosed.request_joint transfers the proved source laws through
exact generic native Meaning. The source and native result use the same
returned machine. done_joint_of_ranges derives these laws for a supplied
actual warm return with valid physical provenance and WordRanges. That
verifier alone does not construct warm completion.

NativeJointClosed.cold_complete constructs its own finite generic native
return from closed, available, capped source operands, SemanticHeap,
Covered[], GuardHeap, valid domains, and WordRanges. It retains the earlier
Correct receipt, SemanticHeap, coverage, and stable extra-fuel return. It
adds the same context, cap, ranked occurrence bound, closedness, Original,
and ProbeFree laws. It does not take a supplied successful return, trace,
callback result law, or desired output cap.

WordRanges remains a substantive boundary. Its definition quantifies over
all actual finite yielded prefixes and checks each reached request's words.
It is not yet derived from general initial numeric resource bounds in this
theorem. Do not report this conditional cold result as a complete initial
resource theorem. Literal self-query integration does derive its own ranges
from the exact short cold and warm paths. That specialization does not
supply the missing general range producer.

The generic native compiler uses the supplied conjunction operation.
The current checked allocated worker also loads equality fields, checks
equality, and can reject a row before child code. These new generic native
laws do not automatically prove that worker's complete Control execution.
Existing physical checked receipts and local adapters remain preserved.

Independent integration constructs a productive Mu and a constrained
ordinary operand from empty. Its actual source query returns that same
nonhereditary ordinary value. The theorem derives all joint laws at the
same returned machine. Separate literal generic native kernels construct
the cold return and the next warm return from the full resulting state.
They include a nonhereditary Cap1 output. No supplied completion or desired
result law is an input to those kernels.

## Remaining work

1. Derive general request word bounds from initial numeric resources.
   Connect the joint laws to the current checked equality-cache Control
   worker. Keep actual cache owners, equality fields, and rejection paths.
   Do not replace either step with a future-prefix or desired-result premise.
2. Construct finite warm Target, Leaf, editor, and class execution from each
   full caller's initial supported inputs and resources. Supplied returns,
   traces, and local continuation laws do not prove this existence result.
3. Prove general constrained recursive descent. Produce active-owner bounds
   and causal stores from initial callers and actual past prefixes. Retain
   the full source gate, which permits nonhereditary ordinary endpoints.
4. Prove repeated reduction convergence. Complete remaining recursive
   pruning and compilation callers. One pass does not prove a fixed point
   or bound intermediate structure.
5. Complete current typing and refinement frontend correspondence. Include
   drawn fields, symbolic measures, errors, validation order, and generator
   rank order. Complete runtime, solver, IO, and randomness adapters. Keep
   capacity, primitive, and user-code assumptions explicit.
6. Compose complete public pipelines through construction, transformations,
   graph conversion, exact queries, generation, and sampling. Include serial
   warm calls and discharge each remaining adapter.

The current cap and captured closedness restrictions define an intermediate
supported family. The final theorem must cover the full source contract.
The complete library goal stays active.

## Validation and Haskell handoff

The pinned full Audit passes 2816 jobs and 62897 dependency checks.
Only propext, Classical.choice, and Quot.sound occur. All eleven production
sources pass strict checks without diagnostics. Imported signatures, axiom
checks, hashes, component manifests, and failed attempts are recorded in
restart-evidence/20261017-joint-native-producer/.
All 83 imported pairs pass in 17 groups. Eight component manifests verify
198 entries. Read checkpoint-validation.json for exact hashes and groups.
Canonical replay retains an older unused-input warning. All new source
warnings are corrected.

Preservation retains 11398 starting files, 2804 older non-Audit proof sources,
all 239 Haskell files, and 68 frozen production manifests with 573 entries.
Stashes and three other worktrees remain unchanged. Preserve the optimized
interned core and every earlier proof, counterexample, repair, and marked draft.

No Haskell change or new Haskell defect occurs in this checkpoint.
PR #65 merges recursive field-pool repair b9219b9e in c0cc8a05.
Current derivation validation rejects the reported Chain pool with
`Left (FieldAtomOnDatatype "Next" 0)`. Standalone holds retains opaque pool
evaluation. Root FINDINGS keeps the external repair handoff first, with
reproducers, affected files, commits, checks, and upstream status.
Reuse unchanged strict Nix all-component build, 798 examples plus golden,
Fourmolu, and Cabal-gild evidence for c0cc8a05.
