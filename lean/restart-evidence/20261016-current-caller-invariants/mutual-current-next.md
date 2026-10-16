# Next: the current mutual physical and language invariant

Read NEXT-PROMPT.md, HANDOFF.md, root FINDINGS.md, CONTEXT.md,
docs/adr/0004-explicit-graph-boundary.md, and
lean/notes-current-caller-invariants.md. Source main is 8f85ddb6.
Preserve the optimized interned core and every older proof. Record each
future Haskell fix first in root FINDINGS.md with its failure/reproducer,
files, commit, checks, and upstream status.

## Verified base

Thirty-five new modules are frozen in frozen-modules.json.
Full Audit is GREEN2406 with 57445 dependency checks; only standard
foundations and the old unused-input warning remain. Proof commits are
6f300927, 5b391983, 2e3f0fd4, and 4b2995ee. Haskell sources are unchanged.
All 4276 starting files and 2370 older non-Audit proof sources are retained.

The actual strict ParentEdge, reduced-edge body, and reduced-edge call now
derive their own full physical/language/global receipts and filtered probes.
Use SourceCurrentAllocatedPartialEdgeActual.edge_body/edge_call as the
edge leaves. Their Scan-only range plan sees only reached evaluated owners,
live original constraints, and literal source field loads. A ready hit
requires no body range plan. Body advancement preserves both outer result
tables. Evaluation retains and finishes its own first-published owner.

PartialFrames retains protected Running and Returned cells in both families
through the actual eight mutual graphs. PartialDescent supplies actual
allocated child payloads, inherited readiness, physical effects, admission,
and warm Sound retention. PartialWalkLanguage supplies precise indexed
WalkLaw/ChildrenLaw induction steps. Smaller actual NodeCall results must
derive the supplied head NodeLaw; these combinators do not prove that call.

## Critical source-read correction

Use SourceCurrentAllocatedPartialSourceReads for the outer induction.
Its parent leaf uses the strict current ParentEdgeActual.Reads. All eight
erasure endpoints preserve the old graph and global endpoints. The converse
is not proved and is false in general at the primary gate layer.

Do not infer validity for arbitrary old EndpointMemoGateTrace.NodeReads.
Its closed endpoint can query a different hidden entry and edge list from
the trace input. SourceCurrentPrimaryReadsCounterexample proves actual
construction, readiness, residency, finite gate execution, initially valid
globals, an old read receipt, and an invalid returned bundle. Identity999
is never installed in that actual heap. This is a Lean receipt defect,
not a Haskell implementation counterexample.

The new primary relation explicitly ties its descendant query to the source
input record. Its completion theorem constructs strict reads from actual
gate execution. Strict Scan/local/parent existence endpoints derive their
schedules from initial invariants and reached range plans. Supplied-read
validity now follows the literal returned global tables. Fixed-budget
exposure uniqueness does not justify equality of different read schedules.

## Next proof

1. Define the legitimate current entry invariant: checked Ready, inventory
   At, warm caller Sound, merge Stored and CacheCovers, fourth Correct,
   actual global Valid, and explicit ProbeHeap. Preserve all warm tables.
   Input requests require inherited readiness and actual input residency.
2. Prove a mutual invariant for NodeCall, NodeBody, Rows, Descendants,
   Children, and Walk using their actual strict read recursors. Each result
   must retain the physical/semantic entry facts at its exact returned state,
   produce the next inventory, and give its independent language law.
   Derive the head law from its smaller NodeCall induction result.
   Do not use a completion callback that assumes the desired body law.
3. In NodeCall evaluation, begin derives the exact evaluating owner. The
   smaller NodeBody proof supplies its result law and residency. Use
   PartialFrames.node_body to retain the owner until finish. Finish installs
   that owner and transport by the actual key derives the candidate law.
   Completed hits use the stored law and keep the whole caller state.
4. An ordinary row runs its actual EdgeCall, then descendants of THAT
   returned edge, then the suffix. The parent constructor can reject and
   change the child count. Do not use the original edge's old child list or
   own constraint after its call.
5. InheritedPrefix combines inherited FIRST and returned own SECOND once.
   Contradiction skips the own accessor. Its exact satisfaction law derives
   the combined parent obligation. Indexed allocated descents feed each
   child. PartialWalkLanguage combines the actual head/tail induction laws.
   RawRebuild uses same-arity setChildren with the complete returned guard.
6. Compose the exact returned row union through literal modifyNode to derive
   the ordinary NodeBody law. Keep its actual identity fast path.
   Binder reconstruction uses MuRebuild at a resident binder and the explicit
   ProbeHeap. Parent probe transport now supplies this invariant globally
   through the lower current operations; still prove the outer transport.

Then add the literal bounded executable worker with complete reached state.
Distinguish done, errors, incomplete fuel, busy, absent, and unexpected Rec.
Hits can succeed at zero body fuel. Connect completed execution to the strict
graph and derive sufficient stable bounds only on a justified domain.

## Remaining full objective

General constrained outer termination remains open. Operations.hs:119-142
records unequal-length path classes as an unproved case. Local completion
and semantic narrowing do not imply decreasing child depth. Public
reducePartially is one pass. Repeated-pass convergence is separate.

Serial logical graphs do not prove GHC forcing, lazy IntMap/list demand,
the noConstraint CAF, concurrent publication, concrete identity lifetime,
machine Int conversion, or word capacity. Keep all frontend and recursive
generator adapters, separate Sized contracts, solver IO, random sources,
callbacks, codecs, older constructor/equality work, and broader library
targets active. No board posts or deployments.

Use one canonical Lake process at a time. Poll its actual handle to a
terminal result. Preserve all raw evidence. Reuse unchanged-source strict
Nix all-component build, 777 examples plus golden, five-file Fourmolu, and
four-package Cabal-gild. Push verified formalize checkpoints regularly.
Do not mark the full goal complete at a component checkpoint.
