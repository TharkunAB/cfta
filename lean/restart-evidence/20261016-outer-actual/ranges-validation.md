# Actual-prefix outer worker range predicates

Frozen source: `SourceCurrentAllocatedPartialWorkerRanges.lean`, 152 lines,
SHA256 c5cb3bc781b19ee76d571f594daa80bc49c494af7673510442e35ee3562b1c30.

The eight predicates have the same family names, ten bounds, fixed budget,
and normal inputs as the literal PartialWorker. They use its exact fuel and
phase schedule. Node and edge calls read the actual begin result and check
the stored owner at the actual post-demand caller state. Ready, busy, and
absent branches impose True. Terminal node branches, ordinary exhaustion,
empty lists, contradictory inherited children, and failed inherited prefixes
also impose True.

`After observed next` checks next only on an actual `.done value caller`.
A failed observation imposes True. Rows checks the reached edge call, then
its actual successful returned edge's descendants, then the suffix at that
actual successful descendant return. Walk checks the literal indexed
descent's NodeCall and its suffix at the actual successful caller return.
Descendants passes its actual inherited-prefix operation state to children.
No predicate quantifies over arbitrary future returned states or assumes a
completed callback or semantic postcondition.

The edge-body predicate is success-gated as approved by root. It evaluates
the literal parent observation. A done parent requires the existing initial
ParentWorkerActual.ResidentRanges; a failed parent imposes True. The helper
`edgeBody_of_done ranges done` recovers that exact ResidentRanges from a
supplied literal edgeBody success. Other helpers expose exact evaluate
owners and successful continuation checks.

Direct pinned Lean source elaboration returned exit0 with no warnings in
`ranges-direct-1.log`. Root canonical validation returned exit0, 1478 jobs,
session18912, `ranges-build-1.log`; only the historical unused-input warning
remains. The final external check against canonical imported oleans returned
exit0 in `ranges-public-3.log`, with thirteen declaration axiom/signature pairs
(nine definitions and four theorems) and fourteen integration kernels.
The kernels cover failed continuations, zero-fuel ready hits, busy failure,
bare-reference error, parent failure and successful extraction, ordinary
fuel decrement, exact row and walk prefix states, failed suffix skipping,
inherited error/success, contradiction on an unresolved child, and empty
walk. The final log has no warnings, errors, or sorryAx. Only standard Lean
foundations occur in dependencies.

These are check predicates. They do not assert successful execution, initial
physical facts, result language, general termination, or host demand order.
This owner ran no Lake process and changed no older source or Haskell file.
Root controls full Actual composition.
