# One actual final heap for a fixed Returned law

Status: READ-ONLY DESIGN AUDIT. No new Lean declaration or compiler credit.

The proposal is viable as a proof design. Fix the final heap of the SUPPLIED
actual checked execution once. Use that heap only as a common physical reader.
Keep the conditional result law fixed from empty memo initialization. This
removes the growing-witness-set backfill problem and excludes the earlier
taller fake-pattern attack. It does not yet prove the recursive producer laws.

The original accepted source, build, stored FULL U, original root, fuels,
outcomes, noStop behavior, and joint finite accepted-completion objective stay
unchanged. The copied original coupled header is byte-identical. No runtime
counterexample or Haskell defect is claimed.

## Actual prefix-to-final extensions

Let `T : Trace n C0 S0 Cf Sf` be the supplied checked trace. Set the fixed
reader `F = Sf.native.machine.heap`. This is an actual observed field of T.
It is not an extra heap, model, compatibility, or future-extension premise.

Every split index k <= n has literal prefix and suffix traces at ONE common
control and checked state Sk. Construct these by induction on T. At k=0 use
Trace.refl and T. At k+1 use the real head instruction and the split of its
tail. This does not select an arbitrary reachable state or another branch.

`SourceCurrentAllocatedNativeSemanticTraceReadback.effects` gives Good Sk and
the original fields along the prefix. Apply that SAME existing theorem to
the literal suffix, with those reached facts. It derives
`Extension Sk.native.machine Sf.native.machine`. The source heap, issued
identities, and domain-table entries all survive. No cancellation of an
extension and no backward extension is used.

The initial Good/field facts and current checks must be the original produced
source resources. They are not new whole-goal assumptions. The step-level
physical laws also suffice for the machine-only induction. The frozen entry
receipt uses that smaller induction. Its original validation was interrupted
by an appended standalone import; this audit assigns it no new proof credit.

## Fixed conditional law

Use the EXISTING `SourceCurrentAllocatedNativeContextCache.Returned` directly.
The detailed mathematical law and proposed theorem shape are in
`THEOREM-SHAPE.md`. They are specifications for a proof, not new Lean APIs.

The A qualification retains the exact empty domain and closed only-U input
profiles. An M witness retains a genuine full U/pattern compiler entry in T,
the original domain cache and exact entered domain, full closed pattern P,
its real control identity, node/union tag, body/ref alias, both operand orders,
and the original weak/strict height bounds. P has NO only-U premise.

The witness must place P in F. An authentic checked entry already derives
this: its first input check gives full P availability, and its actual suffix
gives extension to F. Current operands are also available in F through their
own literal suffix. Thus the proof compares actual complete records at one
coherent heap. It does not compare records in unrelated source extensions.

Quantify the result law over ALL these genuine witnesses of the supplied T
from the start. Do not add witnesses as execution proceeds. `returned_empty`
is vacuous for this one fixed law, even when an authentic witness's actual
entry happens later. The lookup/demand/finish property laws then use exactly
the same law. A finish still requires the producer's local conditional law;
those recursive producer proofs are the remaining work.

A witness is supplied as data when a conditional law is APPLIED. Its existence
for every relevant actual request is a separate producer obligation. The full
worker theorem must derive that existence. It cannot assume a future-witness
supplier or replace the full finite-assignment objective by this cache law.

## Concrete cached repeated-request test

Use a real closed nonempty ordinary Q with control identity qid. Let D be the
literal domain entered for U and Q from the empty structural domain. Its seen
set contains exactly pair(uid,qid). Consider the cached request

```
r = (domain D, left Q, right reference(interned uid))
```

With the actual normal nonempty/no-reset/non-self/order guards,
`Control.repeated_first` returns `reference(intersection uid qid)` in canonical
pair order. That value is open and fails the closed only-U result profile.
This is the prior adversarial qualification case. This audit does not claim
that an accepted source execution reaches it.

Try to qualify that old cached request later with an authentic taller pattern
P at the same entered domain D. Domain key equality fixes its singleton seen
pair; fixed-uid cancellation gives pid=qid. Canonical domain identities can be
compared in the actual final domain cache by Domain.grows and identity_exact.
Both Q and P are closed and available in F. The exact existing
`closed_identity_injective F facts Q P ... qid ...` gives Q=P. Consequently
height(Q)=height(P), so the required ref-side STRICT inequality is false.
The bad cached result never satisfies M for such a witness.

The same argument excludes a future raw Pfake with reused qid and changed
payload. It cannot coexist with Q as a closed Available record in F. A raw
matching ID without final availability remains unsound. Two unrelated heaps
remain insufficient. A later authentic entry for the same actual Q is allowed,
but it still cannot satisfy the strict inequality for this repeated request.

Physical `node_request_exact` and `node_ready_property` preserve the entire
original cached request. They prevent a ready hit from silently changing the
operand or domain to fit a different later witness. They do not prove a local
result profile without Returned.

## Birth-time availability and exact scope

NodeReady and Domain alone do NOT give availability of the non-Mu P in an
earlier producer heap. Domain.bindings retains only Mu names. Availability in
F transports forward from an earlier state, not backward. A domain key stores
the non-Mu identity pair without its full payload or height. The complete
request equality at a cache hit does not add that missing payload to a past
heap.

There are two useful routes. Do not conflate them.

1. Within ONE closed empty-domain native root call, an authentic entry witness
   can retain its actual queried-owner prefix. The EXISTING
   `SourceCurrentNativeRequestSourceScope.node_prefix` then derives BOTH full
   queried operands in that call's FIXED INITIAL HEAP. If one operand is P,
   actual initial-to-producer extension gives P availability at an EARLIER
   producer, even when this particular entry occurs later. This uses actual
   source scope, not backward growth. The entry-to-queried-owner connection and
   original admission bounds must be derived. The existing optional Origin
   does recover the owner at optional sites; it is not a blanket origin theorem
   for every reached entry or request.
2. A native conditional M producer may instead use full P only at the common
   final reader. At the producer machine, actual NodeReady supplies the current
   operands and represented domain. Same-heap identity/height arguments use F.
   Body/ref lookup must be proved from that current Domain, original full U,
   and source growth. This avoids a birth-time P-availability assumption.
   This formulation has not yet been proved for all actual native body cases.

Existing kernel M theorems have a DIFFERENT premise: extension from the
ORIGINAL literal entered machine to the current machine. A later entry cannot
supply that extension to an earlier cached producer. Do not apply these
kernel theorems backward or silently rebase their fixed original entry.
`mixed_entry_replay_after_extension` also needs the already-directed earlier
extension. Current Domain and final common-heap identity do not alone supply it.

If using an earlier genuine entry instead, a new actual domain-origin argument
must extract it from the real prefix and identify its full pattern at F. An
allocation history of KEYS alone is insufficient. It must retain actual
compiler operands and IDs. A nonempty initial domain cache also needs its real
source origin; empty NODE/EDGE memo tables do not imply an empty DOMAIN cache.

## Outcomes and warm history

A yielded Trace ends at an actual control. A successful call has its exact
pure-return trace by done_trace/node_done. The last pure step leaves the heap
fixed. For failed, constraint-error, or blocked execution, include the actual
last non-yielded step before calling its resulting heap the final reader.
`step_invariants` and `execute_invariants` cover all those outcome tags. Their
current physical checks must come from original admission. A yielded-only
Trace does not automatically include a heap write of a final blocked step.
No supplied fuel is enlarged and no completion is asserted.

Fixing F per new warm query does NOT initialize all its old returned cells for
free. To derive Returned from empty initialization, the observed history must
include those old actual producers, with the SAME F fixed for the proof. A
single current-call Trace starting from a warm memo cache is not that history.
Across Source calls, constructor and caller effects outside this native Trace
must also have their actual forward heap transport. The single-call fixed
input-scope theorem does not automatically cover producers from earlier calls.
Do not use an unrelated sibling heap as F without the actual caller transport.

An arbitrary checked Code trace is also too broad: physical finish inputs alone
permit finishing a cell with an arbitrary AVAILABLE value. The theorem must
start from the SAME genuine original compiled source request and retain its
actual producer/finish ancestry. The design does not prove a law for arbitrary
handwritten finish instructions.

Earlier outputs after a later stop keep their own original branch obligations.
A common native reader neither merges their symbolic state histories nor proves
one compatible assignment for them. Global source trace composition and the
original same-root joint finite accepted-completion target remain open.

## First next proof

Prove one ACTUAL native M producer at fixed observed reader F. Obtain current
operands/domain from actual input checks. Obtain their extension to F from the
same trace. Keep the genuine original closed pattern at F, the exact entered
domain, and strict ref height bound. Prove the repeated branch impossible by
common-heap identity; retain original budgets and exact cached request.

Then extend to the body/ref/union/ordinary and allocated edge-body cases and
preserve the SAME Returned law at every supplied-fuel endpoint. The fixed F
choice removes one logical obstruction. It is not a proof of these cases,
all-slot provenance, arbitrary narrowed-domain inhabitation, one compatible
historical assignment, or full Haskell correspondence.
