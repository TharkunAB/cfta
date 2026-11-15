# Native C/M target and first missing producer

Status: UNPROVED SPECIFICATION. This is not a Lean declaration or a proof.
There is no current public full native C/M header to quote. The exact complete
Kernel header is preserved separately and is already proved. This file pins
the remaining native scope without inventing a proved analogue.

## Original parameters that must remain

Retain the accepted firstOrderRaw library/query/signed source expression,
successful build from empty, original source heap and stored FULL
`U = .mu entry body depth ordinary`. Retain original NodeKey, entry identity,
ALL body/depth/ordinary metadata, source Facts and actual source-heap growth.

Retain full original P, P.free=[], identity(P)=some pid, tag(P)=node OR union,
and the actual original source entry. Do not add only-U(P). Do not replace P
by an operand descendant or by a same-ID value selected without availability.
Write R=`.reference (.interned entry.identity)` and uid=entry.identity.
Let Profile(v) mean `v.free=[]` and every InternedBoundaryAtoms atom of v is
`.mu uid`. Available is a separate physical property, not inhabitance.

## Exact actual entry and common execution

Fix ONE actual completed checked trace T from original control/state C0/S0
to Cf/Sf. Let W be the literal Sf.native.machine.heap, not a supplied future
heap. Retain the original whole supplied fuel and require trace counts bounded
by that fuel. The original S0 contains Native.initial with BOTH complete
FlatMemoThunk.empty families. Empty tables with arbitrary old cells are not
this initialization. Retain initial weak Physical, source-heap growth,
operations validity, ORIGINAL InputsThrough and ORIGINAL FieldsThrough.
No RequiredCache.Ready, future Physical, future Extension, model or future
availability supplier is permitted.

An authentic M entry is DATA about this SAME T:

    an actual prefix C0/S0 -> .code (.enter emptyDomain U P uid pid k) / entryBefore
    the actual one-step enter event and its actual continuation
    E = Environment.enter entryBefore.native.machine.domains emptyKey U P uid pid
    entered heap = entryBefore.native.machine.heap
    entered domains = E.2; actual continuation receives E.1

P availability and physical readiness at that event come from the checked
entry/actual original plans. P availability at W and every earlier-prefix
extension to W must be DERIVED from T. Keep full P, original identities and
actual bound continuations. Do not demand original-entry->earlier-producer
growth: a memo producer can precede this authentic later entry.
The existing SameExecutionReferenceControl consumes actual entry and producer
prefixes and derives suffixes. It does not prove that all needed prefixes exist.

## Closed and original mixed request qualifications

For actual closed requests retain original input availability and define the
sufficient domain case literally as:

    Profile(left) and Profile(right) and
    (domain = emptyDomain OR domain.key.free.isEmpty = false).

The public A projection remains emptyDomain only. The internal closed clause
must also cover SAME-D closed requests created by original-M reference reads.
Do not replace the domain disjunction by arbitrary Cache.Valid domain. The
latter allows empty-free recorded-pair cutoffs and can return an OPEN reference.

For each authentic original entry E above, the M qualification is:

    request.domain = E.1
    operands = (alias,Q) OR (Q,alias)
    alias = body OR alias = R
    Q is Available at the actual producer/read point, closed, and only-U
    height(Q) <= height(P)
    alias = R -> height(Q) < height(P).

The exact original P/height/entry and BOTH operand orders must stay fixed in
all recursive calls. A same-key domain handle is sufficient only where an
existing syntactic key lemma proves that particular control equation. It does
not justify arbitrary request equality, warm cell payload equality, or a new
original entry witness.

## Required native history conclusion

Use the EXISTING ContextCache.Returned predicate and the actual Node/Edge
memo families. The node law must give Profile for every qualified closed
request and every qualified original M request. The exact OPEN auxiliary
clauses remain separate conjuncts. Their results can contain cutoff references;
they must not be replaced by Profile or assumed closed as intermediate values.

The edge law must use actual ordered child pairs and actual domains. For each
qualified C/M pair of rows, EVERY returned child must have Profile. It must
cover successful matched rows, sentinel mismatch, and both raw orientations.
The proof must derive membership/child qualification from the actual pair
walk and checked field reads. It cannot accept a future child Profile law as
an extra source assumption. Existing precise auxiliary row-readback laws may
be projected where their antecedents actually hold; they do not cover all
mixed source-body versus operand rows.

For EVERY actual prefix and supplied-budget endpoint of T, preserve BOTH
Returned laws, including the state after finish and before pure observation,
and blocked/error/stopped retained states. For every actual returning raw trace
of count<=original fuel, derive the corresponding request law. Busy/blocked
states have no fabricated result or termination claim. No recursive IH may
use count+1 to observe an already reached pure body. A local trace_done
observation is not extra recursive fuel.

The initial laws follow from BOTH complete families empty. Ready branches
consume the SAME law at the exact raw request before reset or swap. Evaluated
branches prove the law from genuine bounded children before storing the real
payload at finish. The desired final projection is native available/closed/
only-U closure for the SAME original A/M requests. No Kernel-native semantic
correspondence or cache-model premise is supplied.

## Next concrete producer: M reference -> same-D closed query

For actual M request `(E.1,R,Q)` or `(E.1,Q,R)` with the ORIGINAL full-P strict
height qualification, prove the complete native history case as follows.

1. Derive actual nonrepeated reference control and FULL original U read from
   original source facts plus actual same-execution entry/producer receipts.
   Existing CommonReaderReferenceControl and SameExecutionReferenceControl
   already prove this LOCAL control when those receipts and qualifications
   are supplied. Reuse them. Do not add a wrapper that hides their premises.
2. The literal read emits `(E.1,U,Q)` or `(E.1,Q,U)` in the SAME current state.
   Existing mixed_entry_nonempty_free_map derives the closed resettable domain.
   Q stays the original closed only-U operand with strict original-P height.
3. A ready hit needs the COUPLED closed Returned clause at this exact raw key.
   A direct/evaluated body resets to a genuine smaller empty-domain query.
   The coupled IH must prove the latter; it is not a supplied cache promise.
4. Empty-domain U/Q in turn can enter a new actual original U/Q domain and
   recurse through body/Q. General body/ordinary and body/union producer cases
   must therefore be assembled with the closed clause, not deferred to a
   separately initialized child run or independently selected witness.

The first new semantic assembly is this coupled closed/M native induction.
For its ordinary case, derive each genuine row child as closed/closed or
ref-U/closed under the SAME original entry. PrefixHeight.child_lt/member_lt
then yield strict height relative to ORIGINAL P. Original P can contain atoms
other than U; no proof may silently add only-U(P).

## Exact producer-scope obstruction

SourceQueryInduction.query_returned_and_raw_results is public. Its complete
header is in PUBLIC-SOURCE-QUERY-ENGINE-HEADER.lean.txt. It supplies genuine
positive-prefix callbacks with used+count<=parentFuel and count<parentFuel.
It also derives first-state source growth and operations validity internally.

Its callback domain, however, contains arbitrary weak-Physical states with
cold-source growth and original plans. It does not assert they are prefixes
of the chosen T or that their heap grows to W. Thus it cannot by itself
instantiate the fixed-W authentic-entry law above. The missing receipt/qualifier
producer must be derived on the SAME actual execution. It must cover earlier
memo births as well as later reads. Adding future heap extension or P availability
as a body-rule supplier would change the full goal.

This is the exact remaining admission work. Current local reference control
and selected profile histories are sufficient ingredients for their stated
cases. They are not the whole producer/admission theorem.
