# Global row footprints and actual outer memo origins

Recorded 2026-10-18 04:55 CEST. This review adds one checked guard-algebra
witness. It adds no production theorem or general termination claim.

## Global property and the exact closure failure

Let P(g) mean that every record returned by PhysicalPayload.own g satisfies
ClassPositionalFootprints.Unselected record 1 1. This is a property of the
full equality accessor, not only the stored equalities field. It imposes
no condition when own returns contradiction (.ok none).

The checked witness uses the actual native conjoin function and two raw
constraints. first has stored classes [[[0],[1]]] and residual Same [] [0].
second has stored classes [] and residual Or [Top]. Both stored fields are
Cached. The first accessor returns .ok none. The second returns .ok (some []).
Both P premises hold. Their literal native conjunction has an unsupported
positive residual. Its accessor falls back to the combined stored field.
It returns exactly one coherent record with paths [[0],[1]]. Endpoint [1]
is a prefix of [1,1], so P fails at the conjunction.

The same checked statement proves accepted first 2 = false. The checked
constructor rejects the first input at that arity. No accepted-input closure
counterexample is established. The witness does not construct a native
Trace or claim that these guards occur in an accepted public execution.
It refutes the unrestricted algebraic closure rule P(a) and P(b) imply
P(conjoin a b), even with Cached stored fields. This is not a Haskell defect.

The failure is at sourceEqualities, not a demonstrated failure of ordinary
path saturation. sourceEqualities merges positive residual equalities only
when positiveNormalized succeeds. A None contradiction can hide stored
paths. After an unsupported residual enters the outer conjunction, that
extraction is disabled and those stored paths become visible. See
SourceCompactGuards.lean:488 and ConstraintConstructors.lean:20.

Consequently a finite literal list whose effective own fields satisfy P
is not by itself a P-closed alphabet. Filtering the finite original guard
inventory by Derived does not fix this: conjunction of the two literals is
itself Derived and fails P. Filtering that carrier again by P needs an
additional conjunction-closure proof, and this example refutes that rule
on the unrestricted raw domain. Finite inventory membership alone gives
neither the footprint nor an ordering of outer requests.

## Branches that copy or create fields

Ordinary Required and below-edit reconstruction copy full raw row fields.
Node and union normalization can remove or reorder rows, but they do not
invent a new constraint. SourceCurrentRequiredHeapEffects.head/requireAll
already preserve arbitrary AnnotationHeap predicates on actual completed
graphs, with their stated initial semantic, cost, and availability facts.
The actual positional laws recover the complete original guard of every
positive surviving row. These copies therefore transport a known P fact.

Source constructor work, bare-self filtering, stored substitution, and
optional binders can also preserve arbitrary raw-field annotations.
AnnotationHeap.run and AnnotationStoredSyntax.optionalBinder are existing
producers. The latter uses actual stored syntax and a resident input, not
a desired body/output relation. A warm winner is an existing physical
record; a global heap annotation covers that earlier payload too. General
used-Mu occurrence correspondence remains open, but it is not required merely
to retain an already-established global guard predicate.

The native ordinary edge body introduces the actual conjoined constraint.
An arity mismatch, checked Parent rejection, or cleared projection introduces
Top. P(Top) is immediate. The conjunction branch is the substantive missing
closure step for this accessor-only predicate. Generic ConstraintEditClosure
and ConstraintPassClosure have explicit closed/range/graph entry premises;
they must not be cited as unconditional completion or unrestricted current
worker producers. Current NativeClosedGuardAlphabet retains its supplied
closed alphabet through actual checked prefixes; it does not prove P on
that alphabet. Causal GuardHeap and AnnotationHeap are different invariants.
ParentGuardHeapReturns transports the former and does not imply P on every
physical row key.

One stronger candidate is to require prefix-disjointness for every path in
the stored equality field and every Same atom exposed by outer conjunction
flattening. It would inspect hidden stored paths too. Appending a suffix to
a path disjoint from [1,1] retains disjointness. Normalizer-generated paths
have exactly that form (EqualityNormalize.mem_extendClass). Canonical class
filtering and connected-component union introduce no other path. Outer guard
conjunction retains exactly the union of its original atoms. These facts
suggest a normalization/Derived induction for that stronger predicate, then
an implication to P. This is a proposed next proof, not a checked theorem
in this package. It strengthens the initial hypothesis and does not solve
the unrestricted full-library goal. No accepted-input closure counterexample
or general accepted-input closure theorem was proved in this review.

## SourceCurrentOuterPositionalOrigins

Reviewed all six public declarations and all private proof bodies at SHA
a096cca0722664c4cc4c4cd95e3e5cb1e41f32c7353f155ee7ca2e8f4b966ebc.
No material issue was found.

EdgeLink refers to the original captured row, its original guard footprint,
and the same input/output forest index. It does not assert that every guard
satisfies a global footprint. Origins adds this relation only to returned
edge cells and retains the exact request-to-key law. initial derives it for
empty outer tables with no supplied result-origin premise.

The cold/warm helper does not infer full request identity from a numeric
edge key alone. It uses EqReady for both inherited payloads, valid canonical
equality allocation, resident complete edge values, and coherent edge
identity uniqueness. begin_request also proves the selected handle is linked
to the queried key and that beginEdge leaves checked state unchanged.
These conditions exclude arbitrary malformed prepopulated tables.

A ready hit recovers the actual returned cell, derives owner=request, and
uses its prior Origins fact. Cold evaluation retains the exact evaluating
owner. edge_body uses ActualParentRowOrigins.edge from initial weak Good,
Stored, field readiness, inherited readiness, available children, and the
causal Plain heap. Parent does not change the outer result tables. The proof
then finishes only the captured handle with the newly derived EdgeLink.
It does not install the relation of a losing or hypothetical owner.

all_done follows literal successful worker equations with smaller outer
fuel at recursive node, row, and child calls. Existing prefix invariants
supply each intermediate Good and input fact. Existing actual guard-heap
transport supplies the causal heap after completed calls. Mu and constructor
branches retain outer tables. reached follows actual prefix transitions and
completed earlier calls. It does not assume a future child return, a supplied
future Link, a rank, Cap, NoDeep, global closure, or an idle table.

The results are completed-call and reached-prefix memo-invariant producers.
They establish neither general successful outer completion nor global P.
Fixed positive-chain mass decrease still requires an actual chain producer
and each next guard footprint. Basic class [0]=[1] is already outside the
fixed (1,1) footprint, so this global condition is a restricted input property.
The unrestricted goal still needs all-active-owner separation and a bound
or well-founded measure over the actual mixed-index execution.

## Selected evidence

Root outer-origin-direct-1 is genuinely zero bytes and matches the final
source. Canonical1 passes 1846 jobs with only the old ClosedCompletion warning.
Root public1 prints six full signature/proof/axiom pairs. This review pins
those receipts but does not select their six public pairs a second time.

Own global-footprint-kernels-3 is terminal zero with a zero-byte log.
Own kernels-public1 prints one full constructed signature/proof/axiom pair.
All eight required options are explicit and only standard axioms occur.
The first failed normalization attempt and the earlier successful witness without the rejection
conclusion remain with their immutable executed snapshots and raw logs. All four
own attempts use effective 4 GiB maximum/high, swap zero, and a five-minute
timeout. No production file, old evidence, Haskell source, or authority document
was changed. No new production canonical run was needed for the review.
