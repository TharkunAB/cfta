# Independent native request position review

Reviewed on 2026-10-21 at 03:49 CEST. The complete final 1,193-line source is
SourceCurrentNativeRequestPositivePositions.lean, SHA256
e62eed872e07c2457a0ae577e7e35281b48fe4d5ebc6b90bbb403a62e01c5727.
No material issue was found. The review read the complete proof and each final
diff. It owns zero Lean/Lake commands and zero public pairs. It reuses the
owner's three full public readbacks: one definition and two theorems. Earlier
reviews and proof packages remain unchanged.

## Public invariant and actual endpoints

Support (line 50) is a public per-cell invariant on both native memo families.
Its definition exposes the exact captured NodeRequest and EdgeRequest laws.
At each supported finite depth, original source bindings and actual source
input support plus input caps imply backward positive-position support for a
returned value. The edge law separately retains the root full guard and each
exact natural child index, including nullary rows. Suspended/evaluating cells
do not assume a future returned result. FlatMemoThunk.Valid also retains its
ordinary bounded/linked cell conditions, with trivial key relation; physical
key correctness is supplied separately. The public definition has no generated
private NodePos, EdgePos or CodePos type dependency.

call (line 1138) consumes an actual completed empty-domain node Trace at a
current Checked state. It takes fixed-source Facts, Current/Context, actual
causal publication History empty-to-current, the old conditional joint cache
laws, current Support, source-available closed operands and explicit finite
Plain caps. It derives final Support, the same-path OR-input result law, the
old actual joint Return and final causal publication history. These are
current past-cache invariants. It has no premise asserting this request's
result law or a future enclosing return. Source availability is in the FIXED
source heap, not merely in an arbitrary later generated-value heap.

request (line 1171) derives both old and new cache laws from literal empty
native tables, establishes initial Current/Context, and invokes call ONCE.
Good, SemanticReady, GuardHeap Plain, actual causal history, source availability,
closedness and finite caps remain explicit. Original, OriginalBindings and
NodeInputs are derived internally. It assumes the actual finite admitted
Trace; it proves no existence, numeric capacity bound or termination result.

## Constructor and exact indexed child inversion

Actual makeNode readback maps each surviving canonical result row to an
original full row. Source and canonical row indices can differ. The natural
child index and full row guard stay fixed. makeUnion handles empty, singleton,
ordinary collapse and mixed union branches. Full coherent resident readback
is used after matching references, so equal keys are not substituted for full
values without the required cache facts. Union membership adds no path step.

The checked edge helper is inserted byte-for-byte from the separately checked
private snippet. It inverts the actual body yield, actual two field loads,
allocation result and full guard readback. The accepted branch uses the real
loaded conjoin closure: if the returned guard is nonplain, an input guard is
nonplain. The root case needs no child. Rejected/mismatched sentinel output
has Top and an empty child, so it cannot contain a positive path.

The child walk retains All2 between the exact ordered zip and returned child
list. getElem?_zip_eq_some recovers BOTH input child lookups at the SAME index.
Equal repeated values do not identify distinct positions. Earlier returned
availability is transported through the actual later machine Extension.
The edge law therefore supplies positional support rather than only output
membership. makeEdge readback retains its exact full children and guard.

## Private certificates are discharged by actual traces

CodePos and ControlPos are private proof interfaces. Node and edge continuations
consume actual returned availability/residency, the old cap law and the new
position law. Every state-changing primitive and child continuation includes
Causal at that exact returned machine. Generic bind and ordered walk compose
these exact intermediate states. There is no new evaluator. Raw protected
finish instructions have False certificates; they are handled only by the
actual protected-body split below.

node_law_pos derives the conditional node position law for every supported
depth, rather than assume it. It covers the actual decision order: empty,
reset, self, swap, repeated, Mu, union, reference and ordinary cases. Repeated
placeholder references are opaque and have no PositiveAt. Explicit ordinary
constructor cases retain the full original List.Mem row receipt. They do not
case-split a nonempty membership proof into unrelated alternative witnesses.

The Mu certificate derives exact entered bindings and body inputs from the
current domain and source support. The SAME child return supplies old NodeLaw
and new NodePos. Its old law derives the finite cap of THAT incoming maybeMu
body. The certificate consumes the checked maybeMu position theorem once,
with THAT child's semantic/available/guard state and causal history. A capped
Mu operand has a hereditary Plain body; it cannot supply a positive body path.
A non-Mu operand's body is its literal input. A warm stored winner is never
identified with the current incoming body.

The reference branch uses the actual read of a legitimate source binding.
It recovers the exact available hereditary Plain source Mu and its actual
read lookup. Its positivity is excluded. The other operand keeps the same
path. This does not infer that arbitrary resolved heap names are Plain.

## Warm cells and protected finishes

Empty tables satisfy both returned-law stores. Actual lookup inserts only a
suspended cell; demand creates no returned positional law. Warm ready hits
use PhysicalCache.Valid and actual checked key safety to identify the complete
captured request with the queried request. Both cap and position laws are
read for that exact request. Key equality or Shape alone is not used to
replace the captured payload.

The private strong induction is on the length of the supplied actual Trace.
Each real primitive step derives its physical Current/Context from the old
framework and Causal from NativePublicationTrace.step at THAT admitted step.
No Grows, issued extension, memo history or scalar Mu store is promoted into
causal publication history. Actual optional pending/failing branches cannot
supply the successful yielded step required by the trace.

through splits ONE actual bind trace into bodyTrace/result/middle and the
exact outerTrace. The old completed theorem and new smaller-fuel induction
consume the SAME bodyTrace and result. from_history derives Causal at THAT
middle. The continuation then receives those old cap and new position facts,
old and new memo stores, physical checks and exact returned machine.

through_node and through_edge additionally retain the actual protected finish
frame. ProtectedPrefix owner preservation proves that the SAME handle still
contains the SAME captured evaluating request after the actual clean body.
The old joint store and new Support are updated with that owner's actual
returned body and the two laws derived for that same result. There is no
independent writer selection or caller-supplied desired finish law. A finish
changes only memo status, so the machine/heap Causal from the body remains
valid. The exact continuation trace is then the smaller next induction.

The actual edgeBody case uses the actual unbound checked body yield. It calls
the inserted edge certificate on that same body, then binds its exact caller
continuation. The node cases distinguish direct, ready and evaluating paths;
both evaluating paths keep their actual protected finish. All calls use the
explicit physical/old/new postcondition triples, so no unrelated post is
chosen by a metavariable.

The old cap/physical completed theorem is independent of this new positional
proof. Reusing it on the same trace does not assume the new law. The induction
proves a supplied finite execution property. It is not a decrease proof for
recursive runtime execution or an active-owner renewal rank.

## Final changes and limits

The final differences repair elaboration: local source/equality scope,
explicit control and postcondition arguments, exact ordinary constructors,
Mu result-variable elimination and literal reference CodePos unfolding. They
add no semantic premise, remove no actual call and change no public contract.
The selected strict source is the exact reviewed final source.

The cold endpoint derives native cache position support internally. The warm
endpoint permits its reuse for actual later fixed-source requests. Generated
closed inputs that were not source-available still need actual source/cache
rebasing. This theorem does not discharge that composition, chronological
selected class edits, a retained child pair, original binding ancestry,
global renewal/final retention/outer completion/convergence, or production
Haskell refinement. The unrestricted opaque-Mu counterexample remains valid
outside the finite-cap and supported-binding premises.

## Frozen evidence

Selected request-position-direct-4 is terminal zero and its log is literally
empty. Selected request-position-public-1 is terminal zero, 272,302 bytes,
with complete check/type/body/axiom output for Support, call and request.
All eight printer settings are present. Public types contain no generated
private names. No terms are omitted. Each of the THREE heads, including the
Support DEFINITION, reports exactly propext, Classical.choice and Quot.sound.
Support does not report zero axioms. There is no project or evaluator axiom.

Both selected commands use pinned Lean 4.34.1, effective 4 GiB max/high,
zero swap, five minutes and fresh usage above one percent. The main owner
retains five commands with three failed elaboration attempts. The separate
private edge helper retains its own four commands and two failures, outside
that main count and with no additional public pair. This review adds none.
Recorded commands are preserved unchanged. Portable verification checks frozen
snapshots. --live also checks ROOT foundations and the installed candidate if
present. Final root Audit and publication are separate work owned by root.
