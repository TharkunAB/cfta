# Exact replay from observed boundary absence

`InternedObservedAbsence.Related` preserves the actual empty status of two
records. It also requires exact record equality when the first record has
no forbidden boundary atom. The forbidden predicate is arbitrary. It can
exclude every fresh reference and every Mu identity allocated after a
selected reservation. A predicate that excludes only one reference is
insufficient because the boundary profile stops at Mu records.

`makeNode_related` and `makeUnion_related` derive this relation from actual
constructor executions. They use a common coherent extension of the two
cache histories. Dead edges disappear on both sides. Every surviving edge
has exactly equal children when its forbidden boundaries are absent.
Canonical edge readback then gives equal surviving edge lists. Union
absence reaches every original operand, including ordinary merge branches.
The final equality is equality of complete records, not only their atoms
or tree language.

`InternedOrdinaryAbsenceReplay.build_related` lifts these constructor laws
through actual source nodes, unions, child lists, and edge lists.
`build_equal` states the resulting exact equality for two completed source
traces. Both executions complete by source induction. Captured input values
can contain arbitrary earlier Mu records. The source body itself does not
construct a new dynamic Mu.

`InternedObservedFilter.filter_related` handles actual root self filtering.
The supplied sentinel must be outside the forbidden set. Filtering cannot
hide a forbidden boundary under that condition. It also preserves exact
empty status through the source union invariants.
`InternedOrdinaryCallbackReplay.callback_related` composes the source body
and normalized callback executions. It derives exact output agreement when
the first normalized result has no forbidden boundary. It assumes no
callback key law.

`InternedRequestAgreement` compares completed Mu requests in the same
actual common cache extension. Equal probe pairs and cleanup flags imply
equal complete outputs, even when the callbacks differ. Coherent resident
probe records let equal canonical keys establish the same result. This
handles the completed-request branch without a callback comparison law.

The focused build has 195 jobs. The isolated axiom audit checks 8,114 theorem
dependencies with only `propext`, `Classical.choice`, and `Quot.sound`.
These modules discharge the ordinary constructor and allowed-sentinel
filter branches of the general source replay argument.

The dynamic smart Mu branch remains open. In particular, its fresh local
reference is forbidden. Root self filtering can remove that reference
before smart cleanup returns an unused body. The normalized result can
therefore be clear while the raw body is not. The remaining argument must
relate the actual two fresh body executions with their respective local
names, including root self alternatives and bare-self cleanup. No general
closed-Syntax no-pending theorem is claimed here.
