# Next fixed-reader Mu proof step

Reviewed at 2026-10-18 22:13 CEST.
This is a read-only proof-design review.
It adds no Lean declaration, build, theorem pair, or counterexample claim.
The accompanying progress-review-source-pins.json records the exact reviewed bytes.

The current generator has no arbitrary-chain constructor.
There is no new actual causal counterexample in this review.
A general Mu simulation theorem remains unproved.

## What the existing recursor permits

Generated has only refl and filtered constructors.
Its recursive premises occur through Inputs.reference, which stores both existing Generated proofs for the resolved lexical pair.
Inputs.fixed stores one identical capture and exact map agreement on its free names.
See SourceCurrentRetainedMuDirectedCase.lean:53–105.
Finite constructor proofs cannot contain themselves as recursive subproofs.
The mutual recursor therefore gives a genuine proof-height induction for those already supplied lexical pairs.
It does not give an induction hypothesis for an arbitrary strict source child, a newly formed generator, or a selected writer's body.

A chain appears only in the separate Closure of Generated or Below.
Below is one-way literal inclusion.
The existing normalization relation does not assert that every generator is Directed.
At a causal reader, CausalGeneratedEmpty.generated already proves Empty agreement for every Generated pair by the actual mutual recursor.
It calls causal source fusion in the filtered case and uses the recursive Empty facts only at reference slots.
See SourceCurrentCausalGeneratedEmpty.lean:41–77.
Thus an Empty/nonempty counterexample cannot satisfy that theorem's History premise.
Ready alone does not replace causal History.
The earlier artificial-cache contract obstruction is outside that causal premise and is not a Haskell counterexample.

## Exact next membership lemma

The next small substantive producer is a cross-local version of PublicationReconstructionGenerators.publication.
Keep the same actual selected Publication event, Ready reader, Grows event.after reader, candidate availability, outer Environment, and Replacements reader outer.
Replace the single local value by two Available values u and v.
Take both Generated reader u v and Generated reader v u.
Keep BOTH literal warm equations explicit:

```text
execute event.body (bind reservedName u outer) reader = done left reader
execute event.ordinary (bind ordinaryName v outer) reader = done right reader
```

Derive Generated reader left right and its reverse.
Do not conclude Local, Directed, Same, or language equivalence.

This is a direct actual-constructor proof route.
PublicationSharedReplacements.shared, substitutions, and paired already accept distinct local values.
See SourceCurrentPublicationSharedReplacements.lean:25–30, 49–79.
The two local Generated premises provide the new leading Inputs.reference slot.
The fixed capture tail uses one identical shared map and reflexive membership.
The selected event supplies actual aliases and scoped self tests.
The old raw callback schedules and their warm replays remain unchanged.
No desired parent observation law is needed.

For a retained pair MuA/MuB, using its existing Generated proof in this leading slot is legal membership evidence.
It can supply a finite self back-edge for a new source-body generator.
It cannot justify calling the current Generated-recursion hypothesis on that newly created proof.
The new proof contains the parent proof and need not have smaller proof height.
A new relation constructor with the same premises does not remove this obligation by itself.

## Fragment induction and the actual cold boundary

Node row fragments now have direct actual schedules.
GeneratedRowSchedules.node retains the common original source index, full fields, and ordered mutual child generators from RowCalls only.
CausalRowFragmentAlignment.node adds derived Empty and survival parity using History.
Neither requires a whole ordinary-group stored call.
See those modules at lines 303 and 39 respectively.

FixedReaderUnionClauses.union reduces the parent to strict source-member atom and row clauses at the ORIGINAL reader.
Its atom premise includes the exact literal atom and actual warm atom call.
Its row premise includes the exact original row and actual RowCalls.
The child source expressions are strict members of the original union list.
The theorem does not itself derive the atom premise for an arbitrary active binder.
See SourceCurrentFixedReaderUnionClauses.lean:108.

Variables can use the existing lexical proof-height hypothesis at a selected reference slot.
A fixed nonreference capture instead uses identical filtering and exact map congruence.
GeneratedVariableFilter.variable_call already establishes that distinction.
See SourceCurrentGeneratedVariableFilter.lean:134.
This base case does not require a fresh general binder law for fixed captures.

Selected older writers need not have smaller source syntax than the current requester.
NativeMuGrowthWriters.from_empty recovers their actual event and prefix paths, but it supplies no current-source size inequality.
A source-size-only binder recursion is therefore invalid.
The actual retained self edge also cannot be justified by raw returned Value.depth: smart-unused finish can return a degree-zero ordinary value from a degree-one candidate whose stored body still has degree zero.

There is a second, independent boundary.
CausalStoredMuGenerators.unfolding retains the exact successor at the original reader, but its Generated comparison is indexed by the produced FINAL reader.
See SourceCurrentCausalStoredMuGenerators.lean:117–128.
Generated.filtered requires both stored calls to be warm at its own reader.
See SourceCurrentRetainedMuDirectedCase.lean:80–85.
A successful unfold may allocate before it returns.
The final-reader comparison cannot be relabeled as an original-reader comparison.
GeneratedGrowth.generated transports membership forward only; it provides no backward membership or observation transport.
WarmSupport permits observation transport, but its general open source producer is not supplied by the closed preparation theorem.
See SourceCurrentGeneratedGrowth.lean:20 and SourceCurrentObservationReaderSupport.lean:47,132,307.

The cross-local lemma should therefore be implemented first with both actual warm conditions intact.
The following general Mu task must retain the original-reader cold execution interval or derive the required same-reader fragment calls from actual support.
It must not silently add a cold Generated constructor and assume that constructor is Directed.
Newly allocated Mu outputs need an actual reader-compatible writer/support argument before an observation proof can use them.

## Useful proof organization after that step

Use lexical generator proof height only for existing Inputs.reference premises.
Use strict source size for node children and union members in the fragment law.
Use actual earlier publication paths when the selected writer source differs from the requester.
For a proof driven by an observed Mu successor, count the actual left epsilon path: the Mu unfold consumes one left step.
OpenWeakSimulation.Forward.path already checks this path-count decrease; its right path can have any finite length.
Rows then reduce finite observation depth, while source fragment descent and lexical proof height handle work at the same observation budget.
This is a candidate organization, not a checked complete lexicographic induction.
The missing cold-fragment/support certificate is a real additional proof obligation.
No well-founded source measure alone establishes it.

The immediate action is the cross-local actual warm publication membership lemma above.
The decisive next semantic consumer is an original-reader selected-Mu atom continuation that handles the actual cold interval without assuming its desired simulation clauses.
This report does not claim that this latter continuation is already produced or that current Generated is sound for every Ready heap.
