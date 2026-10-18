# Physical invariants through actual Parent returns

This component proves preservation through actual successful worker returns.
It does not prove that a worker returns. It does not prove general outer
termination or exclude a collision with an active node owner.

## Initial data and returned facts

`SourceCurrentNativeOperationHeap.Good` contains weak physical native cells,
constructor `Ready`, full equality-operation memo `Valid`, allocated guard
fields, `SemanticReady`, and the stored cost heap. Native cells retain their
captured operands and resident results. They do not assert native query
language correctness or semantic memo-key safety.

`SourceCurrentLowerOperationInvariants.Effect` contains final `Good`, actual
constructor `Keeps`, and equality-operation `Grows`. Each lower theorem
derives these facts from the initial invariant and a literal successful
worker equation. It does not take a reached-input plan, `Ranges`, or a
supplied completed graph. Graphs used inside the proofs come from the
successful worker equations.

The merge premise is the existing `SourceCurrentMemoMergeEffects.Stored`.
Each entry has the exact original reference, an available original and
result, and a closed result when its original is closed. This condition is
stronger than residency alone. It is an initial memo condition. It is not
a future result condition or a semantic language law. Shared target slots
need only available stored values. A new class initializes empty slots.

`SourceCurrentOpenProjectionFields` proves annotation preservation through
completed projection graphs. Its public node, rows, and forest theorems
take those graphs. The lower worker derives them from actual successful
returns. These projection theorems do not require global closedness,
`WarmHead`, a finite `Cap`, or selected path support.

The lower proof covers actual Target, Force, Leaf, edit, edit-list, class,
class-fold, and class-pass returns. The Parent proof covers actual Seeded,
Scan, Required, class-pass, local reduction, and constructor returns. It
retains arbitrary Mu and union payloads. Child and row recursion uses
literal intermediate states and actual returned values.

`SourceCurrentParentOperationInvariants.parent` takes initial `Good` and
merge `Stored`. Its live branch needs the original guard field, inherited
`EqReady`, and available children. It returns `Effect`, final merge
`Stored`, and residency of the exact returned edge. The raw rejection
branch does not use the live premises. The separate `reject` theorem
requires only initial `Good` and the symbol. It constructs its own empty
field and sentinel. It needs no child residency, inherited readiness,
original field, or worker fuel.

Old `Ready` entries persist through the returned operation growth. New
descents can use final `Valid` and existing descent correctness. This
component does not assume validity at every prefix. It also does not
derive validity at arbitrary failed worker states.

## Checked integrations

`ParentInvariantKernels.constructed_live` constructs its own physical
source, fields, initial invariant, symbolic numeric reservation, and
actual Parent return. The source contains a Mu outside every finite
input `Cap` and an unrelated open depth reference. The actual precheck
selects a nonempty class list. The theorem applies the new invariant
producer to that same Parent return. It proves final full operation
validity, edge residency, and retention of the original field. It does
not take a future return, trace, range, or output invariant as an input.

`ParentInvariantKernels.constructed_rejected` uses arbitrary inherited
data and arbitrary children. Its raw contradictory guard has no initial
field lookup result. All nine worker fuels are zero. The literal Parent
returns the actual sentinel with final `Good` and resident output.

The private setup comes from the immutable earlier
`20261017-initial-parent/parent-numeric-kernels-1.source.lean`. That file
is unchanged. Both new integration statements are public aliases of
their exact checked private statements. No assumptions were removed for
printing. The integrations test physical transport. They do not establish
a general execution producer for Parent.

## Verification and attempt provenance

Final strict logs are `native-direct-3`, `projection-direct-3`,
`lower-direct-4`, and `parent-direct-4`, with the common
`parent-invariants-` prefix. Each log has zero bytes. Kernel strict attempt
1 also has zero bytes. All runs after the initial infrastructure failure
read back MemoryMax and MemoryHigh as 4294967296 and swap as zero.

Final public group 2 checks 50 distinct declarations. These comprise 35
handwritten heads, three structure constructors, and twelve projections.
Final kernel-public group 2 checks two constructed theorems. All 52 pairs
include full signatures, full proof prints, and axiom reports. All eight
required options are explicit. Only `propext`, `Classical.choice`, and
`Quot.sound` occur. No print omission or printer failure is accepted.

Native direct attempt 1 could not connect to the user systemd bus. Lean
did not start. Its source, raw log, and metadata remain present. It has
no cgroup readback. Native attempt 2 failed a private alias declaration.
Projection direct attempt 1 returned zero with an unused cost warning;
it is not selected as strict evidence. Foundation canonical attempt 1
also records that earlier projection warning. Projection strict attempt
2 removed the warning. Attempt 3 changes only the inaccurate module
header and remains strict clean. The proofs and signatures are unchanged.

Lower attempts 1 through 3 preserve namespace, elaboration, instance,
and linter failures. Lower attempt 5 is a redundant zero-byte check of
the exact final attempt-4 source. Parent attempts 1 through 3 preserve
type, unused-instance, and constructor-instance elaboration failures.
Every attempted source and raw output is retained under its own number.

Final canonical projection, lower, and Parent builds succeed. Their only
warning is replayed from the unchanged
`InternedFreshOrdinaryClosedCompletion.lean`. The final native source
was built by foundation canonical 1; its strict check is clean. That
historical foundation build also compiled the earlier projection draft.
The final projection has its own later canonical-3 receipt.

## Remaining boundary

Successful physical invariant production does not supply semantic native
key safety, a recursive body language law, or a success theorem for all
outer calls. General progress still needs exclusion of physical key
collisions with every active ancestor. It separately needs a well-founded
bound on fresh recursive requests. Parent can construct new values, so
neither operation growth nor no-busy alone proves termination. Haskell
correspondence is a separate obligation.
