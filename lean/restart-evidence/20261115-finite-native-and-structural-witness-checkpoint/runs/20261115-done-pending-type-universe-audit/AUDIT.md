# DONE pending domains and the original stored U

Recorded: 2026-11-15 03:35 CET.
Status: READ-ONLY SOURCE AUDIT. No new theorem or compilation credit.

## Answer

The existing proofs do NOT identify every graph-bearing pending handle at an
actual DONE source output as the exact original U handle. They establish the
following chain, with two explicit gaps:

1. DONE + native CacheValid gives an available CLOSED recursive-boundary value
   and an EMPTY stored bucket at every graph-bearing pending slot.
2. A recursive boundary can be `.mu` OR `.union`.
3. If that actual value is a Mu and its atoms are only the original U atom,
   an EXISTING checked classifier proves equality of the FULL Mu payload with U.
   An EXISTING lookup inverse then gives the exact original encoded handle.
4. The missing source producer is the only-U property for every actual live
   pending handle at the emitted endpoint. Program roles do not contain it.
5. Even after that producer, the explicit union case needs a separate actual
   exclusion/collapse or semantic/productivity classification. Only-U atoms do
   not imply that a union value has the Mu constructor or the original handle.

No accepted-source execution counterexample is established here. The statement
about every remaining handle is unproved; this audit does not declare it false.

## Exact checked headers

All paths are relative to `/home/tritlo/Code/mcfta`. HEADER-MAP.json records exact
source lines, copied header files and hashes. SOURCE-PINS.json pins the reads.

### DONE supplies boundary and empty bucket

`MicroCFTA.SourcePruningEnumerationRestart.done_pending_boundary`
`lean/MicroCFTA/SourcePruningEnumerationDischargeBoundary.lean:46`

Inputs: actual caller/cache, CacheValid, actual noStop restart DONE, and the exact
stored `.unenumerated (some handle) scs` slot. Conclusion:

```lean
∃ value,
  lookupNode caller.checked.native.machine.heap handle = some value ∧
  Available caller.checked.native.machine.heap value ∧ value.free = [] ∧
  MergedOrdinaryHeight.recursiveBoundary value = true ∧ scs = []
```

This is not a Mu classification. The exact definition at
`lean/MicroCFTA/MergedOrdinaryHeight.lean:89` is:

```lean
def recursiveBoundary : Value Symbol Guard → Bool
  | .mu .. | .union .. => true
  | _ => false
```

NativeIndex.candidate in SourcePruningEnumerationNativeIndex.lean:17 uses the
literal negation `!(recursiveBoundary decodedValue && scs.isEmpty)`.
A union with an empty bucket is therefore as unexpandable as a Mu with one.
DONE excludes pending ordinary/Empty native handles, but not pending unions.

CurrentProgramEagerResources.accepted and CurrentProgramEagerOutputs.accepted
supply DONE output control for their stable real-narrow worker family. The
current audit is conditional on an ACTUAL DONE output. It does not promote
stable-family coverage to every original supplied budget or every stopped
snapshot. Earlier emitted outputs after a later stop remain in the full goal.

### The full Mu equality is already proved

`MicroCFTA.SourceSynthesisCurrentUniverseClosedMuClassification.current_stored_universe_closed_mu_eq_after_growth`
`lean/MicroCFTA/SourceSynthesisCurrentUniverseClosedMuClassification.lean:17`

Its original accepted-source/build/stored-U inputs remain essential. At the
actual grown heap it additionally needs Facts, Grows from that same sourceHeap,
Available for the candidate Mu, closedness, and:

```lean
∀ atom ∈ atoms (.mu other otherBody otherDepth otherOrdinary),
  atom = .mu entry.identity
```

Its conclusion is FULL value equality:

```lean
Value.mu other otherBody otherDepth otherOrdinary = .mu entry body depth ordinary
```

Thus the body, ordinary payload, depth and interned entry all agree. The proof
uses `closed_identity_injective` from
SourceSynthesisUniverseMixedDescendantFreshness.lean:35 and actual coherent
complete physical readback. It does not merely compare markers or atom lists.

Atoms stops at a Mu and records its identity. The full-payload equality follows
from same-heap availability/coherence, not from inspecting a Mu body in atoms.
A fresh narrowed Mu identity cannot satisfy the stated only-U premise. A
candidate with the same identity and a different body cannot satisfy the full
physical coherence premises. No new body-equality theorem is needed here.

`MicroCFTA.SourcePruningEnumerationIdentity.lookup_encode`
`lean/MicroCFTA/SourcePruningEnumerationIdentity.lean:11`

Given Coherent and the actual successful lookup, this theorem yields
`encodeNode value = some handle`. After substituting full Mu equality, the
exact raw handle is `entry.identity + 1`. Do not stop at atom-identity equality
or introduce another handle-injectivity provider.

### Generated closure is local, not emitted-slot coverage

`MicroCFTA.SourceSynthesisCurrentUniverseGeneratedTypeClosure.current_stored_universe_closed_type_intersection_atoms`
`lean/MicroCFTA/SourceSynthesisCurrentUniverseGeneratedTypeClosure.lean:69`

For the SAME accepted source/build/stored U, source-grown heap and valid domain
cache, it takes TWO closed available operands whose atoms are already only U.
For every supplied native fuel it returns a Checked result for the literal
empty-domain kernel execute, with the same only-U property at successful results.
The stronger first conjunct of `current_stored_universe_coupled_fuel_atoms`
also retains result availability and closedness. Both exact headers are copied.

This theorem does not state that arbitrary closed values in every grown heap
have only U atoms. It does not classify every native result table, every warm
query, or every pending enumeration slot. Grows alone cannot supply that claim.
Do not replace its two operand atom premises with Program/Type guard roles.

`MicroCFTA.SourceSynthesisCurrentUniverseStartupAtoms.current_stored_universe_closed_startup_value_atoms`
`lean/MicroCFTA/SourceSynthesisCurrentUniverseStartupAtoms.lean:66`

This DOES derive only-U atoms for every closed available value in the ORIGINAL
completed sourceHeap. It is a genuine initializer producer. Its Available
premise is at sourceHeap, not an arbitrary later heap. The after-growth theorem
at line 158 has the reverse role: GIVEN only-U atoms, derive closedness. It does
not derive only-U atoms from closedness after growth.

`MicroCFTA.SourceSynthesisCurrentComponentFieldNativeAtoms.current_component_fields_cold_native_result_atoms`
`lean/MicroCFTA/SourceSynthesisCurrentComponentFieldNativeAtoms.lean:35`

An existing stronger concrete local producer already connects actual source
component first-slot calls to a completed COLD native query. It derives operand
availability/closedness/annotations/only-U atoms, exact kernel correspondence
via native_node_correct, and the same properties at the returned value.
Its machine is sourceHeap + empty domain cache and its thunks are initial.
It takes actual native completion plus its bounds. It explicitly does not
establish source root-worker reachability or all warm/reached calls. Reuse this
producer rather than duplicating it or counting it as whole-slot coverage.

The actual SharedIncomingNode source calls NativeDemand on the literal
empty-domain request for incoming and old. A separate existing actual shared
incoming observer preserves the successful native demand, actual phase/check,
result availability, extension and initial native step. That supplies real
operational receipts. It does not by itself derive only-U operands or a complete
emitted-slot induction.

## What Program/Type roles actually say

`ProgramSlots` in SourceSynthesisProgramEnumerationRoles.lean:48 marks Program
positions. It preserves allocated Program roots, IncomingAvoid and either
ValueFields for a pending native Program value or FragmentRoles for an expanded
Program fragment. The module explicitly leaves Type children unrestricted.

`ValueFields` in SourceSynthesisHereditaryProgramFields.lean:24 permits only
Empty and ordinary Program heads. Its row certificate records the literal
Program layout and Annotated guards for Type fields. `Annotated` in
SourceEqualityAnnotationLanguage.lean:16 includes arbitrary references, unions
and Mu bodies whose EDGE GUARDS satisfy the supplied predicate. It does not
restrict Mu identities, node symbols, native handle identity, or inhabitance.
Original mixed Type-slot and later local class-slot laws retain those same
annotation/route predicates. They are not only-U certificates.

Consequently, one can combine DONE boundary classification with ProgramSlots
and the ValueFields constructors to rule out a marked Program slot remaining
pending. That is a direct consequence of the inspected definitions, not a new
checked theorem in this packet. It does not define a complementary complete
Type-slot role or prove an only-U property for every unmarked slot.

## First missing producer and the union branch

The first required source-grounded producer should state, for the actual
original-source emitted cache at its exact native endpoint: every actual
retained graph-bearing pending slot's decoded value has only the SAME stored
U atom. Derive it through the actual source/row/child/native/projection/merge
and cache-restoration operations. Preserve raw slot/handle identity and the
original sourceHeap/U throughout. Do not take the property as a future model,
inhabitance or whole-history provider premise.

A live-slot/actual-operand induction is the relevant obligation. An invariant
for ALL closed values in an arbitrarily grown physical heap is stronger and
is not a consequence of the checked returned-value closure theorem. Intermediate
or abandoned records should not be confused with actual retained domains.

After that result, Mu leaves are handled by the existing full classifier and
lookup inverse. Explicit unions still need an actual producer. The exact
`InternedBoundaryAtoms.atoms` definition traverses union members, so a union may
have only U atoms while still containing ordinary members. The exact makeUnion
code in InternedConstructorTemplates.lean:275 has a genuine explicit-union
branch whenever multiple distinct surviving members are not all ordinary nodes.
It does not automatically replace U plus another member by U.

No source-reachable example of that situation is asserted. Conversely, no
inspected source theorem excludes it from every actual DONE Type slot. A proof
of semantic equality/inclusion or a concrete finite member for such a union may
be sufficient for assignment construction, even when exact handle equality is
too strong. That would be a different explicit result, not proof that every
handle literally is U. It must be derived from actual union provenance.

The original source may also have no stored Mu. The startup atom producer has
an explicit no-Mu/one-owner split. A theorem for all accepted sources must handle
the no-owner case; it cannot add existence of stored U to the original request.
The current Mu classifier and generated closure are conditional on an actual
stored U and should retain that scope.

## Other assignment boundaries

Node=None slots bypass NativeIndex.candidate: it returns false regardless of
bucket contents. DONE therefore does not establish their bucket=[] property.
`ProperState` in EnumerationProgress.lean:28 would supply that property, but
Packet in SourcePruningEnumerationRecursivePacket.lean:21 has no ProperState
field. Do not infer it from Packet or DONE without the actual source producer.
The question in this audit concerns graph-bearing native handles only.

Even exact-U pending domains with empty PRESENT buckets would establish only
one component of finite assignment construction. Historical removed buckets,
all parent fragment equations, aliases, residuals, actual root readback and
accepted completion of the SAME original root still have to hold under ONE rho.
DONE does not reconstruct cleared obligations. Other components must not receive
independently chosen assignments and then be combined without proof.

Only this new audit directory was written. No live source, compiler, Git, board,
Haskell or /tmp was changed. No new runtime defect or Haskell fix is claimed.
