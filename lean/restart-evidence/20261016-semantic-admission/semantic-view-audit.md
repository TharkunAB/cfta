# Stored input views, exact ranks, and cache admission

Read-only audit. Checked on 2026-10-16 at repository HEAD
`f37a8fe5bfd794693bcdc1c10a3a59b288421119`. No Lean build, Haskell execution,
or proof-source edit was performed. The theorem signatures below were read
from source. Proposed transport lemmas are not claimed as proved.

## Result

Actual heap growth preserves the literal view fields on old complete resident
inputs. It can therefore preserve `InputDerivation` at the **same rank** on
the old finite, reference-closed input domain. The stored view does not call
an unfolding operation or allocate identities. A new mutual derivation
transport lemma is still needed. No existing exact-rank transport theorem
was found in the inspected modules.

This result does not admit generated operands to an old model. It also does
not derive admission of captured memo requests from physical cache validity.
These are separate obligations.

## The actual read operations

* `SourcePreparedSharedRows.lean:26–27` defines
  `read state identity := (state.nodes.issued identity).bind state.nodeRecords`.
  This is a read of two stored maps. It does not call `nodeEdges` or `unfold`.
* `SourceRecursiveIntersectionInputView.lean:31–39` defines `payload`. For a
  node, Mu, or union tag, it uses that read and checks the complete tag with
  `inputOf value = input`. A missing or wrong-tag read gives `.empty`.
* `SourceRecursiveIntersectionInputView.lean:75–86` defines `view`.
  `rows` copies the original ordinary rows with exact guards and ordered
  `inputOf` children. `body` returns `inputOf` of the **stored original Mu
  body**. `members` copies the stored union members. `free` reads cached free
  names. `copy` uses `shape`; its Mu case copies the original body and omits
  the stored depth and ordinary probes (`shape`, lines 42–49).
* `SourceRecursiveIntersectionInputIdentity.lean:15–16` defines
  `representative state name := inputOf ((read state name).getD .empty)`.
* In contrast, `SourcePreparedSharedRows.rows` at lines 50–56 selects a
  completed `MergedSourceExposure.nodeEdges` result. Its `read_finite` and
  `rows_read` require the prepared-cache context and return the same prepared
  cache. **The input view does not call this `rows` function.**
* Actual stored unfolding is a different operation:
  `InternedFreshOrdinaryStoredSubstitution.lean:76–85` runs fresh construction
  of an encoded body under the recursive replacement environment. Its
  returned output or heap can depend on actual construction. That operation
  is absent from the definitions of `view` and `representative` above.

Consequently, allocating an exposed ordinary head does not change the old
Mu's stored body edge or introduce a new identity into that old view read.
The exposed result itself can be a new input that requires new admission.

## Existing exact readback and growth contracts

`SourcePreparedSharedRows.read_identity` (`SourcePreparedSharedRows.lean:82`):

```lean
(state) (facts : Facts state) (value) (available : Available state value)
(identity : Nat) (same : reference value = some identity) :
  read state identity = some value
```

`SourceRecursiveIntersectionInputView.payload_readback`
(`SourceRecursiveIntersectionInputView.lean:105`):

```lean
(state) (facts : Facts state) (value) (available : Available state value)
(input : Input)
(complete : IntersectionFlatMemoKey.input value.referenceOf = some input) :
  payload state input = value
```

`representative_record` (`SourceRecursiveIntersectionInputIdentity.lean:19`)
has the same state/facts/value/available/name premises and
`reference value = some name`; its conclusion is
`representative state name = inputOf value`.

`payload_grows` (`SourceRecursiveIntersectionInputGrowth.lean:15`):

```lean
(before after) (beforeFacts : Facts before) (afterFacts : Facts after)
(growth : Grows before after)
(history : Extends before.nodes.issued after.nodes.issued)
(value) (available : Available before value) (input : Input)
(complete : IntersectionFlatMemoKey.input value.referenceOf = some input) :
  payload after input = payload before input
```

The same module proves exact `free_grows` (line 32), `copy_grows` (40),
`body_grows` (48), `rows_grows` (57), and `members_grows` (66). Each takes
both `Facts`, actual `Grows`, and issued `Extends`. The final operand is
`OriginalInput before input`, with the corresponding Mu/node/union tag for
body/rows/members. Guard interpretation `holds` stays fixed.

`growthAgreement` (`SourceRecursiveIntersectionScheduleGrowth.lean:16`)
packages those laws as:

```lean
(before after) (beforeFacts : Facts before) (afterFacts : Facts after)
(growth : Grows before after)
(history : Extends before.nodes.issued after.nodes.issued) (holds) :
  ViewAgreement (view before holds) (view after holds) (OriginalInput before)
```

`SourceEqualityRequiredCache.Keeps` (`SourceEqualityRequiredCache.lean:25`)
contains `Ready after`, the full `Grows before after`, and issued `Extends`.
With initial facts from initial readiness or `Good`, this supplies the
growth premises. `Grows` alone is insufficient: its four fields retain
canonical and record maps, but do not retain the issued map
(`InternedConstructorTemplates.lean:78–82`). `Available.grows` also explicitly
requires issued `Extends` (`InternedProbeProvenance.lean:52–60`).

## Exact-rank transport: minimum next proof

`InputDerivation` (`IntersectInput.lean:15–32`) reads only ordinary rows,
Mu bodies, and union members. Its binder/reference rules preserve the
literal smaller rank with `<`; the union and forest rules retain their
literal `≤` bounds. Thus a mutual induction can preserve each rank without
inflating it.

The generic proposed contract is:

```lean
(same : ViewAgreement beforeView afterView valid)
(references : ∀ name, valid (.ref name) → valid (.mu name)) :
  ∀ input, valid input → ∀ rank term,
    InputDerivation afterView input rank term ↔
      InputDerivation beforeView input rank term
```

The forest motive needs validity of each member of the input list. Both
directions use the same original-domain row/body/member closure. In the
reverse direction, rewrite new row/member membership with the field
equalities before invoking that closure.

The extra `references` premise is necessary for this route.
`ViewAgreement` itself has no such field
(`IntersectViewAgreement.lean:15–23`). `OriginalInput before (.ref name)`
only gives a reserved available reference; it does not by itself give a
completed stored Mu at that name. Do not claim derivation invariance for
every arbitrary open `OriginalInput` on the strength of `growthAgreement`
alone. This is a proof-domain warning, not a new checked counterexample.

Use the old finite closed-root domain instead. Its
`FiniteInput.reference_valid` supplies this premise
(`IntersectInput.lean:83`). `closed_reach_original`
(`SourceRecursiveIntersectionInputInventory.lean:104–109`) supplies original
complete records throughout that domain, including the resolved Mu.
`SourceCurrentAllocatedNativeInputInventoryModels.reachable_original`
at lines 36–44 applies this to a finite root list. Restrict
`growthAgreement` to that domain.

Then prove reachability stability for the same old roots by induction on
`InputReach`, in both directions. With both finite models admitting the old
input, `finiteRanks_exact` (`IntersectInput.lean:94–117`) turns same-rank
derivation equivalence into exact `inputAt` equivalence. Taking `∃ rank`
gives language equivalence (`finiteLanguages_exact`, lines 124–131).
`finiteInputMeaning.languages` is exactly `finiteLanguages` (185–187), and
`finiteRankedInput.languages` is exactly `finiteRanks` (228–229).

Do not assert equality of the total view or of the total rank family across
heaps. A previously absent identity reads `.empty`; a later stored record
can change that default. Equality is scoped to old admitted identities.
The current same-source `SourceCurrentAllocatedNativeInputModelTransport`
avoids this issue: both inventories have the same view and representative,
so its global rank/language equalities are valid in that narrower scope.

## Physical cache validity does not supply admission

* `SourceCurrentAllocatedNativePhysicalCache.lean:20–38`: `NodeGood` gives
  `NodeReady` in every phase, plus returned `Available`; `EdgeGood` gives
  `EdgeReady` plus returned `EdgeResident`. `Valid` adds kernel validity and
  actual key-linked flat memo validity. It mentions no input model.
* `SourceRecursiveIntersectionThunks.lean:39–44`: `NodeReady` is exactly
  `Domain machine request.domain ∧ Available heap left ∧ Available heap right`.
  `EdgeReady` substitutes physical row residency. Neither includes
  `Original`, `model.valid`, reachability from old roots, or closedness.
* `SourceCurrentAllocatedNativeContextCache.lean:22–35`: `NodeInputs` adds
  both `Original` and both fixed-model validity premises. `EdgeInputs` adds
  the corresponding facts for every original row child. `NodeLaw` and
  `EdgeLaw` take these predicates as antecedents (lines 54–81).
  `Contextual` only stores those conditional laws (144–149).

For example, an empty finite root list has no valid inputs. Every
`NodeInputs` antecedent is then false. Node contextual laws can hold for
arbitrary returned values, so they cannot supply old admission of existing
node cells. Child-bearing edge cells have the same issue. This
definition-level obstruction does not need a language or runtime failure.

`SourceCurrentAllocatedNativeWarmQuery.query_complete` explicitly requires
`Available source` for both operands and `inputs.valid` for both inputs
(lines 72–90). Its receipt does not remove those premises. A generated
closed result can be `Original` and available in the current heap while
still being outside the old root model.

## Next cache bridge and remaining limits

Retain an independent admission invariant for returned captured requests.
Derive it at each actual publication/completion from the request's operand
lineage, and retain it through lookup, demand, finish, and heap growth.
Do not derive it from a conditional `NodeLaw` or `Contextual` proof.

For cross-heap contextual-law transport, old operand admission alone is
not the complete scoped agreement contract. Also retain agreement for
each identity in the captured `request.domain.key.seen` pairs.
`SoundPairs` and `CompletePairs` directly use those identities
(`SourceCurrentAllocatedNativePairContexts.lean:29–36`). The actual enter
schedule adds pairs of current input identities, so this belongs in the
same admission/lineage invariant. The existing `NodeScope` only retains
original available operands and original binder reads; it does not assert
finite-root reachability (`SourceRecursiveIntersectionRequestScope.lean:20–33`).

After those facts are derived, rebase the admitted old cells to the larger
current finite model using scoped exact rank/language agreement. Admit the
new closed generated operands as explicit roots of that current model.
This preserves the same actual native memo and operation state. It does
not reset tables or assume a future successful result.

Actual GHC heap publication, machine identity capacity, and source runtime
readback remain separate from these resident-model lemmas. This audit does
not establish the semantic common-language law for an entire dynamic class
query or general outer constrained-reduction termination.
