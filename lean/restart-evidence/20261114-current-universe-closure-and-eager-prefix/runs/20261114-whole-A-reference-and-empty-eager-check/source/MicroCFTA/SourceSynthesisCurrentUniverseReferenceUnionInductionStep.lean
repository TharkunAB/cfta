import MicroCFTA.SourceSynthesisCurrentUniverseReferenceDescendantSteps
import MicroCFTA.SourceSynthesisCurrentUniverseAtomInductionSteps
import MicroCFTA.SourceSynthesisCurrentUniverseStartupAtoms

/-!
# The original refU and closed-union case under lower-fuel M

Native union distribution precedes reference lookup.
Each ordered member call retains the original refU and entered domain.
The reverse orientation spends one additional fuel on sorting.
An empty member list can complete with zero child fuel.
The full simultaneous generated-Type theorem remains open.
-/
namespace MicroCFTA.SourceSynthesisCurrentUniverseReferenceUnionInductionStep
open Cache InternedConstructorTemplates InternedNestedFacts InternedProbeProvenance
open InternedBinderProtocol (NodeKey Reference)
open InternedBoundaryAtoms
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionControl
open SourceSynthesisUniversePrefixHeight (height)

set_option autoImplicit false

section Generic
variable {Symbol Guard : Type}

/-- Sorting a left reference retains the same machine and original domain before distribution. -/
private theorem reference_union_swap_step
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (fuel : Nat)
    (domain : Interned IntersectionFlatMemoKeyDomain.DomainKey) (name : Nat)
    (entry : Interned NodeKey) (members : List (Value Symbol Guard)) (level : Nat)
    (state : Machine Symbol Guard) :
    execute emptyGuard conjoin (fuel + 1) domain (.reference (.interned name))
        (.union entry members level []) state =
      execute emptyGuard conjoin fuel domain (.union entry members level []) (.reference (.interned name)) state := by
  have tagOrder : compare (4 : Nat) 3 = .gt := by decide
  have selected : decision domain.key (.reference (.interned name)) (.union entry members level []) = .swap := by
    simp [decision, hasEmpty, reset, closedSelf, greater, compareValue, tag,
      Value.referenceOf, Value.free, tagOrder]
  simp only [execute, onNode, selected]

end Generic

open SourceSynthesisTypeSyntax (Library Query)
open SourceSynthesisGeneralizeSyntax (Guard top)
open SourceSynthesisFirstOrderConstruction (Expression)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "ordinarySymbols" => SourceSynthesisUniverseCallerBoundary.ordinarySymbols

/-- Both original refU/union orders distribute using only strictly smaller original-domain M calls. -/
theorem current_stored_universe_reference_union_of_coupled_fuel_induction
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (lib : Library) (query : Query) (signed : Int) (whole : Expression)
    (accepted : SourceSynthesisCurrentConstruction.firstOrderRaw lib query signed = .ok whole)
    (rootValue : Value Symbol Guard) (sourceHeap : State Symbol Guard)
    (built : InternedFreshOrdinaryConstruction.build (ordinarySymbols whole) [] empty =
      .done rootValue sourceHeap)
    (key : NodeKey) (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (stored : sourceHeap.nodeRecords key = some (.mu entry body depth ordinary))
    (heap : State Symbol Guard) (facts : Facts heap) (growth : Grows sourceHeap heap)
    (domains : Cache.State IntersectionFlatMemoKeyDomain.DomainKey) (cacheValid : Cache.Valid domains)
    (pattern : Value Symbol Guard) (patternAvailable : Available heap pattern)
    (patternClosed : pattern.free = []) (patternId : Nat)
    (patternIdentity : identity pattern = some patternId) (fuel : Nat) :
    let universeValue : Value Symbol Guard := .mu entry body depth ordinary
    let entered := SourceRecursiveIntersectionEnvironment.enter domains IntersectionEmptyDomain.emptyKey
      universeValue pattern entry.identity patternId
    let initial : Machine Symbol Guard := ⟨heap, entered.2⟩
    ∀ later : Machine Symbol Guard, SourceRecursiveIntersectionKernel.Valid later → Extension initial later →
    ∀ (unionEntry : Interned NodeKey) (members : List (Value Symbol Guard))
      (unionDepth : Nat) (unionFree : List Reference),
      let operand : Value Symbol Guard := .union unionEntry members unionDepth unionFree
      Available later.heap operand → operand.free = [] →
      (∀ atom ∈ atoms operand, atom = .mu entry.identity) → height operand < height pattern →
      (∀ smaller : Nat, smaller < fuel → ∀ current : Machine Symbol Guard,
        SourceRecursiveIntersectionKernel.Valid current → Extension later current →
        ∀ openAlias : Value Symbol Guard, (openAlias = body ∨ openAlias = .reference (.interned entry.identity)) →
        ∀ closedOperand : Value Symbol Guard, Available current.heap closedOperand → closedOperand.free = [] →
        (∀ atom ∈ atoms closedOperand, atom = .mu entry.identity) → height closedOperand ≤ height pattern →
        (openAlias = .reference (.interned entry.identity) → height closedOperand < height pattern) →
        ∀ aliasFirst : Bool,
        Checked current
          (if aliasFirst then execute top SourceEqualityPCSNativeEdge.conjoin smaller entered.1 openAlias closedOperand current
            else execute top SourceEqualityPCSNativeEdge.conjoin smaller entered.1 closedOperand openAlias current)
          (fun after value => Available after.heap value ∧ value.free = [] ∧
            ∀ atom ∈ atoms value, atom = .mu entry.identity)) →
      ∀ referenceFirst : Bool,
      Checked later (execute top SourceEqualityPCSNativeEdge.conjoin fuel entered.1
        (if referenceFirst then .reference (.interned entry.identity) else operand)
        (if referenceFirst then operand else .reference (.interned entry.identity)) later)
        (fun after value => Available after.heap value ∧ value.free = [] ∧
          ∀ atom ∈ atoms value, atom = .mu entry.identity) := by
  let universeValue : Value Symbol Guard := .mu entry body depth ordinary
  let entered := SourceRecursiveIntersectionEnvironment.enter domains IntersectionEmptyDomain.emptyKey
    universeValue pattern entry.identity patternId
  let initial : Machine Symbol Guard := ⟨heap, entered.2⟩
  dsimp only
  intro later laterValid continuation unionEntry members unionDepth unionFree
  intro operandAvailable operandClosed operandAtoms strict mixedInduction referenceFirst
  have freeEmpty : unionFree = [] := operandClosed
  subst unionFree
  let operand : Value Symbol Guard := .union unionEntry members unionDepth []
  obtain ⟨_universeClosed, freshness⟩ :=
    SourceSynthesisUniverseMixedDescendantFreshness.current_stored_universe_strict_descendant_fresh_after_mixed_entry
      lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
      heap facts growth domains cacheValid pattern patternAvailable patternClosed patternId patternIdentity
  obtain ⟨_different, _directApart, _reverseApart, _directFresh, _reverseFresh, known, _found⟩ :=
    freshness later laterValid continuation operand operandAvailable operandClosed unionEntry.identity rfl strict
  have laterGrowth : Grows sourceHeap later.heap := grows_trans growth continuation.heap
  have ownerAvailable : Available later.heap universeValue :=
    laterValid.1.cached.nodes key _ (laterGrowth.nodeRecords key _ stored)
  have installed := InternedFreshProbeKeys.resident_entry later.heap laterValid.1.coherent
    universeValue ownerAvailable.resident entry rfl
  have issued := (laterValid.1.coherent.valid.2.2 entry.key entry installed).2
  have referenceAvailable : Available later.heap (.reference (.interned entry.identity)) := by
    apply reference_available
    intro name occurrence
    have same : name = entry.identity := by simpa [Value.free] using occurrence
    subst name
    exact ⟨entry.key, issued⟩
  have memberAvailable : ∀ member ∈ members, Available later.heap member := by
    intro member present
    exact (SourceSynthesisCurrentUniverseAtomInductionSteps.union_member_closed_atoms
      later.heap laterValid.1 entry.identity unionEntry members unionDepth []
      operandAvailable operandClosed operandAtoms member present).1
  have distribute (smaller : Nat) (below : smaller < fuel) :
      Checked later
        ((walk (fun member current => execute top SourceEqualityPCSNativeEdge.conjoin smaller entered.1
          member (.reference (.interned entry.identity)) current) members later).bind
          (fun values after => work (makeUnion values) after))
        (fun after value => Available after.heap value ∧ value.free = [] ∧
          ∀ atom ∈ atoms value, atom = .mu entry.identity) := by
    have payload := SourceSynthesisCurrentUniverseAtomInductionSteps.ordered_union_atoms_of_fuel_induction
      top SourceEqualityPCSNativeEdge.conjoin smaller entered.1 members (.reference (.interned entry.identity)) true
      later laterValid known referenceAvailable memberAvailable entry.identity
      (by
        intro member present current currentValid extension value after returned
        have memberFacts := SourceSynthesisCurrentUniverseAtomInductionSteps.union_member_closed_atoms
          later.heap laterValid.1 entry.identity unionEntry members unionDepth []
          operandAvailable operandClosed operandAtoms member present
        have memberStrict := Nat.lt_trans
          (SourceSynthesisUniversePrefixHeight.member_lt unionEntry members unionDepth [] member present) strict
        have checked := mixedInduction smaller below current currentValid extension
          (.reference (.interned entry.identity)) (Or.inr rfl)
          member (extension.available member memberFacts.1) memberFacts.2.1 memberFacts.2.2
          (Nat.le_of_lt memberStrict) (fun _ => memberStrict) false
        exact (checked.result value after returned).2.2)
    change Checked later
      ((walk (fun member current => execute top SourceEqualityPCSNativeEdge.conjoin smaller entered.1
        member (.reference (.interned entry.identity)) current) members later).bind
        (fun values after => work (makeUnion values) after))
      (fun after value => Available after.heap value ∧ ∀ atom ∈ atoms value, atom = .mu entry.identity) at payload
    refine ⟨payload.valid, payload.extension, ?_⟩
    intro value after returned
    have supplied := payload.result value after returned
    have endpoint :
        ((walk (fun member current => execute top SourceEqualityPCSNativeEdge.conjoin smaller entered.1
          member (.reference (.interned entry.identity)) current) members later).bind
          (fun values after => work (makeUnion values) after)).state = after :=
      congrArg Result.state returned
    have afterValid : SourceRecursiveIntersectionKernel.Valid after := endpoint ▸ payload.valid
    have afterExtension : Extension later after := endpoint ▸ payload.extension
    have afterGrowth : Grows sourceHeap after.heap := grows_trans laterGrowth afterExtension.heap
    exact ⟨supplied.1,
      SourceSynthesisCurrentUniverseStartupAtoms.current_stored_universe_boundary_atoms_closed_after_growth
        lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
        after.heap afterValid.1 afterGrowth value supplied.1 supplied.2,
      supplied.2⟩
  have complete :=
    SourceSynthesisCurrentUniverseReferenceDescendantSteps.current_stored_universe_union_reference_descendant_after_mixed_entry
      lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
      heap facts growth domains cacheValid pattern patternAvailable patternClosed patternId patternIdentity
      later laterValid continuation unionEntry members unionDepth operandAvailable strict
  cases referenceFirst with
  | false =>
      change Checked later
        (execute top SourceEqualityPCSNativeEdge.conjoin fuel entered.1 operand (.reference (.interned entry.identity)) later)
        (fun after value => Available after.heap value ∧ value.free = [] ∧
          ∀ atom ∈ atoms value, atom = .mu entry.identity)
      cases fuel with
      | zero => exact checked_failed later laterValid .exhausted _
      | succ smaller =>
          exact (complete smaller).1.symm ▸ distribute smaller (Nat.lt_succ_self smaller)
  | true =>
      change Checked later
        (execute top SourceEqualityPCSNativeEdge.conjoin fuel entered.1 (.reference (.interned entry.identity)) operand later)
        (fun after value => Available after.heap value ∧ value.free = [] ∧
          ∀ atom ∈ atoms value, atom = .mu entry.identity)
      cases fuel with
      | zero => exact checked_failed later laterValid .exhausted _
      | succ preceding =>
          cases preceding with
          | zero =>
              have exhausted : execute top SourceEqualityPCSNativeEdge.conjoin 1 entered.1
                  (.reference (.interned entry.identity)) operand later = .failed .exhausted later :=
                (reference_union_swap_step top SourceEqualityPCSNativeEdge.conjoin 0 entered.1 entry.identity
                  unionEntry members unionDepth later).trans rfl
              exact exhausted.symm ▸ checked_failed later laterValid .exhausted _
          | succ smaller =>
              exact (complete smaller).2.symm ▸ distribute smaller (by omega)

end MicroCFTA.SourceSynthesisCurrentUniverseReferenceUnionInductionStep

#print axioms MicroCFTA.SourceSynthesisCurrentUniverseReferenceUnionInductionStep.reference_union_swap_step
#print axioms MicroCFTA.SourceSynthesisCurrentUniverseReferenceUnionInductionStep.current_stored_universe_reference_union_of_coupled_fuel_induction
