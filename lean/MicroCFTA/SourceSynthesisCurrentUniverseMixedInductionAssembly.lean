import MicroCFTA.SourceSynthesisCurrentUniverseMixedBodyNodeInductionStep
import MicroCFTA.SourceSynthesisCurrentUniverseMixedBodyUnionInductionStep
import MicroCFTA.SourceSynthesisCurrentUniverseReferenceNodeInductionStep
import MicroCFTA.SourceSynthesisCurrentUniverseReferenceUnionInductionStep
import MicroCFTA.SourceSynthesisCurrentUniverseClosedMuClassification
import MicroCFTA.SourceSynthesisUniverseMixedEntryReplay

/-!
# The original mixed-domain conjunct under coupled strong fuel induction

Every smaller M request retains its original heap, cache, P and entered domain.
The checked structural cases cover the original body and original refU aliases.
The complete coupled theorem remains open until the A conjunct is assembled.
-/
namespace MicroCFTA.SourceSynthesisCurrentUniverseMixedInductionAssembly
open Cache InternedConstructorTemplates InternedNestedFacts InternedProbeProvenance
open InternedBinderProtocol (NodeKey Reference)
open InternedBoundaryAtoms
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionControl
open SourceSynthesisTypeSyntax (Library Query)
open SourceSynthesisGeneralizeSyntax (Guard top)
open SourceSynthesisFirstOrderConstruction (Expression)
open SourceSynthesisUniversePrefixHeight (height)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "ordinarySymbols" => SourceSynthesisUniverseCallerBoundary.ordinarySymbols

set_option autoImplicit false

/-- The exact original M conjunct follows from the exact coupled hypotheses at strictly smaller fuel. -/
theorem current_stored_universe_mixed_of_coupled_strong_induction
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (lib : Library) (query : Query) (signed : Int) (whole : Expression)
    (accepted : SourceSynthesisCurrentConstruction.firstOrderRaw lib query signed = .ok whole)
    (rootValue : Value Symbol Guard) (sourceHeap : State Symbol Guard)
    (built : InternedFreshOrdinaryConstruction.build (ordinarySymbols whole) [] empty =
      .done rootValue sourceHeap)
    (key : NodeKey) (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (stored : sourceHeap.nodeRecords key = some (.mu entry body depth ordinary))
    (fuel : Nat)
    (induction : ∀ smaller : Nat, smaller < fuel →
    (∀ (heap : State Symbol Guard) (_facts : Facts heap) (_growth : Grows sourceHeap heap)
      (domains : Cache.State IntersectionFlatMemoKeyDomain.DomainKey) (_cacheValid : Cache.Valid domains)
      (left right : Value Symbol Guard),
      Available heap left → Available heap right → left.free = [] → right.free = [] →
      (∀ atom ∈ InternedBoundaryAtoms.atoms left, atom = .mu entry.identity) →
      (∀ atom ∈ InternedBoundaryAtoms.atoms right, atom = .mu entry.identity) →
      let initial : Machine Symbol Guard := ⟨heap, domains⟩
      Checked initial
        (execute top SourceEqualityPCSNativeEdge.conjoin smaller IntersectionEmptyDomain.emptyDomain left right initial)
        (fun after value => Available after.heap value ∧ value.free = [] ∧
          ∀ atom ∈ InternedBoundaryAtoms.atoms value, atom = .mu entry.identity)) ∧
    (∀ (heap : State Symbol Guard) (_facts : Facts heap) (_growth : Grows sourceHeap heap)
      (domains : Cache.State IntersectionFlatMemoKeyDomain.DomainKey) (_cacheValid : Cache.Valid domains)
      (pattern : Value Symbol Guard) (patternId : Nat),
      Available heap pattern → pattern.free = [] →
      SourceRecursiveIntersectionControl.identity pattern = some patternId →
      (SourceRecursiveIntersectionControl.tag pattern = 1 ∨ SourceRecursiveIntersectionControl.tag pattern = 3) →
      let universeValue : Value Symbol Guard := .mu entry body depth ordinary
      let entered := SourceRecursiveIntersectionEnvironment.enter domains IntersectionEmptyDomain.emptyKey
        universeValue pattern entry.identity patternId
      let initial : Machine Symbol Guard := ⟨heap, entered.2⟩
      ∀ later : Machine Symbol Guard, SourceRecursiveIntersectionKernel.Valid later → Extension initial later →
      ∀ openAlias : Value Symbol Guard, (openAlias = body ∨ openAlias = .reference (.interned entry.identity)) →
      ∀ operand : Value Symbol Guard, Available later.heap operand → operand.free = [] →
      (∀ atom ∈ InternedBoundaryAtoms.atoms operand, atom = .mu entry.identity) →
      height operand ≤ height pattern →
      (openAlias = .reference (.interned entry.identity) → height operand < height pattern) →
      Checked later (execute top SourceEqualityPCSNativeEdge.conjoin smaller entered.1 openAlias operand later)
        (fun after value => Available after.heap value ∧ value.free = [] ∧
          ∀ atom ∈ InternedBoundaryAtoms.atoms value, atom = .mu entry.identity) ∧
      Checked later (execute top SourceEqualityPCSNativeEdge.conjoin smaller entered.1 operand openAlias later)
        (fun after value => Available after.heap value ∧ value.free = [] ∧
          ∀ atom ∈ InternedBoundaryAtoms.atoms value, atom = .mu entry.identity))) :
    (∀ (heap : State Symbol Guard) (_facts : Facts heap) (_growth : Grows sourceHeap heap)
      (domains : Cache.State IntersectionFlatMemoKeyDomain.DomainKey) (_cacheValid : Cache.Valid domains)
      (pattern : Value Symbol Guard) (patternId : Nat),
      Available heap pattern → pattern.free = [] →
      SourceRecursiveIntersectionControl.identity pattern = some patternId →
      (SourceRecursiveIntersectionControl.tag pattern = 1 ∨ SourceRecursiveIntersectionControl.tag pattern = 3) →
      let universeValue : Value Symbol Guard := .mu entry body depth ordinary
      let entered := SourceRecursiveIntersectionEnvironment.enter domains IntersectionEmptyDomain.emptyKey
        universeValue pattern entry.identity patternId
      let initial : Machine Symbol Guard := ⟨heap, entered.2⟩
      ∀ later : Machine Symbol Guard, SourceRecursiveIntersectionKernel.Valid later → Extension initial later →
      ∀ openAlias : Value Symbol Guard, (openAlias = body ∨ openAlias = .reference (.interned entry.identity)) →
      ∀ operand : Value Symbol Guard, Available later.heap operand → operand.free = [] →
      (∀ atom ∈ InternedBoundaryAtoms.atoms operand, atom = .mu entry.identity) →
      height operand ≤ height pattern →
      (openAlias = .reference (.interned entry.identity) → height operand < height pattern) →
      Checked later (execute top SourceEqualityPCSNativeEdge.conjoin fuel entered.1 openAlias operand later)
        (fun after value => Available after.heap value ∧ value.free = [] ∧
          ∀ atom ∈ InternedBoundaryAtoms.atoms value, atom = .mu entry.identity) ∧
      Checked later (execute top SourceEqualityPCSNativeEdge.conjoin fuel entered.1 operand openAlias later)
        (fun after value => Available after.heap value ∧ value.free = [] ∧
          ∀ atom ∈ InternedBoundaryAtoms.atoms value, atom = .mu entry.identity)) := by
  intro heap facts growth domains cacheValid pattern patternId
  intro patternAvailable patternClosed patternIdentity patternShape
  let universeValue : Value Symbol Guard := .mu entry body depth ordinary
  let entered := SourceRecursiveIntersectionEnvironment.enter domains IntersectionEmptyDomain.emptyKey
    universeValue pattern entry.identity patternId
  let initial : Machine Symbol Guard := ⟨heap, entered.2⟩
  dsimp only
  intro later laterValid continuation openAlias aliasFamily operand
  intro operandAvailable operandClosed operandAtoms bounded referenceStrict
  cases fuel with
  | zero =>
      exact ⟨checked_failed later laterValid .exhausted _, checked_failed later laterValid .exhausted _⟩
  | succ childFuel =>
      have laterGrowth : Grows sourceHeap later.heap := grows_trans growth continuation.heap
      have lowerA (smaller : Nat) (below : smaller < childFuel + 1)
          (current : Machine Symbol Guard) (currentValid : SourceRecursiveIntersectionKernel.Valid current)
          (extension : Extension later current)
          (left right : Value Symbol Guard) (leftAvailable : Available current.heap left)
          (rightAvailable : Available current.heap right) (leftClosed : left.free = []) (rightClosed : right.free = [])
          (leftAtoms : ∀ atom ∈ atoms left, atom = .mu entry.identity)
          (rightAtoms : ∀ atom ∈ atoms right, atom = .mu entry.identity) :
          Checked current
            (execute top SourceEqualityPCSNativeEdge.conjoin smaller IntersectionEmptyDomain.emptyDomain left right current)
            (fun after value => Available after.heap value ∧ value.free = [] ∧
              ∀ atom ∈ atoms value, atom = .mu entry.identity) := by
        exact (induction smaller below).1 current.heap currentValid.1
          (grows_trans laterGrowth extension.heap) current.domains currentValid.2 left right
          leftAvailable rightAvailable leftClosed rightClosed leftAtoms rightAtoms
      have lowerM (smaller : Nat) (below : smaller < childFuel + 1)
          (current : Machine Symbol Guard) (currentValid : SourceRecursiveIntersectionKernel.Valid current)
          (extension : Extension later current)
          (candidateAlias : Value Symbol Guard)
          (family : candidateAlias = body ∨ candidateAlias = .reference (.interned entry.identity))
          (closedOperand : Value Symbol Guard) (available : Available current.heap closedOperand)
          (closed : closedOperand.free = []) (onlyU : ∀ atom ∈ atoms closedOperand, atom = .mu entry.identity)
          (heightBound : height closedOperand ≤ height pattern)
          (strict : candidateAlias = .reference (.interned entry.identity) → height closedOperand < height pattern)
          (aliasFirst : Bool) :
          Checked current
            (if aliasFirst then execute top SourceEqualityPCSNativeEdge.conjoin smaller entered.1 candidateAlias closedOperand current
              else execute top SourceEqualityPCSNativeEdge.conjoin smaller entered.1 closedOperand candidateAlias current)
            (fun after value => Available after.heap value ∧ value.free = [] ∧
              ∀ atom ∈ atoms value, atom = .mu entry.identity) := by
        have original := (induction smaller below).2 heap facts growth domains cacheValid pattern patternId
          patternAvailable patternClosed patternIdentity patternShape current currentValid
          (continuation.trans extension) candidateAlias family closedOperand available closed onlyU heightBound strict
        cases aliasFirst with
        | false => exact original.2
        | true => exact original.1
      have universeAvailable : Available later.heap universeValue :=
        laterValid.1.cached.nodes key _ (laterGrowth.nodeRecords key _ stored)
      have universeClosed : universeValue.free = [] :=
        SourceSynthesisCurrentUniverseStartupAtoms.current_stored_universe_boundary_atoms_closed_after_growth
          lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
          later.heap laterValid.1 laterGrowth universeValue universeAvailable
          (by
            intro atom occurrence
            simpa only [universeValue, atoms, List.mem_singleton] using occurrence)
      obtain ⟨bodyEntry, _marker, arrow, rows, bodyEq, _bodyAvailable, _rest⟩ :=
        SourceSynthesisCurrentUniverseBodyChildClassification.current_stored_universe_body_physical_children_after_growth
          lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
          later.heap laterValid.1 laterGrowth
      have aliasOwner (candidateAlias : Value Symbol Guard)
          (family : candidateAlias = body ∨ candidateAlias = .reference (.interned entry.identity))
          (otherFuel : Nat) :
          Checked later (execute top SourceEqualityPCSNativeEdge.conjoin otherFuel entered.1 candidateAlias universeValue later)
            (fun after value => Available after.heap value ∧ value.free = [] ∧
              ∀ atom ∈ atoms value, atom = .mu entry.identity) := by
        have originalFamily : candidateAlias = .reference (.interned entry.identity) ∨ candidateAlias = body :=
          family.elim Or.inr Or.inl
        have checked :=
          (SourceSynthesisUniverseMixedEntryReplay.current_stored_universe_open_alias_checked_after_mixed_extension
            lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
            heap growth domains cacheValid pattern patternId patternAvailable patternClosed patternIdentity patternShape
            candidateAlias originalFamily later laterValid continuation).2 otherFuel
        refine ⟨checked.valid, checked.extension, ?_⟩
        intro value after returned
        have supplied := checked.result value after returned
        exact ⟨supplied.1, (congrArg Value.free supplied.2.1).trans universeClosed, supplied.2.2⟩
      have ownerBoth (candidateAlias : Value Symbol Guard)
          (family : candidateAlias = body ∨ candidateAlias = .reference (.interned entry.identity)) :
          Checked later (execute top SourceEqualityPCSNativeEdge.conjoin (childFuel + 1) entered.1 candidateAlias universeValue later)
            (fun after value => Available after.heap value ∧ value.free = [] ∧
              ∀ atom ∈ atoms value, atom = .mu entry.identity) ∧
          Checked later (execute top SourceEqualityPCSNativeEdge.conjoin (childFuel + 1) entered.1 universeValue candidateAlias later)
            (fun after value => Available after.heap value ∧ value.free = [] ∧
              ∀ atom ∈ atoms value, atom = .mu entry.identity) := by
        refine ⟨aliasOwner candidateAlias family (childFuel + 1), ?_⟩
        rcases family with originalBody | originalReference
        · subst candidateAlias
          have tagOrder : compare (2 : Nat) 1 = .gt := by decide
          have physicalSelected : decision entered.1.key universeValue
              (.node bodyEntry (canonicalEdges (arrow :: rows)) 0 [.interned entry.identity]) = .swap := by
            simp [universeValue, decision, hasEmpty, reset, closedSelf, greater, compareValue, tag,
              Value.referenceOf, Value.free, tagOrder]
          have moved := congrArg
            (fun candidate : Value Symbol Guard => decision entered.1.key universeValue candidate) bodyEq
          have selected : decision entered.1.key universeValue body = .swap := moved.trans physicalSelected
          have swapped : execute top SourceEqualityPCSNativeEdge.conjoin (childFuel + 1) entered.1 universeValue body later =
              execute top SourceEqualityPCSNativeEdge.conjoin childFuel entered.1 body universeValue later := by
            simp only [execute, onNode, selected]
          exact swapped.symm ▸ aliasOwner body (Or.inl rfl) childFuel
        · subst candidateAlias
          have tagOrder : compare (4 : Nat) 2 = .gt := by decide
          have selected : decision entered.1.key (.reference (.interned entry.identity)) universeValue = .swap := by
            simp [universeValue, decision, hasEmpty, reset, closedSelf, greater, compareValue, tag,
              Value.referenceOf, Value.free, tagOrder]
          have swapped : execute top SourceEqualityPCSNativeEdge.conjoin ((childFuel + 1) + 1) entered.1
                (.reference (.interned entry.identity)) universeValue later =
              execute top SourceEqualityPCSNativeEdge.conjoin (childFuel + 1) entered.1
                universeValue (.reference (.interned entry.identity)) later := by
            simp only [execute, onNode, selected]
          exact swapped ▸ aliasOwner (.reference (.interned entry.identity)) (Or.inr rfl) ((childFuel + 1) + 1)
      cases operand with
      | empty =>
          have returned : Checked later (.done (.empty : Value Symbol Guard) later)
              (fun after value => Available after.heap value ∧ value.free = [] ∧
                ∀ atom ∈ atoms value, atom = .mu entry.identity) := by
            apply checked_pure later laterValid
            refine ⟨empty_available later.heap, rfl, ?_⟩
            intro atom occurrence
            simp only [atoms, List.not_mem_nil] at occurrence
          have forward : execute top SourceEqualityPCSNativeEdge.conjoin (childFuel + 1) entered.1 openAlias .empty later =
              .done .empty later := by
            simp [execute, onNode, decision, hasEmpty, Value.referenceOf]
          have reverse : execute top SourceEqualityPCSNativeEdge.conjoin (childFuel + 1) entered.1 .empty openAlias later =
              .done .empty later := by
            simp [execute, onNode, decision, hasEmpty, Value.referenceOf]
          exact ⟨forward.symm ▸ returned, reverse.symm ▸ returned⟩
      | reference name =>
          change [name] = [] at operandClosed
          cases operandClosed
      | node operandEntry operandRows operandDepth operandFree =>
          rcases aliasFamily with originalBody | originalReference
          · subst openAlias
            have checked :=
              SourceSynthesisCurrentUniverseMixedBodyNodeInductionStep.current_stored_universe_body_node_of_coupled_fuel_induction
                lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
                heap facts growth domains cacheValid pattern patternAvailable patternClosed patternId patternIdentity (childFuel + 1)
                later laterValid continuation operandEntry operandRows operandDepth operandFree
                operandAvailable operandClosed operandAtoms bounded lowerA lowerM
            exact ⟨checked true, checked false⟩
          · subst openAlias
            have checked :=
              SourceSynthesisCurrentUniverseReferenceNodeInductionStep.current_stored_universe_reference_node_of_coupled_fuel_induction
                lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
                heap facts growth domains cacheValid pattern patternAvailable patternClosed patternId patternIdentity (childFuel + 1)
                later laterValid continuation operandEntry operandRows operandDepth operandFree
                operandAvailable operandClosed operandAtoms (referenceStrict rfl) lowerA
            exact ⟨checked true, checked false⟩
      | union unionEntry members unionDepth unionFree =>
          rcases aliasFamily with originalBody | originalReference
          · subst openAlias
            have checked :=
              SourceSynthesisCurrentUniverseMixedBodyUnionInductionStep.current_stored_universe_body_union_of_coupled_fuel_induction
                lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
                heap facts growth domains cacheValid pattern patternAvailable patternClosed patternId patternIdentity (childFuel + 1)
                later laterValid continuation unionEntry members unionDepth unionFree
                operandAvailable operandClosed operandAtoms bounded lowerM
            exact ⟨checked true, checked false⟩
          · subst openAlias
            have checked :=
              SourceSynthesisCurrentUniverseReferenceUnionInductionStep.current_stored_universe_reference_union_of_coupled_fuel_induction
                lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
                heap facts growth domains cacheValid pattern patternAvailable patternClosed patternId patternIdentity (childFuel + 1)
                later laterValid continuation unionEntry members unionDepth unionFree
                operandAvailable operandClosed operandAtoms (referenceStrict rfl) lowerM
            exact ⟨checked true, checked false⟩
      | mu other otherBody otherDepth otherOrdinary =>
          have same := SourceSynthesisCurrentUniverseClosedMuClassification.current_stored_universe_closed_mu_eq_after_growth
            lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
            later.heap laterValid.1 laterGrowth other otherBody otherDepth otherOrdinary
            operandAvailable operandClosed operandAtoms
          have moved := congrArg
            (fun candidate : Value Symbol Guard =>
              Checked later (execute top SourceEqualityPCSNativeEdge.conjoin (childFuel + 1) entered.1 openAlias candidate later)
                (fun after value => Available after.heap value ∧ value.free = [] ∧
                  ∀ atom ∈ atoms value, atom = .mu entry.identity) ∧
              Checked later (execute top SourceEqualityPCSNativeEdge.conjoin (childFuel + 1) entered.1 candidate openAlias later)
                (fun after value => Available after.heap value ∧ value.free = [] ∧
                  ∀ atom ∈ atoms value, atom = .mu entry.identity)) same
          exact Eq.mpr moved (ownerBoth openAlias aliasFamily)

end MicroCFTA.SourceSynthesisCurrentUniverseMixedInductionAssembly
