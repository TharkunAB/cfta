import MicroCFTA.SourceSynthesisCurrentUniverseMixedBodyOrdinaryStep
import MicroCFTA.SourceSynthesisCurrentUniverseMixedBodyControl

/-!
# The actual body and closed-node case under coupled fuel induction

The original source and entered domain determine the native control branch.
The swap branch uses the lower-fuel mixed hypothesis on its reversed call.
The ordinary branch uses the actual ordered payload and closed-call reset.
Zero fuel retains the exhausted result and the same machine.
The full simultaneous generated-Type theorem remains open.
-/
namespace MicroCFTA.SourceSynthesisCurrentUniverseMixedBodyNodeInductionStep
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

/-- The actual body and closed-node call needs only the two strictly lower-fuel hypotheses. -/
theorem current_stored_universe_body_node_of_coupled_fuel_induction
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
    ∀ (operandEntry : Interned NodeKey) (operandRows : List (EdgeValue Symbol Guard))
      (operandDepth : Nat) (operandFree : List Reference),
      let operand : Value Symbol Guard := .node operandEntry operandRows operandDepth operandFree
      Available later.heap operand → operand.free = [] →
      (∀ atom ∈ atoms operand, atom = .mu entry.identity) → height operand ≤ height pattern →
      (∀ smaller : Nat, smaller < fuel → ∀ current : Machine Symbol Guard,
        SourceRecursiveIntersectionKernel.Valid current → Extension later current →
        ∀ left right : Value Symbol Guard, Available current.heap left → Available current.heap right →
        left.free = [] → right.free = [] →
        (∀ atom ∈ atoms left, atom = .mu entry.identity) →
        (∀ atom ∈ atoms right, atom = .mu entry.identity) →
        Checked current
          (execute top SourceEqualityPCSNativeEdge.conjoin smaller IntersectionEmptyDomain.emptyDomain left right current)
          (fun after value => Available after.heap value ∧ value.free = [] ∧
            ∀ atom ∈ atoms value, atom = .mu entry.identity)) →
      (∀ smaller : Nat, smaller < fuel → ∀ current : Machine Symbol Guard,
        SourceRecursiveIntersectionKernel.Valid current → Extension later current →
        ∀ openAlias : Value Symbol Guard, (openAlias = body ∨ openAlias = .reference (.interned entry.identity)) →
        ∀ closedOperand : Value Symbol Guard, Available current.heap closedOperand → closedOperand.free = [] →
        (∀ atom ∈ atoms closedOperand, atom = .mu entry.identity) → height closedOperand ≤ height pattern →
        (openAlias = .reference (.interned entry.identity) → height closedOperand < height pattern) →
        ∀ bodyFirst : Bool,
        Checked current
          (if bodyFirst then execute top SourceEqualityPCSNativeEdge.conjoin smaller entered.1 openAlias closedOperand current
            else execute top SourceEqualityPCSNativeEdge.conjoin smaller entered.1 closedOperand openAlias current)
          (fun after value => Available after.heap value ∧ value.free = [] ∧
            ∀ atom ∈ atoms value, atom = .mu entry.identity)) →
      ∀ bodyFirst : Bool,
      Checked later (execute top SourceEqualityPCSNativeEdge.conjoin fuel entered.1
        (if bodyFirst then body else operand) (if bodyFirst then operand else body) later)
        (fun after value => Available after.heap value ∧ value.free = [] ∧
          ∀ atom ∈ atoms value, atom = .mu entry.identity) := by
  let universeValue : Value Symbol Guard := .mu entry body depth ordinary
  let entered := SourceRecursiveIntersectionEnvironment.enter domains IntersectionEmptyDomain.emptyKey
    universeValue pattern entry.identity patternId
  let initial : Machine Symbol Guard := ⟨heap, entered.2⟩
  dsimp only
  intro later laterValid continuation operandEntry operandRows operandDepth operandFree
  intro operandAvailable operandClosed operandAtoms bounded closedInduction mixedInduction bodyFirst
  cases fuel with
  | zero =>
      exact checked_failed later laterValid .exhausted _
  | succ childFuel =>
      let operand : Value Symbol Guard := .node operandEntry operandRows operandDepth operandFree
      let left : Value Symbol Guard := if bodyFirst then body else operand
      let right : Value Symbol Guard := if bodyFirst then operand else body
      obtain ⟨bodyEntry, bodyRows, bodyEq, bodyAvailable, _bodyApart, _operandApart,
          _fresh, _reverseFresh, controls⟩ :=
        SourceSynthesisCurrentUniverseMixedBodyControl.current_stored_universe_body_ordinary_control_after_mixed_extension
          lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
          heap facts growth domains cacheValid pattern patternAvailable patternClosed patternId patternIdentity
          later laterValid continuation operandEntry operandRows operandDepth operandFree
          operandAvailable operandClosed operandAtoms bounded
      have controlled : decision entered.1.key left right = if greater left right then .swap else .ordinary :=
        controls bodyFirst
      have childBelow : childFuel < Nat.succ childFuel := Nat.lt_succ_self childFuel
      cases observed : greater left right with
      | false =>
          have selected : decision entered.1.key left right = .ordinary := by
            simpa [observed] using controlled
          refine SourceSynthesisCurrentUniverseMixedBodyOrdinaryStep.current_stored_universe_body_ordinary_atoms_of_fuel_induction
            lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
            heap facts growth domains cacheValid pattern patternAvailable patternClosed patternId patternIdentity childFuel
            later laterValid continuation operandEntry operandRows operandDepth operandFree
            operandAvailable operandClosed operandAtoms bounded ?_ ?_ bodyFirst selected
          · intro smaller below current currentValid extension first second firstAvailable secondAvailable
            intro firstClosed secondClosed firstAtoms secondAtoms value after returned
            have checked := closedInduction smaller (Nat.lt_trans below childBelow)
              current currentValid extension first second firstAvailable secondAvailable
              firstClosed secondClosed firstAtoms secondAtoms
            exact (checked.result value after returned).2.2
          · intro current currentValid extension child childAvailable childClosed childAtoms strict
            intro referenceFirst value after returned
            have checked := mixedInduction childFuel childBelow current currentValid extension
              (.reference (.interned entry.identity)) (Or.inr rfl)
              child childAvailable childClosed childAtoms (Nat.le_of_lt strict) (fun _ => strict) referenceFirst
            exact (checked.result value after returned).2.2
      | true =>
          have universeAvailable : Available heap universeValue :=
            facts.cached.nodes key _ (growth.nodeRecords key _ stored)
          have allocation := SourceRecursiveIntersectionKernel.entered
            (⟨heap, domains⟩ : Machine Symbol Guard) ⟨facts, cacheValid⟩
            IntersectionEmptyDomain.emptyDomain (empty_domain _) universeValue pattern
            universeAvailable patternAvailable entry.identity patternId
          have known : Domain later entered.1 := allocation.2.2.grows entered.1 continuation
          have leftAvailable : Available later.heap left := by
            cases bodyFirst with
            | false => exact operandAvailable
            | true => exact bodyAvailable
          have rightAvailable : Available later.heap right := by
            cases bodyFirst with
            | false => exact bodyAvailable
            | true => exact operandAvailable
          have bodyNotReference : body ≠ .reference (.interned entry.identity) := by
            intro impossible
            rw [bodyEq] at impossible
            cases impossible
          have native := SourceSynthesisCurrentUniverseMixedBodyControl.swap_atoms_of_fuel_induction
            top SourceEqualityPCSNativeEdge.conjoin childFuel entered.1 left right later
            laterValid known leftAvailable rightAvailable entry.identity controlled observed
            (by
              intro value after returned
              have checked := mixedInduction childFuel childBelow later laterValid (Extension.refl later)
                body (Or.inl rfl) operand operandAvailable operandClosed operandAtoms bounded
                (fun impossible => False.elim (bodyNotReference impossible)) (!bodyFirst)
              cases bodyFirst with
              | false => exact (checked.result value after returned).2.2
              | true => exact (checked.result value after returned).2.2)
          refine ⟨native.valid, native.extension, ?_⟩
          intro value after returned
          have supplied := native.result value after returned
          have endpoint :
              (execute top SourceEqualityPCSNativeEdge.conjoin (childFuel + 1) entered.1 left right later).state = after :=
            congrArg Result.state returned
          have afterValid : SourceRecursiveIntersectionKernel.Valid after := endpoint ▸ native.valid
          have afterExtension : Extension later after := endpoint ▸ native.extension
          have afterGrowth : Grows sourceHeap after.heap :=
            grows_trans growth (grows_trans continuation.heap afterExtension.heap)
          exact ⟨supplied.1,
            SourceSynthesisCurrentUniverseStartupAtoms.current_stored_universe_boundary_atoms_closed_after_growth
              lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
              after.heap afterValid.1 afterGrowth value supplied.1 supplied.2,
            supplied.2⟩

end MicroCFTA.SourceSynthesisCurrentUniverseMixedBodyNodeInductionStep

#print axioms MicroCFTA.SourceSynthesisCurrentUniverseMixedBodyNodeInductionStep.current_stored_universe_body_node_of_coupled_fuel_induction
