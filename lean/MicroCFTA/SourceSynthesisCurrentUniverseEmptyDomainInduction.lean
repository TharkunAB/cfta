import MicroCFTA.SourceSynthesisCurrentUniverseClosedMuClassification
import MicroCFTA.SourceSynthesisCurrentUniverseNodeAtomInductionSteps
import MicroCFTA.SourceSynthesisCurrentUniverseBodyChildClassification
import MicroCFTA.SourceSynthesisCurrentUniverseMuAtomInductionStep

namespace MicroCFTA.SourceSynthesisCurrentUniverseEmptyDomainInduction
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

set_option maxHeartbeats 2000000 in
/-- The whole empty-domain step uses both original conjuncts only at smaller fuel. -/
theorem current_stored_universe_empty_domain_of_coupled_fuel_induction
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (lib : Library) (query : Query) (signed : Int) (whole : Expression)
    (accepted : SourceSynthesisCurrentConstruction.firstOrderRaw lib query signed = .ok whole)
    (rootValue : Value Symbol Guard) (sourceHeap : State Symbol Guard)
    (built : InternedFreshOrdinaryConstruction.build (ordinarySymbols whole) [] empty =
      .done rootValue sourceHeap)
    (key : NodeKey) (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (stored : sourceHeap.nodeRecords key = some (.mu entry body depth ordinary))
    (fuel : Nat)
    (fuelInduction : ∀ smaller : Nat, smaller < fuel →
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
      (left right : Value Symbol Guard),
      Available heap left → Available heap right → left.free = [] → right.free = [] →
      (∀ atom ∈ InternedBoundaryAtoms.atoms left, atom = .mu entry.identity) →
      (∀ atom ∈ InternedBoundaryAtoms.atoms right, atom = .mu entry.identity) →
      let initial : Machine Symbol Guard := ⟨heap, domains⟩
      Checked initial
        (execute top SourceEqualityPCSNativeEdge.conjoin fuel IntersectionEmptyDomain.emptyDomain left right initial)
        (fun after value => Available after.heap value ∧ value.free = [] ∧
          ∀ atom ∈ InternedBoundaryAtoms.atoms value, atom = .mu entry.identity)) := by
  intro heap facts growth domains cacheValid left right leftAvailable rightAvailable
  intro leftClosed rightClosed leftAtoms rightAtoms
  let initial : Machine Symbol Guard := ⟨heap, domains⟩
  let universeValue : Value Symbol Guard := .mu entry body depth ordinary
  have initialValid : Valid initial := ⟨facts, cacheValid⟩
  have native := execute_checked top SourceEqualityPCSNativeEdge.conjoin fuel
    IntersectionEmptyDomain.emptyDomain left right initial initialValid
    (empty_domain initial) leftAvailable rightAvailable
  refine ⟨native.valid, native.extension, ?_⟩
  intro value after returned
  change execute top SourceEqualityPCSNativeEdge.conjoin fuel
    IntersectionEmptyDomain.emptyDomain left right initial = .done value after at returned
  have reached :
      (execute top SourceEqualityPCSNativeEdge.conjoin fuel
        IntersectionEmptyDomain.emptyDomain left right initial).state = after :=
    congrArg Result.state returned
  have available : Available after.heap value := native.result value after returned
  have afterValid : Valid after := reached ▸ native.valid
  have afterExtension : Extension initial after := reached ▸ native.extension
  have resultAtoms : ∀ atom ∈ atoms value, atom = .mu entry.identity := by
    cases fuel with
    | zero =>
        simp only [execute] at returned
        cases returned
    | succ childFuel =>
        have lower := fuelInduction childFuel (Nat.lt_succ_self childFuel)
        by_cases empty : hasEmpty left right = true
        · have branch := empty_first IntersectionEmptyDomain.emptyDomain.key left right empty
          have observed := returned
          simp only [execute, onNode, branch] at observed
          cases observed
          intro atom occurrence
          simp only [atoms, List.not_mem_nil] at occurrence
        have noEmpty : hasEmpty left right = false := by
          cases observed : hasEmpty left right with
          | false => rfl
          | true => exact False.elim (empty observed)
        have noReset : reset IntersectionEmptyDomain.emptyDomain.key left right = false := by
          exact Bool.and_false (left.free.isEmpty && right.free.isEmpty)
        by_cases self : closedSelf left right = true
        · have branch := self_first IntersectionEmptyDomain.emptyDomain.key left right noEmpty noReset self
          have observed := returned
          simp only [execute, onNode, branch] at observed
          cases observed
          exact leftAtoms
        have noSelf : closedSelf left right = false := by
          cases observed : closedSelf left right with
          | false => rfl
          | true => exact False.elim (self observed)
        by_cases swap : greater left right = true
        · have branch := swap_first IntersectionEmptyDomain.emptyDomain.key left right
            noEmpty noReset noSelf swap
          have observed := returned
          simp only [execute, onNode, branch] at observed
          have checked := lower.1 heap facts growth domains cacheValid right left
            rightAvailable leftAvailable rightClosed leftClosed rightAtoms leftAtoms
          exact (checked.result value after observed).2.2
        have noSwap : greater left right = false := by
          cases observed : greater left right with
          | false => rfl
          | true => exact False.elim (swap observed)
        have inputIdentity (input : Value Symbol Guard) (closed : input.free = [])
            (nonempty : input ≠ .empty) : ∃ name : Nat, identity input = some name := by
          cases input with
          | empty => exact False.elim (nonempty rfl)
          | reference _name => cases closed
          | node own _rows _level _free => exact ⟨own.identity, rfl⟩
          | mu own _body _depth _ordinary => exact ⟨own.identity, rfl⟩
          | union own _members _level _free => exact ⟨own.identity, rfl⟩
        have leftNonempty : left ≠ .empty := by
          intro same
          rw [same] at noEmpty
          simp [hasEmpty, Value.referenceOf] at noEmpty
        have rightNonempty : right ≠ .empty := by
          intro same
          rw [same] at noEmpty
          simp [hasEmpty, Value.referenceOf] at noEmpty
        obtain ⟨leftId, leftIdentity⟩ := inputIdentity left leftClosed leftNonempty
        obtain ⟨rightId, rightIdentity⟩ := inputIdentity right rightClosed rightNonempty
        have selectedPayload : decision IntersectionEmptyDomain.emptyDomain.key left right = payload left right := by
          change (if hasEmpty left right then .empty
            else if reset IntersectionEmptyDomain.emptyDomain.key left right then .reset
            else if closedSelf left right then .self
            else if greater left right then .swap
            else match identity left, identity right with
              | some first, some second =>
                  if pair first second ∈ ([] : List (Nat × Nat)) then .repeated (pair first second)
                  else payload left right
              | _, _ => .unsupported) = payload left right
          simp only [noEmpty, noReset, noSelf, noSwap, Bool.false_eq_true, ite_false,
            leftIdentity, rightIdentity, List.not_mem_nil]
        have unionWalk
            (own : Interned NodeKey) (members : List (Value Symbol Guard))
            (level : Nat) (free : List Reference) (other : Value Symbol Guard) (side : Bool)
            (unionAvailable : Available heap (.union own members level free))
            (unionClosed : (Value.union own members level free).free = [])
            (unionAtoms : ∀ atom ∈ atoms (.union own members level free), atom = .mu entry.identity)
            (otherAvailable : Available heap other) (otherClosed : other.free = [])
            (otherAtoms : ∀ atom ∈ atoms other, atom = .mu entry.identity) :
            Checked initial
              ((walk (fun member current =>
                if side then execute top SourceEqualityPCSNativeEdge.conjoin childFuel
                  IntersectionEmptyDomain.emptyDomain member other current
                else execute top SourceEqualityPCSNativeEdge.conjoin childFuel
                  IntersectionEmptyDomain.emptyDomain other member current) members initial).bind
                (fun values final => work (makeUnion values) final))
              (fun final result => Available final.heap result ∧
                ∀ atom ∈ atoms result, atom = .mu entry.identity) := by
          apply SourceSynthesisCurrentUniverseAtomInductionSteps.ordered_union_atoms_of_fuel_induction
            top SourceEqualityPCSNativeEdge.conjoin childFuel IntersectionEmptyDomain.emptyDomain
            members other side initial initialValid (empty_domain initial) otherAvailable
            (fun member included => unionAvailable.children member (by simpa only [children] using included))
            entry.identity
          intro member included current currentValid continuation result final done
          have memberInputs := SourceSynthesisCurrentUniverseAtomInductionSteps.union_member_closed_atoms
            heap facts entry.identity own members level free unionAvailable unionClosed unionAtoms member included
          have currentGrowth : Grows sourceHeap current.heap := grows_trans growth continuation.heap
          cases side with
          | false =>
              change execute top SourceEqualityPCSNativeEdge.conjoin childFuel
                IntersectionEmptyDomain.emptyDomain other member current = .done result final at done
              have checked := lower.1 current.heap currentValid.1 currentGrowth current.domains currentValid.2
                other member (continuation.available other otherAvailable)
                (continuation.available member memberInputs.1) otherClosed memberInputs.2.1
                otherAtoms memberInputs.2.2
              exact (checked.result result final done).2.2
          | true =>
              change execute top SourceEqualityPCSNativeEdge.conjoin childFuel
                IntersectionEmptyDomain.emptyDomain member other current = .done result final at done
              have checked := lower.1 current.heap currentValid.1 currentGrowth current.domains currentValid.2
                member other (continuation.available member memberInputs.1)
                (continuation.available other otherAvailable) memberInputs.2.1 otherClosed
                memberInputs.2.2 otherAtoms
              exact (checked.result result final done).2.2
        have muRequest
            (pattern : Value Symbol Guard) (patternId : Nat)
            (patternIdentity : identity pattern = some patternId)
            (patternShape : tag pattern = 1 ∨ tag pattern = 3)
            (patternAvailable : Available heap pattern) (patternClosed : pattern.free = [])
            (patternAtoms : ∀ atom ∈ atoms pattern, atom = .mu entry.identity)
            (side : Bool)
            (selected : decision IntersectionEmptyDomain.emptyDomain.key
              (if side then universeValue else pattern) (if side then pattern else universeValue) =
              (if side then .leftMu else .rightMu)) :
            Checked initial
              (execute top SourceEqualityPCSNativeEdge.conjoin (childFuel + 1)
                IntersectionEmptyDomain.emptyDomain (if side then universeValue else pattern)
                (if side then pattern else universeValue) initial)
              (fun final result => Available final.heap result ∧ result.free = [] ∧
                ∀ atom ∈ atoms result, atom = .mu entry.identity) := by
          have universeAvailable : Available heap universeValue :=
            facts.cached.nodes key _ (growth.nodeRecords key _ stored)
          let entered := SourceRecursiveIntersectionEnvironment.enter domains IntersectionEmptyDomain.emptyKey
            universeValue pattern entry.identity patternId
          let current : Machine Symbol Guard := ⟨heap, entered.2⟩
          have allocation := SourceRecursiveIntersectionKernel.entered initial initialValid
            IntersectionEmptyDomain.emptyDomain (empty_domain initial)
            universeValue pattern universeAvailable patternAvailable entry.identity patternId
          obtain ⟨bodyEntry, _marker, arrow, rows, bodyEq, _remaining⟩ :=
            SourceSynthesisCurrentUniverseBodyChildClassification.current_stored_universe_body_physical_children_after_growth
              lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
              heap facts growth
          have bodyNotReference : body ≠ .reference (.interned entry.identity) := by
            intro impossible
            rw [bodyEq] at impossible
            cases impossible
          have mixed := lower.2 heap facts growth domains cacheValid pattern patternId
            patternAvailable patternClosed patternIdentity patternShape current allocation.1
            (Extension.refl current) body (Or.inl rfl) pattern patternAvailable patternClosed patternAtoms
            (Nat.le_refl _) (fun same => False.elim (bodyNotReference same))
          refine SourceSynthesisCurrentUniverseMuAtomInductionStep.current_stored_universe_selected_mu_atoms_of_mixed_induction
            lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
            heap facts growth domains cacheValid pattern patternAvailable patternClosed patternAtoms
            patternId patternIdentity patternShape childFuel side selected ?_
          cases side with
          | false => exact mixed.2
          | true => exact mixed.1
        cases left <;> cases right
        all_goals try solve | cases leftClosed
        all_goals try solve | cases rightClosed
        all_goals try solve | cases leftIdentity
        all_goals try solve | cases rightIdentity
        case node.node first firstRows firstLevel firstFree second secondRows secondLevel secondFree =>
          have selected : decision IntersectionEmptyDomain.emptyDomain.key
              (.node first firstRows firstLevel firstFree) (.node second secondRows secondLevel secondFree) = .ordinary := by
            simpa only [payload] using selectedPayload
          have checked := SourceSynthesisCurrentUniverseNodeAtomInductionSteps.ordinary_closed_nodes_atoms_of_fuel_induction
            top SourceEqualityPCSNativeEdge.conjoin childFuel IntersectionEmptyDomain.emptyDomain
            first second firstRows secondRows firstLevel secondLevel firstFree secondFree initial initialValid
            (empty_domain initial) entry.identity leftAvailable rightAvailable leftClosed rightClosed
            leftAtoms rightAtoms selected
            (by
              intro firstChild secondChild current currentValid continuation firstAvailable secondAvailable
              intro firstClosed secondClosed firstAtoms secondAtoms result final done
              have checked := lower.1 current.heap currentValid.1 (grows_trans growth continuation.heap)
                current.domains currentValid.2 firstChild secondChild firstAvailable secondAvailable
                firstClosed secondClosed firstAtoms secondAtoms
              exact (checked.result result final done).2.2)
          exact (checked.result value after returned).2
        case node.union own rows level free other members otherLevel otherFree =>
          have selected : decision IntersectionEmptyDomain.emptyDomain.key
              (.node own rows level free) (.union other members otherLevel otherFree) = .rightUnion := by
            simpa only [payload] using selectedPayload
          have checked := unionWalk other members otherLevel otherFree (.node own rows level free) false
            rightAvailable rightClosed rightAtoms leftAvailable leftClosed leftAtoms
          have observed := returned
          simp only [execute, onNode, selected] at observed
          exact (checked.result value after observed).2
        case union.node own members level free other rows otherLevel otherFree =>
          have selected : decision IntersectionEmptyDomain.emptyDomain.key
              (.union own members level free) (.node other rows otherLevel otherFree) = .leftUnion := by
            simpa only [payload] using selectedPayload
          have checked := unionWalk own members level free (.node other rows otherLevel otherFree) true
            leftAvailable leftClosed leftAtoms rightAvailable rightClosed rightAtoms
          have observed := returned
          simp only [execute, onNode, selected] at observed
          exact (checked.result value after observed).2
        case union.union own members level free other otherMembers otherLevel otherFree =>
          have selected : decision IntersectionEmptyDomain.emptyDomain.key
              (.union own members level free) (.union other otherMembers otherLevel otherFree) = .leftUnion := by
            simpa only [payload] using selectedPayload
          have checked := unionWalk own members level free (.union other otherMembers otherLevel otherFree) true
            leftAvailable leftClosed leftAtoms rightAvailable rightClosed rightAtoms
          have observed := returned
          simp only [execute, onNode, selected] at observed
          exact (checked.result value after observed).2
        case mu.node own ownBody ownDepth ownOrdinary other rows level free =>
          have same : Value.mu own ownBody ownDepth ownOrdinary = universeValue :=
            SourceSynthesisCurrentUniverseClosedMuClassification.current_stored_universe_closed_mu_eq_after_growth
              lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
              heap facts growth own ownBody ownDepth ownOrdinary leftAvailable leftClosed leftAtoms
          have selected : decision IntersectionEmptyDomain.emptyDomain.key
              (.mu own ownBody ownDepth ownOrdinary) (.node other rows level free) = .leftMu := by
            simpa only [payload] using selectedPayload
          have observed := returned
          rw [same] at selected observed
          have checked := muRequest (.node other rows level free) other.identity rfl (Or.inl rfl)
            rightAvailable rightClosed rightAtoms true selected
          exact (checked.result value after observed).2.2
        case mu.union own ownBody ownDepth ownOrdinary other members level free =>
          have same : Value.mu own ownBody ownDepth ownOrdinary = universeValue :=
            SourceSynthesisCurrentUniverseClosedMuClassification.current_stored_universe_closed_mu_eq_after_growth
              lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
              heap facts growth own ownBody ownDepth ownOrdinary leftAvailable leftClosed leftAtoms
          have selected : decision IntersectionEmptyDomain.emptyDomain.key
              (.mu own ownBody ownDepth ownOrdinary) (.union other members level free) = .leftMu := by
            simpa only [payload] using selectedPayload
          have observed := returned
          rw [same] at selected observed
          have checked := muRequest (.union other members level free) other.identity rfl (Or.inr rfl)
            rightAvailable rightClosed rightAtoms true selected
          exact (checked.result value after observed).2.2
        case node.mu own rows level free other otherBody otherDepth otherOrdinary =>
          have same : Value.mu other otherBody otherDepth otherOrdinary = universeValue :=
            SourceSynthesisCurrentUniverseClosedMuClassification.current_stored_universe_closed_mu_eq_after_growth
              lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
              heap facts growth other otherBody otherDepth otherOrdinary rightAvailable rightClosed rightAtoms
          have selected : decision IntersectionEmptyDomain.emptyDomain.key
              (.node own rows level free) (.mu other otherBody otherDepth otherOrdinary) = .rightMu := by
            simpa only [payload] using selectedPayload
          have observed := returned
          rw [same] at selected observed
          have checked := muRequest (.node own rows level free) own.identity rfl (Or.inl rfl)
            leftAvailable leftClosed leftAtoms false selected
          exact (checked.result value after observed).2.2
        case union.mu own members level free other otherBody otherDepth otherOrdinary =>
          have same : Value.mu other otherBody otherDepth otherOrdinary = universeValue :=
            SourceSynthesisCurrentUniverseClosedMuClassification.current_stored_universe_closed_mu_eq_after_growth
              lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
              heap facts growth other otherBody otherDepth otherOrdinary rightAvailable rightClosed rightAtoms
          have selected : decision IntersectionEmptyDomain.emptyDomain.key
              (.union own members level free) (.mu other otherBody otherDepth otherOrdinary) = .rightMu := by
            simpa only [payload] using selectedPayload
          have observed := returned
          rw [same] at selected observed
          have checked := muRequest (.union own members level free) own.identity rfl (Or.inr rfl)
            leftAvailable leftClosed leftAtoms false selected
          exact (checked.result value after observed).2.2
        case mu.mu own ownBody ownDepth ownOrdinary other otherBody otherDepth otherOrdinary =>
          have firstSame : Value.mu own ownBody ownDepth ownOrdinary = universeValue :=
            SourceSynthesisCurrentUniverseClosedMuClassification.current_stored_universe_closed_mu_eq_after_growth
              lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
              heap facts growth own ownBody ownDepth ownOrdinary leftAvailable leftClosed leftAtoms
          have secondSame : Value.mu other otherBody otherDepth otherOrdinary = universeValue :=
            SourceSynthesisCurrentUniverseClosedMuClassification.current_stored_universe_closed_mu_eq_after_growth
              lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
              heap facts growth other otherBody otherDepth otherOrdinary rightAvailable rightClosed rightAtoms
          have universeClosed : universeValue.free = [] := by
            rw [← firstSame]
            exact leftClosed
          have reuse : closedSelf universeValue universeValue = true := by
            simp [closedSelf, universeClosed]
          rw [firstSame, secondSame, reuse] at noSelf
          cases noSelf
  refine ⟨available, ?_, resultAtoms⟩
  exact SourceSynthesisCurrentUniverseStartupAtoms.current_stored_universe_boundary_atoms_closed_after_growth
    lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
    after.heap afterValid.1 (grows_trans growth afterExtension.heap) value available resultAtoms

end MicroCFTA.SourceSynthesisCurrentUniverseEmptyDomainInduction
