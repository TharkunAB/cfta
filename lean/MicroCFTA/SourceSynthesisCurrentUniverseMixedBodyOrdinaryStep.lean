import MicroCFTA.SourceSynthesisCurrentUniverseBodyChildClassification
import MicroCFTA.SourceSynthesisCurrentUniverseNodeAtomInductionSteps
import MicroCFTA.SourceSynthesisCurrentUniverseStartupAtoms
import MicroCFTA.SourceSynthesisUniverseClosedResetSteps

/-!
# The actual ordinary mixed-body branch under lower-fuel induction

The source body supplies original reference children or a closed marker.
Reference children use the lower-fuel mixed induction hypothesis.
Closed marker children use the actual closed-call reset before empty-domain induction.
The auxiliary theorem retains the actual ordinary branch selection.
The complete coupled generated-Type theorem remains open.
-/
namespace MicroCFTA.SourceSynthesisCurrentUniverseMixedBodyOrdinaryStep
open Cache InternedConstructorTemplates InternedNestedFacts InternedProbeProvenance
open InternedBinderProtocol (NodeKey Reference)
open InternedBoundaryAtoms InternedEdgeResidency
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionControl
open SourceSynthesisUniversePrefixHeight (height)

set_option autoImplicit false

section Generic
variable {Symbol Guard : Type}

/-- Actual ordered node calls use only lower-fuel reference and closed-reset cases. -/
private theorem ordered_mixed_node_atoms_of_fuel_induction
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (fuel : Nat)
    (domain : Interned IntersectionFlatMemoKeyDomain.DomainKey)
    (nonempty : domain.key.free.isEmpty = false) (ownerId ceiling : Nat)
    (bodyRows operandRows : List (EdgeValue Symbol Guard))
    (state : Machine Symbol Guard) (valid : SourceRecursiveIntersectionKernel.Valid state)
    (known : Domain state domain)
    (bodyResident : ∀ row ∈ bodyRows, EdgeResident state.heap row)
    (operandResident : ∀ row ∈ operandRows, EdgeResident state.heap row)
    (requests : ∀ bodyRow ∈ bodyRows, ∀ operandRow ∈ operandRows,
      ∀ bodyChild ∈ bodyRow.children, ∀ operandChild ∈ operandRow.children,
      (bodyChild = .reference (.interned ownerId) ∨
        (Available state.heap bodyChild ∧ bodyChild.free = [] ∧ atoms bodyChild = [])) ∧
      Available state.heap operandChild ∧ operandChild.free = [] ∧
      (∀ atom ∈ atoms operandChild, atom = .mu ownerId) ∧ height operandChild < ceiling)
    (closedInduction : ∀ smaller : Nat, smaller < fuel →
      ∀ current : Machine Symbol Guard, SourceRecursiveIntersectionKernel.Valid current →
      Extension state current → ∀ left right : Value Symbol Guard,
      Available current.heap left → Available current.heap right → left.free = [] → right.free = [] →
      (∀ atom ∈ atoms left, atom = .mu ownerId) →
      (∀ atom ∈ atoms right, atom = .mu ownerId) →
      ∀ (value : Value Symbol Guard) (after : Machine Symbol Guard),
      execute emptyGuard conjoin smaller IntersectionEmptyDomain.emptyDomain left right current = .done value after →
      ∀ atom ∈ atoms value, atom = .mu ownerId)
    (referenceInduction : ∀ current : Machine Symbol Guard,
      SourceRecursiveIntersectionKernel.Valid current → Extension state current →
      ∀ operand : Value Symbol Guard, Available current.heap operand → operand.free = [] →
      (∀ atom ∈ atoms operand, atom = .mu ownerId) → height operand < ceiling →
      ∀ bodyFirst : Bool, ∀ (value : Value Symbol Guard) (after : Machine Symbol Guard),
      (if bodyFirst then execute emptyGuard conjoin fuel domain (.reference (.interned ownerId)) operand current
        else execute emptyGuard conjoin fuel domain operand (.reference (.interned ownerId)) current) = .done value after →
      ∀ atom ∈ atoms value, atom = .mu ownerId)
    (bodyFirst : Bool) :
    Checked state
      (if bodyFirst then node emptyGuard conjoin (execute emptyGuard conjoin fuel domain) bodyRows operandRows state
        else node emptyGuard conjoin (execute emptyGuard conjoin fuel domain) operandRows bodyRows state)
      (fun after value => Available after.heap value ∧ ∀ atom ∈ atoms value, atom = .mu ownerId) := by
  have childStep (bodyRow : EdgeValue Symbol Guard) (bodyMember : bodyRow ∈ bodyRows)
      (operandRow : EdgeValue Symbol Guard) (operandMember : operandRow ∈ operandRows)
      (bodyChild : Value Symbol Guard) (bodyIncluded : bodyChild ∈ bodyRow.children)
      (operandChild : Value Symbol Guard) (operandIncluded : operandChild ∈ operandRow.children)
      (current : Machine Symbol Guard) (currentValid : SourceRecursiveIntersectionKernel.Valid current)
      (growth : Extension state current) (bodyFirst : Bool)
      (value : Value Symbol Guard) (after : Machine Symbol Guard)
      (returned : (if bodyFirst then execute emptyGuard conjoin fuel domain bodyChild operandChild current
        else execute emptyGuard conjoin fuel domain operandChild bodyChild current) = .done value after) :
      ∀ atom ∈ atoms value, atom = .mu ownerId := by
    have supplied := requests bodyRow bodyMember operandRow operandMember
      bodyChild bodyIncluded operandChild operandIncluded
    have operandAvailable := growth.available operandChild supplied.2.1
    rcases supplied.1 with originalReference | marker
    · rw [originalReference] at returned
      exact referenceInduction current currentValid growth operandChild operandAvailable
        supplied.2.2.1 supplied.2.2.2.1 supplied.2.2.2.2 bodyFirst value after returned
    · have markerAvailable := growth.available bodyChild marker.1
      have markerAtoms : ∀ atom ∈ atoms bodyChild, atom = .mu ownerId := by
        intro atom occurrence
        rw [marker.2.2] at occurrence
        cases occurrence
      have currentKnown := known.grows domain growth
      cases bodyFirst with
      | false =>
          have native := SourceSynthesisUniverseClosedResetSteps.closed_reset_atoms_of_fuel_induction
            emptyGuard conjoin fuel domain nonempty ownerId operandChild bodyChild
            supplied.2.2.1 marker.2.1 current currentValid currentKnown operandAvailable markerAvailable
            (fun smaller below value after done => closedInduction smaller below current currentValid growth
              operandChild bodyChild operandAvailable markerAvailable supplied.2.2.1 marker.2.1
              supplied.2.2.2.1 markerAtoms value after done)
          exact (native.result value after returned).2
      | true =>
          have native := SourceSynthesisUniverseClosedResetSteps.closed_reset_atoms_of_fuel_induction
            emptyGuard conjoin fuel domain nonempty ownerId bodyChild operandChild
            marker.2.1 supplied.2.2.1 current currentValid currentKnown markerAvailable operandAvailable
            (fun smaller below value after done => closedInduction smaller below current currentValid growth
              bodyChild operandChild markerAvailable operandAvailable marker.2.1 supplied.2.2.1
              markerAtoms supplied.2.2.2.1 value after done)
          exact (native.result value after returned).2
  cases bodyFirst with
  | false =>
      apply SourceSynthesisCurrentUniverseNodeAtomInductionSteps.ordered_node_atoms_of_fuel_induction
        emptyGuard conjoin fuel domain operandRows bodyRows state valid known operandResident bodyResident ownerId
      intro pair matched children zipped current currentValid growth value after returned
      have rows := (pairs_member operandRows bodyRows pair).mp matched
      have included := List.of_mem_zip zipped
      exact childStep pair.2 rows.2.1 pair.1 rows.1 children.2 included.2 children.1 included.1
        current currentValid growth false value after returned
  | true =>
      apply SourceSynthesisCurrentUniverseNodeAtomInductionSteps.ordered_node_atoms_of_fuel_induction
        emptyGuard conjoin fuel domain bodyRows operandRows state valid known bodyResident operandResident ownerId
      intro pair matched children zipped current currentValid growth value after returned
      have rows := (pairs_member bodyRows operandRows pair).mp matched
      have included := List.of_mem_zip zipped
      exact childStep pair.1 rows.1 pair.2 rows.2.1 children.1 included.1 children.2 included.2
        current currentValid growth true value after returned

/-- A selected ordinary call on two literal nodes executes the actual ordered payload. -/
private theorem execute_selected_ordinary_nodes
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (fuel : Nat)
    (domain : Interned IntersectionFlatMemoKeyDomain.DomainKey)
    (leftEntry : Interned NodeKey) (leftRows : List (EdgeValue Symbol Guard))
    (leftDepth : Nat) (leftFree : List Reference)
    (rightEntry : Interned NodeKey) (rightRows : List (EdgeValue Symbol Guard))
    (rightDepth : Nat) (rightFree : List Reference) (state : Machine Symbol Guard)
    (selected : decision domain.key (.node leftEntry leftRows leftDepth leftFree)
      (.node rightEntry rightRows rightDepth rightFree) = .ordinary) :
    execute emptyGuard conjoin (fuel + 1) domain
      (.node leftEntry leftRows leftDepth leftFree) (.node rightEntry rightRows rightDepth rightFree) state =
      node emptyGuard conjoin (execute emptyGuard conjoin fuel domain) leftRows rightRows state := by
  simp only [execute, onNode, selected]

end Generic

open SourceSynthesisTypeSyntax (Library Query)
open SourceSynthesisGeneralizeSyntax (Guard top)
open SourceSynthesisFirstOrderConstruction (Expression)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "ordinarySymbols" => SourceSynthesisUniverseCallerBoundary.ordinarySymbols

/-- The actual selected ordinary mixed-body call derives its child cases from the same source. -/
theorem current_stored_universe_body_ordinary_atoms_of_fuel_induction
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
        ∀ (value : Value Symbol Guard) (after : Machine Symbol Guard),
        execute top SourceEqualityPCSNativeEdge.conjoin smaller IntersectionEmptyDomain.emptyDomain left right current =
          .done value after → ∀ atom ∈ atoms value, atom = .mu entry.identity) →
      (∀ current : Machine Symbol Guard, SourceRecursiveIntersectionKernel.Valid current → Extension later current →
        ∀ child : Value Symbol Guard, Available current.heap child → child.free = [] →
        (∀ atom ∈ atoms child, atom = .mu entry.identity) → height child < height pattern →
        ∀ bodyFirst : Bool, ∀ (value : Value Symbol Guard) (after : Machine Symbol Guard),
        (if bodyFirst then execute top SourceEqualityPCSNativeEdge.conjoin fuel entered.1
            (.reference (.interned entry.identity)) child current
          else execute top SourceEqualityPCSNativeEdge.conjoin fuel entered.1
            child (.reference (.interned entry.identity)) current) = .done value after →
        ∀ atom ∈ atoms value, atom = .mu entry.identity) →
      ∀ bodyFirst : Bool,
      decision entered.1.key (if bodyFirst then body else operand) (if bodyFirst then operand else body) = .ordinary →
      Checked later (execute top SourceEqualityPCSNativeEdge.conjoin (fuel + 1) entered.1
        (if bodyFirst then body else operand) (if bodyFirst then operand else body) later)
        (fun after value => Available after.heap value ∧ value.free = [] ∧
          ∀ atom ∈ atoms value, atom = .mu entry.identity) := by
  let universeValue : Value Symbol Guard := .mu entry body depth ordinary
  let entered := SourceRecursiveIntersectionEnvironment.enter domains IntersectionEmptyDomain.emptyKey
    universeValue pattern entry.identity patternId
  let initial : Machine Symbol Guard := ⟨heap, entered.2⟩
  dsimp only
  intro later laterValid continuation operandEntry operandRows operandDepth operandFree
  intro operandAvailable operandClosed operandAtoms bounded closedInduction referenceInduction bodyFirst selected
  have universeAvailable : Available heap universeValue :=
    facts.cached.nodes key _ (growth.nodeRecords key _ stored)
  have allocation := SourceRecursiveIntersectionKernel.entered
    (⟨heap, domains⟩ : Machine Symbol Guard) ⟨facts, cacheValid⟩
    IntersectionEmptyDomain.emptyDomain (empty_domain _) universeValue pattern
    universeAvailable patternAvailable entry.identity patternId
  have known : Domain later entered.1 := allocation.2.2.grows entered.1 continuation
  have nonempty : entered.1.key.free.isEmpty = false :=
    SourceSynthesisUniverseClosedResetSteps.mixed_entry_nonempty_free_map
      domains cacheValid entry body depth ordinary pattern patternId
  obtain ⟨bodyEntry, bodyRows, bodyEq, bodyAvailable, requests⟩ :=
    SourceSynthesisCurrentUniverseBodyChildClassification.current_stored_universe_body_ordinary_child_requests_after_mixed_extension
      lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
      heap facts growth domains cacheValid pattern patternAvailable patternClosed patternId patternIdentity
      later laterValid continuation operandEntry operandRows operandDepth operandFree
      operandAvailable operandClosed operandAtoms bounded
  have bodyResident : ∀ row ∈ bodyRows, EdgeResident later.heap row := by
    intro row member
    have actualBody : Available later.heap (.node bodyEntry bodyRows 0 [.interned entry.identity]) := by
      rw [← bodyEq]
      exact bodyAvailable
    exact laterValid.1.linked bodyEntry.key _ (actualBody.resident bodyEntry rfl) row member
  have operandResident : ∀ row ∈ operandRows, EdgeResident later.heap row := by
    intro row member
    exact laterValid.1.linked operandEntry.key _ (operandAvailable.resident operandEntry rfl) row member
  have physical : ∀ bodyRow ∈ bodyRows, ∀ operandRow ∈ operandRows,
      ∀ bodyChild ∈ bodyRow.children, ∀ operandChild ∈ operandRow.children,
      (bodyChild = .reference (.interned entry.identity) ∨
        (Available later.heap bodyChild ∧ bodyChild.free = [] ∧ atoms bodyChild = [])) ∧
      Available later.heap operandChild ∧ operandChild.free = [] ∧
      (∀ atom ∈ atoms operandChild, atom = .mu entry.identity) ∧ height operandChild < height pattern := by
    intro bodyRow bodyMember operandRow operandMember bodyChild bodyIncluded operandChild operandIncluded
    have supplied := (requests bodyRow bodyMember operandRow operandMember).2.2
      bodyChild bodyIncluded operandChild operandIncluded
    exact ⟨supplied.1, supplied.2.1, supplied.2.2.1, supplied.2.2.2.1, supplied.2.2.2.2.1⟩
  have payload := ordered_mixed_node_atoms_of_fuel_induction
    top SourceEqualityPCSNativeEdge.conjoin fuel entered.1 nonempty entry.identity (height pattern)
    bodyRows operandRows later laterValid known bodyResident operandResident physical
    closedInduction referenceInduction bodyFirst
  have native : Checked later (execute top SourceEqualityPCSNativeEdge.conjoin (fuel + 1) entered.1
      (if bodyFirst then body else .node operandEntry operandRows operandDepth operandFree)
      (if bodyFirst then .node operandEntry operandRows operandDepth operandFree else body) later)
      (fun after value => Available after.heap value ∧ ∀ atom ∈ atoms value, atom = .mu entry.identity) := by
    cases bodyFirst with
    | false =>
        change decision entered.1.key (.node operandEntry operandRows operandDepth operandFree) body = .ordinary at selected
        change Checked later
          (node top SourceEqualityPCSNativeEdge.conjoin (execute top SourceEqualityPCSNativeEdge.conjoin fuel entered.1)
            operandRows bodyRows later)
          (fun after value => Available after.heap value ∧ ∀ atom ∈ atoms value, atom = .mu entry.identity) at payload
        change Checked later
          (execute top SourceEqualityPCSNativeEdge.conjoin (fuel + 1) entered.1
            (.node operandEntry operandRows operandDepth operandFree) body later)
          (fun after value => Available after.heap value ∧ ∀ atom ∈ atoms value, atom = .mu entry.identity)
        have selectedMoved := congrArg
          (fun candidate : Value Symbol Guard =>
            decision entered.1.key (.node operandEntry operandRows operandDepth operandFree) candidate) bodyEq
        have exactSelected : decision entered.1.key (.node operandEntry operandRows operandDepth operandFree)
            (.node bodyEntry bodyRows 0 [.interned entry.identity]) = .ordinary :=
          selectedMoved.symm.trans selected
        have operandMoved := congrArg
          (fun candidate : Value Symbol Guard => execute top SourceEqualityPCSNativeEdge.conjoin (fuel + 1)
            entered.1 (.node operandEntry operandRows operandDepth operandFree) candidate later) bodyEq
        have actual := operandMoved.trans (execute_selected_ordinary_nodes
          top SourceEqualityPCSNativeEdge.conjoin fuel entered.1
          operandEntry operandRows operandDepth operandFree bodyEntry bodyRows 0 [.interned entry.identity]
          later exactSelected)
        exact actual.symm ▸ payload
    | true =>
        change decision entered.1.key body (.node operandEntry operandRows operandDepth operandFree) = .ordinary at selected
        change Checked later
          (node top SourceEqualityPCSNativeEdge.conjoin (execute top SourceEqualityPCSNativeEdge.conjoin fuel entered.1)
            bodyRows operandRows later)
          (fun after value => Available after.heap value ∧ ∀ atom ∈ atoms value, atom = .mu entry.identity) at payload
        change Checked later
          (execute top SourceEqualityPCSNativeEdge.conjoin (fuel + 1) entered.1
            body (.node operandEntry operandRows operandDepth operandFree) later)
          (fun after value => Available after.heap value ∧ ∀ atom ∈ atoms value, atom = .mu entry.identity)
        have selectedMoved := congrArg
          (fun candidate : Value Symbol Guard =>
            decision entered.1.key candidate (.node operandEntry operandRows operandDepth operandFree)) bodyEq
        have exactSelected : decision entered.1.key (.node bodyEntry bodyRows 0 [.interned entry.identity])
            (.node operandEntry operandRows operandDepth operandFree) = .ordinary :=
          selectedMoved.symm.trans selected
        have operandMoved := congrArg
          (fun candidate : Value Symbol Guard => execute top SourceEqualityPCSNativeEdge.conjoin (fuel + 1)
            entered.1 candidate (.node operandEntry operandRows operandDepth operandFree) later) bodyEq
        have actual := operandMoved.trans (execute_selected_ordinary_nodes
          top SourceEqualityPCSNativeEdge.conjoin fuel entered.1
          bodyEntry bodyRows 0 [.interned entry.identity] operandEntry operandRows operandDepth operandFree
          later exactSelected)
        exact actual.symm ▸ payload
  refine ⟨native.valid, native.extension, ?_⟩
  intro value after returned
  have supplied := native.result value after returned
  have endpoint :
      (execute top SourceEqualityPCSNativeEdge.conjoin (fuel + 1) entered.1
        (if bodyFirst then body else .node operandEntry operandRows operandDepth operandFree)
        (if bodyFirst then .node operandEntry operandRows operandDepth operandFree else body) later).state = after :=
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

end MicroCFTA.SourceSynthesisCurrentUniverseMixedBodyOrdinaryStep
