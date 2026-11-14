import MicroCFTA.SourceSynthesisCurrentUniverseBodyChildClassification
import MicroCFTA.SourceSynthesisCurrentUniverseAtomInductionSteps
import MicroCFTA.SourceSynthesisCurrentUniverseStartupAtoms
import MicroCFTA.SourceRecursiveIntersectionDomainEquivalence

/-!
# The original stored body and closed-union case under fuel induction

The source body is an open node. A right union runs its members in order.
Every member call retains the original body and original entered domain.
The reversed input spends one fuel on the actual swap.
The full simultaneous generated-Type theorem remains open.
-/
namespace MicroCFTA.SourceSynthesisCurrentUniverseMixedBodyUnionInductionStep
open Cache InternedConstructorTemplates InternedNestedFacts InternedProbeProvenance
open InternedBinderProtocol (NodeKey Reference)
open InternedBoundaryAtoms
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionControl
open SourceRecursiveIntersectionDomain
open SourceSynthesisUniversePrefixHeight (height)

set_option autoImplicit false

section Generic
variable {Symbol Guard : Type}

/-- Exact physical readback separates another complete record from the original Mu identity. -/
private theorem physical_identity_apart_owner
    (heap : State Symbol Guard) (facts : Facts heap)
    (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (ownerAvailable : Available heap (.mu entry body depth ordinary))
    (value : Value Symbol Guard) (available : Available heap value)
    (valueId : Nat) (valueIdentity : SourcePreparedSharedRows.reference value = some valueId)
    (different : value ≠ .mu entry body depth ordinary) : valueId ≠ entry.identity := by
  intro same
  have actualIdentity : SourcePreparedSharedRows.reference value = some entry.identity :=
    valueIdentity.trans (congrArg some same)
  have actualRead := SourcePreparedSharedRows.read_identity heap facts value available entry.identity actualIdentity
  have ownerRead := SourcePreparedSharedRows.read_identity heap facts
    (.mu entry body depth ordinary) ownerAvailable entry.identity rfl
  exact different (Option.some.inj (actualRead.symm.trans ownerRead))

/-- A pair with neither original owner identity cannot select its original seen pair. -/
private theorem pair_apart_owner (left right owner pattern : Nat)
    (leftApart : left ≠ owner) (rightApart : right ≠ owner) :
    pair left right ≠ pair owner pattern := by
  intro same
  have lower := congrArg Prod.fst same
  have upper := congrArg Prod.snd same
  simp only [pair] at lower upper
  omega

/-- The physical source node distributes over a right union; the reverse input sorts first. -/
private theorem body_union_branches
    (domain : Interned IntersectionFlatMemoKeyDomain.DomainKey) (ownerId : Nat)
    (bodyEntry : Interned NodeKey) (bodyRows : List (EdgeValue Symbol Guard))
    (unionEntry : Interned NodeKey) (members : List (Value Symbol Guard))
    (unionDepth : Nat) (unionFree : List Reference)
    (fresh : pair bodyEntry.identity unionEntry.identity ∉ domain.key.seen) :
    decision domain.key (.node bodyEntry bodyRows 0 [.interned ownerId])
        (.union unionEntry members unionDepth unionFree) = .rightUnion ∧
      decision domain.key (.union unionEntry members unionDepth unionFree)
        (.node bodyEntry bodyRows 0 [.interned ownerId]) = .swap := by
  have forwardOrder : compare (1 : Nat) 3 = .lt := by decide
  have reverseOrder : compare (3 : Nat) 1 = .gt := by decide
  constructor
  · simp [decision, hasEmpty, reset, closedSelf, greater, compareValue, tag, identity, payload,
      Value.referenceOf, Value.free, fresh, forwardOrder]
  · simp [decision, hasEmpty, reset, closedSelf, greater, compareValue, tag,
      Value.referenceOf, Value.free, reverseOrder]

end Generic

open SourceSynthesisTypeSyntax (Library Query)
open SourceSynthesisGeneralizeSyntax (Guard top)
open SourceSynthesisFirstOrderConstruction (Expression)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "ordinarySymbols" => SourceSynthesisUniverseCallerBoundary.ordinarySymbols

/-- Both original-body and closed-union orders use only strictly smaller original-domain M calls. -/
theorem current_stored_universe_body_union_of_coupled_fuel_induction
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
    (_patternClosed : pattern.free = []) (patternId : Nat)
    (_patternIdentity : identity pattern = some patternId) (fuel : Nat) :
    let universeValue : Value Symbol Guard := .mu entry body depth ordinary
    let entered := SourceRecursiveIntersectionEnvironment.enter domains IntersectionEmptyDomain.emptyKey
      universeValue pattern entry.identity patternId
    let initial : Machine Symbol Guard := ⟨heap, entered.2⟩
    ∀ later : Machine Symbol Guard, SourceRecursiveIntersectionKernel.Valid later → Extension initial later →
    ∀ (unionEntry : Interned NodeKey) (members : List (Value Symbol Guard))
      (unionDepth : Nat) (unionFree : List Reference),
      let operand : Value Symbol Guard := .union unionEntry members unionDepth unionFree
      Available later.heap operand → operand.free = [] →
      (∀ atom ∈ atoms operand, atom = .mu entry.identity) → height operand ≤ height pattern →
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
  intro later laterValid continuation unionEntry members unionDepth unionFree
  intro operandAvailable operandClosed operandAtoms bounded mixedInduction bodyFirst
  cases fuel with
  | zero => exact checked_failed later laterValid .exhausted _
  | succ childFuel =>
      let operand : Value Symbol Guard := .union unionEntry members unionDepth unionFree
      have laterGrowth : Grows sourceHeap later.heap := grows_trans growth continuation.heap
      obtain ⟨bodyEntry, _marker, arrow, rows, bodyEq, bodyAvailable, _rest⟩ :=
        SourceSynthesisCurrentUniverseBodyChildClassification.current_stored_universe_body_physical_children_after_growth
          lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
          later.heap laterValid.1 laterGrowth
      let bodyRows := canonicalEdges (arrow :: rows)
      have actualBody : Available later.heap (.node bodyEntry bodyRows 0 [.interned entry.identity]) :=
        bodyEq ▸ bodyAvailable
      have ownerAvailable : Available later.heap universeValue :=
        laterValid.1.cached.nodes key _ (laterGrowth.nodeRecords key _ stored)
      have bodyApart : bodyEntry.identity ≠ entry.identity :=
        physical_identity_apart_owner later.heap laterValid.1 entry body depth ordinary ownerAvailable
          (.node bodyEntry bodyRows 0 [.interned entry.identity]) actualBody bodyEntry.identity rfl
          (by intro impossible; cases impossible)
      have unionApart : unionEntry.identity ≠ entry.identity :=
        physical_identity_apart_owner later.heap laterValid.1 entry body depth ordinary ownerAvailable
          operand operandAvailable unionEntry.identity rfl
          (by
            intro impossible
            change (Value.union unionEntry members unionDepth unionFree : Value Symbol Guard) =
              Value.mu entry body depth ordinary at impossible
            cases impossible)
      have originalKey := SourceRecursiveIntersectionSchedule.entered_key domains cacheValid
        IntersectionEmptyDomain.emptyKey universeValue pattern entry.identity patternId
      have apart := pair_apart_owner bodyEntry.identity unionEntry.identity entry.identity patternId bodyApart unionApart
      have fresh : pair bodyEntry.identity unionEntry.identity ∉ entered.1.key.seen := by
        intro seen
        rw [originalKey] at seen
        rcases (extend_seen IntersectionEmptyDomain.emptyKey
          ((SourceRecursiveIntersectionEnvironment.bindings universeValue pattern).map Prod.fst)
          (pair entry.identity patternId) (pair bodyEntry.identity unionEntry.identity)).mp seen with same | old
        · exact apart same
        · simp only [IntersectionEmptyDomain.emptyKey, List.not_mem_nil] at old
      have physicalControl := body_union_branches entered.1 entry.identity bodyEntry bodyRows
        unionEntry members unionDepth unionFree fresh
      have forwardTransport := congrArg
        (fun candidate : Value Symbol Guard => decision entered.1.key candidate operand) bodyEq
      have reverseTransport := congrArg
        (fun candidate : Value Symbol Guard => decision entered.1.key operand candidate) bodyEq
      have forwardSelected : decision entered.1.key body operand = .rightUnion :=
        forwardTransport.trans physicalControl.1
      have reverseSelected : decision entered.1.key operand body = .swap :=
        reverseTransport.trans physicalControl.2
      have bodyNotReference : body ≠ .reference (.interned entry.identity) := by
        intro impossible
        rw [bodyEq] at impossible
        cases impossible
      have childBelow : childFuel < Nat.succ childFuel := Nat.lt_succ_self childFuel
      cases bodyFirst with
      | false =>
          change Checked later (execute top SourceEqualityPCSNativeEdge.conjoin (childFuel + 1) entered.1 operand body later)
            (fun after value => Available after.heap value ∧ value.free = [] ∧
              ∀ atom ∈ atoms value, atom = .mu entry.identity)
          have reversed := mixedInduction childFuel childBelow later laterValid (Extension.refl later)
            body (Or.inl rfl) operand operandAvailable operandClosed operandAtoms bounded
            (fun impossible => False.elim (bodyNotReference impossible)) true
          have swapped : execute top SourceEqualityPCSNativeEdge.conjoin (childFuel + 1) entered.1 operand body later =
              execute top SourceEqualityPCSNativeEdge.conjoin childFuel entered.1 body operand later := by
            simp only [execute, onNode, reverseSelected]
          exact swapped.symm ▸ reversed
      | true =>
          change Checked later (execute top SourceEqualityPCSNativeEdge.conjoin (childFuel + 1) entered.1 body operand later)
            (fun after value => Available after.heap value ∧ value.free = [] ∧
              ∀ atom ∈ atoms value, atom = .mu entry.identity)
          have initialOwner : Available heap universeValue :=
            facts.cached.nodes key _ (growth.nodeRecords key _ stored)
          have allocation := SourceRecursiveIntersectionKernel.entered
            (⟨heap, domains⟩ : Machine Symbol Guard) ⟨facts, cacheValid⟩
            IntersectionEmptyDomain.emptyDomain (empty_domain _) universeValue pattern
            initialOwner patternAvailable entry.identity patternId
          have known : Domain later entered.1 := allocation.2.2.grows entered.1 continuation
          have memberAvailable : ∀ member ∈ members, Available later.heap member := by
            intro member present
            exact (SourceSynthesisCurrentUniverseAtomInductionSteps.union_member_closed_atoms
              later.heap laterValid.1 entry.identity unionEntry members unionDepth unionFree
              operandAvailable operandClosed operandAtoms member present).1
          have payload := SourceSynthesisCurrentUniverseAtomInductionSteps.ordered_union_atoms_of_fuel_induction
            top SourceEqualityPCSNativeEdge.conjoin childFuel entered.1 members body false
            later laterValid known bodyAvailable memberAvailable entry.identity
            (by
              intro member present current currentValid extension value after returned
              have memberFacts := SourceSynthesisCurrentUniverseAtomInductionSteps.union_member_closed_atoms
                later.heap laterValid.1 entry.identity unionEntry members unionDepth unionFree
                operandAvailable operandClosed operandAtoms member present
              have memberBound := Nat.le_trans
                (Nat.le_of_lt (SourceSynthesisUniversePrefixHeight.member_lt unionEntry members unionDepth unionFree member present))
                bounded
              have checked := mixedInduction childFuel childBelow current currentValid extension
                body (Or.inl rfl) member (extension.available member memberFacts.1)
                memberFacts.2.1 memberFacts.2.2 memberBound
                (fun impossible => False.elim (bodyNotReference impossible)) true
              exact (checked.result value after returned).2.2)
          change Checked later
            ((walk (fun member current => execute top SourceEqualityPCSNativeEdge.conjoin childFuel entered.1 body member current)
              members later).bind (fun values after => work (makeUnion values) after))
            (fun after value => Available after.heap value ∧ ∀ atom ∈ atoms value, atom = .mu entry.identity) at payload
          have actual : execute top SourceEqualityPCSNativeEdge.conjoin (childFuel + 1) entered.1 body operand later =
              (walk (fun member current => execute top SourceEqualityPCSNativeEdge.conjoin childFuel entered.1 body member current)
                members later).bind (fun values after => work (makeUnion values) after) := by
            simp only [execute, onNode, forwardSelected, operand]
          have native : Checked later
              (execute top SourceEqualityPCSNativeEdge.conjoin (childFuel + 1) entered.1 body operand later)
              (fun after value => Available after.heap value ∧ ∀ atom ∈ atoms value, atom = .mu entry.identity) :=
            actual.symm ▸ payload
          refine ⟨native.valid, native.extension, ?_⟩
          intro value after returned
          have supplied := native.result value after returned
          have endpoint :
              (execute top SourceEqualityPCSNativeEdge.conjoin (childFuel + 1) entered.1 body operand later).state = after :=
            congrArg Result.state returned
          have afterValid : SourceRecursiveIntersectionKernel.Valid after := endpoint ▸ native.valid
          have afterExtension : Extension later after := endpoint ▸ native.extension
          have afterGrowth : Grows sourceHeap after.heap := grows_trans laterGrowth afterExtension.heap
          exact ⟨supplied.1,
            SourceSynthesisCurrentUniverseStartupAtoms.current_stored_universe_boundary_atoms_closed_after_growth
              lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
              after.heap afterValid.1 afterGrowth value supplied.1 supplied.2,
            supplied.2⟩

end MicroCFTA.SourceSynthesisCurrentUniverseMixedBodyUnionInductionStep
