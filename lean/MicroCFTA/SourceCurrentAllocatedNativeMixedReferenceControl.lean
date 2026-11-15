import MicroCFTA.SourceSynthesisUniverseMixedDescendantFreshness
import MicroCFTA.SourceEqualityNativeDemandOpenMeaning

/-!
# Checked-code reference control below the original mixed entry

The strict operand bound excludes the repeated pair in both orders.
An ordinary operand selects the real source binding read.
The reversed body retains the sorted request and its native memo traffic.
-/
namespace MicroCFTA.SourceCurrentAllocatedNativeMixedReferenceControl
open Cache InternedConstructorTemplates InternedNestedFacts InternedProbeProvenance
open InternedBinderProtocol (NodeKey Reference)
open SourceRecursiveIntersectionControl SourceRecursiveIntersectionDomain
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceSynthesisUniversePrefixHeight (height)
open SourceSynthesisTypeSyntax (Library Query)
open SourceSynthesisGeneralizeSyntax (Guard)
open SourceSynthesisFirstOrderConstruction (Expression)

set_option autoImplicit false
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "ordinarySymbols" => SourceSynthesisUniverseCallerBoundary.ordinarySymbols

/-- Fresh actual operand identities exclude the repeated branch in both orders. -/
theorem fresh_reference_decisions
    (domain : Interned IntersectionFlatMemoKeyDomain.DomainKey) (name : Nat)
    (operand : Value Symbol Guard)
    (fresh : ∀ operandId, identity operand = some operandId →
      pair name operandId ∉ domain.key.seen ∧ pair operandId name ∉ domain.key.seen) :
    (∀ cutoff, decision domain.key (.reference (.interned name)) operand ≠ .repeated cutoff) ∧
      (∀ cutoff, decision domain.key operand (.reference (.interned name)) ≠ .repeated cutoff) := by
  constructor
  · intro cutoff selected
    obtain ⟨first, second, leftIdentity, rightIdentity, keyEq⟩ :=
      SourceEqualityNativeDemandOpenMeaning.repeated_identities domain.key _ _ cutoff selected
    have same : first = name := (Option.some.inj leftIdentity).symm
    subst first
    have member := SourceRecursiveIntersectionResultScope.repeated_seen domain.key _ _ cutoff selected
    rw [keyEq] at member
    exact (fresh second rightIdentity).1 member
  · intro cutoff selected
    obtain ⟨first, second, leftIdentity, rightIdentity, keyEq⟩ :=
      SourceEqualityNativeDemandOpenMeaning.repeated_identities domain.key _ _ cutoff selected
    have same : second = name := (Option.some.inj rightIdentity).symm
    subst second
    have member := SourceRecursiveIntersectionResultScope.repeated_seen domain.key _ _ cutoff selected
    rw [keyEq] at member
    exact (fresh first leftIdentity).2 member

/-- A fresh ordinary operand reaches source reference lookup after the actual guards. -/
theorem node_reference_branch
    (domain : Interned IntersectionFlatMemoKeyDomain.DomainKey)
    (entry : Interned NodeKey) (rows : List (EdgeValue Symbol Guard)) (level name : Nat)
    (fresh : pair entry.identity name ∉ domain.key.seen) :
    decision domain.key (.node entry rows level []) (.reference (.interned name)) = .rightReference := by
  have tagOrder : compare (1 : Nat) 4 = .lt := by decide
  simp [decision, hasEmpty, reset, closedSelf, greater, compareValue, tag, identity, payload,
    Value.referenceOf, Value.free, fresh, tagOrder]

/-- The reversed ordinary request retains the actual source swap. -/
theorem reference_node_branch
    (domain : Interned IntersectionFlatMemoKeyDomain.DomainKey)
    (entry : Interned NodeKey) (rows : List (EdgeValue Symbol Guard)) (level name : Nat) :
    decision domain.key (.reference (.interned name)) (.node entry rows level []) = .swap := by
  have tagOrder : compare (4 : Nat) 1 = .gt := by decide
  simp [decision, hasEmpty, reset, closedSelf, greater, compareValue, tag,
    Value.referenceOf, Value.free, tagOrder]

/-- Original mixed-entry descent gives actual checked-code control and ordinary binding read. -/
theorem current_stored_universe_ref_descendant_control
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
    (lib : Library) (query : Query) (signed : Int) (whole : Expression)
    (accepted : SourceSynthesisCurrentConstruction.firstOrderRaw lib query signed = .ok whole)
    (rootValue : Value Symbol Guard) (sourceHeap : InternedConstructorTemplates.State Symbol Guard)
    (built : InternedFreshOrdinaryConstruction.build (ordinarySymbols whole) [] empty =
      .done rootValue sourceHeap)
    (key : NodeKey) (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (stored : sourceHeap.nodeRecords key = some (.mu entry body depth ordinary))
    (heap : InternedConstructorTemplates.State Symbol Guard) (facts : Facts heap) (growth : Grows sourceHeap heap)
    (domains : Cache.State IntersectionFlatMemoKeyDomain.DomainKey) (cacheValid : Cache.Valid domains)
    (pattern : Value Symbol Guard) (patternAvailable : Available heap pattern)
    (patternClosed : pattern.free = []) (patternId : Nat)
    (patternIdentity : identity pattern = some patternId)
    (_patternKind : tag pattern = 1 ∨ tag pattern = 3) :
    let universeValue : Value Symbol Guard := .mu entry body depth ordinary
    let entered := SourceRecursiveIntersectionEnvironment.enter domains IntersectionEmptyDomain.emptyKey
      universeValue pattern entry.identity patternId
    let initial : Machine Symbol Guard := ⟨heap, entered.2⟩
    ∀ before : Checked width, SourceRecursiveIntersectionKernel.Valid before.native.machine →
      Extension initial before.native.machine →
      ∀ operand : Value Symbol Guard, Available before.native.machine.heap operand →
      operand.free = [] → height operand < height pattern →
      (∀ cutoff, decision entered.1.key (.reference (.interned entry.identity)) operand ≠ .repeated cutoff) ∧
      (∀ cutoff, decision entered.1.key operand (.reference (.interned entry.identity)) ≠ .repeated cutoff) ∧
      (∀ (operandEntry : Interned NodeKey) (rows : List (EdgeValue Symbol Guard)) (level : Nat),
        operand = .node operandEntry rows level [] →
        decision entered.1.key operand (.reference (.interned entry.identity)) = .rightReference ∧
        decision entered.1.key (.reference (.interned entry.identity)) operand = .swap ∧
        compileNode ⟨entered.1, operand, .reference (.interned entry.identity)⟩ =
          compileReference entered.1 entry.identity operand false ∧
        compileNode ⟨entered.1, .reference (.interned entry.identity), operand⟩ =
          requestNode entered.1 operand (.reference (.interned entry.identity)) ∧
        SourceEqualityNativeDemand.step
          (.code (compileNode ⟨entered.1, operand, .reference (.interned entry.identity)⟩)) before =
          .yielded (.code (requestNode entered.1 operand universeValue)) before) := by
  let universeValue : Value Symbol Guard := .mu entry body depth ordinary
  let entered := SourceRecursiveIntersectionEnvironment.enter domains IntersectionEmptyDomain.emptyKey
    universeValue pattern entry.identity patternId
  let initial : Machine Symbol Guard := ⟨heap, entered.2⟩
  obtain ⟨_universeClosed, freshness⟩ :=
    SourceSynthesisUniverseMixedDescendantFreshness.current_stored_universe_strict_descendant_fresh_after_mixed_entry
      lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
      heap facts growth domains cacheValid pattern patternAvailable patternClosed patternId patternIdentity
  dsimp only
  intro before beforeValid continuation operand operandAvailable operandClosed smaller
  have allFresh : ∀ operandId, identity operand = some operandId →
      pair entry.identity operandId ∉ entered.1.key.seen ∧
      pair operandId entry.identity ∉ entered.1.key.seen := by
    intro operandId operandIdentity
    obtain ⟨_different, _directApart, _reverseApart, directFresh, reverseFresh, _known, _found⟩ :=
      freshness before.native.machine beforeValid continuation operand operandAvailable operandClosed
        operandId operandIdentity smaller
    exact ⟨directFresh, reverseFresh⟩
  have notRepeated := fresh_reference_decisions entered.1 entry.identity operand allFresh
  refine ⟨notRepeated.1, notRepeated.2, ?_⟩
  intro operandEntry rows level operandEq
  subst operand
  have fresh := (allFresh operandEntry.identity rfl).2
  have selected := node_reference_branch entered.1 operandEntry rows level entry.identity fresh
  have reversed := reference_node_branch entered.1 operandEntry rows level entry.identity
  have compiled : compileNode ⟨entered.1, .node operandEntry rows level [],
      .reference (.interned entry.identity)⟩ =
      compileReference entered.1 entry.identity (.node operandEntry rows level []) false := by
    simp only [compileNode, selected]
  have found := (freshness before.native.machine beforeValid continuation
    (.node operandEntry rows level []) operandAvailable operandClosed operandEntry.identity rfl smaller).2.2.2.2.2.2
  change lookup before.native.machine.heap entered.1.key entry.identity = some universeValue at found
  have bound : entry.identity ∈ names entered.1.key := by
    by_cases member : entry.identity ∈ names entered.1.key
    · exact member
    · simp only [lookup, member, ite_false, reduceCtorEq] at found
  have read : SourcePreparedSharedRows.read before.native.machine.heap entry.identity = some universeValue := by
    simpa only [lookup, bound, ite_true] using found
  refine ⟨selected, reversed, compiled, ?_, ?_⟩
  · change compileNode ⟨entered.1, .reference (.interned entry.identity),
        .node operandEntry rows level []⟩ =
      requestNode entered.1 (.node operandEntry rows level []) (.reference (.interned entry.identity))
    simp only [compileNode, reversed]
  · change SourceEqualityNativeDemand.step
        (.code (compileNode ⟨entered.1, .node operandEntry rows level [],
          .reference (.interned entry.identity)⟩)) before =
      .yielded (.code (requestNode entered.1 (.node operandEntry rows level []) universeValue)) before
    simp [compiled, compileReference, bound, SourceEqualityNativeDemand.step,
      SourceRecursiveIntersectionNative.step, read, SourceEqualityNativeDemand.lift]

end MicroCFTA.SourceCurrentAllocatedNativeMixedReferenceControl
