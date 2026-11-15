import MicroCFTA.SourceCurrentAllocatedNativeNodeQueryResult
import MicroCFTA.SourceSynthesisCurrentUniverseBodyChildClassification
import MicroCFTA.SourceSynthesisUniverseOffDiagonalReferenceControl

/-!
# Actual native cutoffs below the original stored universe

The source body determines both terminal auxiliary requests.
Literal domain entries insert and retain their actual recursive pairs.
The native query uses its prior returned law or its actual pure body.
The completed bound call retains its original continuation and fuel bound.
-/
namespace MicroCFTA.SourceCurrentAllocatedNativeAuxiliaryCutoffQueries
open Cache InternedConstructorTemplates InternedNestedFacts InternedProbeProvenance
open InternedBinderProtocol (NodeKey Reference)
open SourceRecursiveIntersectionControl SourceRecursiveIntersectionDomain
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceEqualityNativeDemand
open SourceCurrentAllocatedNativeContextCache (Returned)
open SourceSynthesisTypeSyntax (Library Query)
open SourceSynthesisFirstOrderConstruction (Expression)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "ordinarySymbols" => SourceSynthesisUniverseCallerBoundary.ordinarySymbols

set_option autoImplicit false

private theorem auxiliary_repeated_decisions
    (domains : Cache.State IntersectionFlatMemoKeyDomain.DomainKey) (valid : Cache.Valid domains)
    (u b : Interned NodeKey) (rows : List (EdgeValue Symbol Guard))
    (depth ordinary pattern : Value Symbol Guard) (patternId : Nat) :
    let universeValue : Value Symbol Guard := .mu u (.node b rows 0 [.interned u.identity]) depth ordinary
    let bodyValue : Value Symbol Guard := .node b rows 0 [.interned u.identity]
    let referenceValue : Value Symbol Guard := .reference (.interned u.identity)
    let original := SourceRecursiveIntersectionEnvironment.enter domains IntersectionEmptyDomain.emptyKey
      universeValue pattern u.identity patternId
    let bodyFirst := SourceRecursiveIntersectionEnvironment.enter original.2 original.1.key
      bodyValue universeValue b.identity u.identity
    let bodyTerminal := SourceRecursiveIntersectionEnvironment.enter bodyFirst.2 bodyFirst.1.key
      universeValue referenceValue u.identity u.identity
    let diagonalFirst := SourceRecursiveIntersectionEnvironment.enter original.2 original.1.key
      universeValue referenceValue u.identity u.identity
    let diagonalTerminal := SourceRecursiveIntersectionEnvironment.enter diagonalFirst.2 diagonalFirst.1.key
      bodyValue universeValue b.identity u.identity
    decision bodyTerminal.1.key bodyValue referenceValue = .repeated (pair b.identity u.identity) ∧
      decision diagonalTerminal.1.key referenceValue referenceValue = .repeated (pair u.identity u.identity) := by
  let universeValue : Value Symbol Guard := .mu u (.node b rows 0 [.interned u.identity]) depth ordinary
  let bodyValue : Value Symbol Guard := .node b rows 0 [.interned u.identity]
  let referenceValue : Value Symbol Guard := .reference (.interned u.identity)
  let original := SourceRecursiveIntersectionEnvironment.enter domains IntersectionEmptyDomain.emptyKey
    universeValue pattern u.identity patternId
  let bodyFirst := SourceRecursiveIntersectionEnvironment.enter original.2 original.1.key
    bodyValue universeValue b.identity u.identity
  let bodyTerminal := SourceRecursiveIntersectionEnvironment.enter bodyFirst.2 bodyFirst.1.key
    universeValue referenceValue u.identity u.identity
  let diagonalFirst := SourceRecursiveIntersectionEnvironment.enter original.2 original.1.key
    universeValue referenceValue u.identity u.identity
  let diagonalTerminal := SourceRecursiveIntersectionEnvironment.enter diagonalFirst.2 diagonalFirst.1.key
    bodyValue universeValue b.identity u.identity
  have originalValid : Cache.Valid original.2 :=
    (IntersectionEmptyDomain.make_correct domains valid _).1
  have bodyValid : Cache.Valid bodyFirst.2 :=
    (IntersectionEmptyDomain.make_correct original.2 originalValid _).1
  have diagonalValid : Cache.Valid diagonalFirst.2 :=
    (IntersectionEmptyDomain.make_correct original.2 originalValid _).1
  have bodyInserted : pair b.identity u.identity ∈ bodyFirst.1.key.seen := by
    change pair b.identity u.identity ∈
      (SourceRecursiveIntersectionEnvironment.enter original.2 original.1.key
        bodyValue universeValue b.identity u.identity).1.key.seen
    rw [SourceRecursiveIntersectionSchedule.entered_key original.2 originalValid original.1.key
      bodyValue universeValue b.identity u.identity]
    exact SourceRecursiveIntersectionEnvironment.enter_seen _ _ _ _ _
  have bodyRetained : pair b.identity u.identity ∈ bodyTerminal.1.key.seen := by
    change pair b.identity u.identity ∈
      (SourceRecursiveIntersectionEnvironment.enter bodyFirst.2 bodyFirst.1.key
        universeValue referenceValue u.identity u.identity).1.key.seen
    rw [SourceRecursiveIntersectionSchedule.entered_key bodyFirst.2 bodyValid bodyFirst.1.key
      universeValue referenceValue u.identity u.identity]
    exact (extend_seen _ _ _ _).mpr (Or.inr bodyInserted)
  have diagonalInserted : pair u.identity u.identity ∈ diagonalFirst.1.key.seen := by
    change pair u.identity u.identity ∈
      (SourceRecursiveIntersectionEnvironment.enter original.2 original.1.key
        universeValue referenceValue u.identity u.identity).1.key.seen
    rw [SourceRecursiveIntersectionSchedule.entered_key original.2 originalValid original.1.key
      universeValue referenceValue u.identity u.identity]
    exact SourceRecursiveIntersectionEnvironment.enter_seen _ _ _ _ _
  have diagonalRetained : pair u.identity u.identity ∈ diagonalTerminal.1.key.seen := by
    change pair u.identity u.identity ∈
      (SourceRecursiveIntersectionEnvironment.enter diagonalFirst.2 diagonalFirst.1.key
        bodyValue universeValue b.identity u.identity).1.key.seen
    rw [SourceRecursiveIntersectionSchedule.entered_key diagonalFirst.2 diagonalValid diagonalFirst.1.key
      bodyValue universeValue b.identity u.identity]
    exact (extend_seen _ _ _ _).mpr (Or.inr diagonalInserted)
  change decision bodyTerminal.1.key bodyValue referenceValue = _ ∧
    decision diagonalTerminal.1.key referenceValue referenceValue = _
  constructor
  · have tagOrder : compare (1 : Nat) 4 = .lt := by decide
    simp [decision, hasEmpty, reset, closedSelf, greater, compareValue, tag, identity,
      bodyValue, referenceValue, Value.referenceOf, Value.free, bodyRetained, tagOrder]
  · simp [decision, hasEmpty, reset, closedSelf, greater, compareValue, tag, identity,
      referenceValue, Value.referenceOf, Value.free, diagonalRetained,
      SourceRecursiveIntersectionSchedule.reference_interned]

private theorem pure_query_cutoff
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
    (request : NodeRequest Symbol Guard) (expected : Value Symbol Guard)
    (compiled : compileNode request = .pure expected)
    (before after : Checked width) (fuel : Nat) (value : Value Symbol Guard)
    (physical : SourceCurrentAllocatedNativePhysicalCache.Valid before.native)
    (ready : NodeReady before.native.machine request)
    (safe : ∀ key, SourceRecursiveIntersectionMemo.requestKey width request.domain request.left request.right = some key →
      SourceRecursiveIntersectionMemo.KeySafe width request.domain request.left request.right)
    (returned : Returned (fun old result => old = request → result = expected) before.native.nodes)
    (done : execute fuel (.code (requestNode request.domain request.left request.right)) before = .done value after) :
    value = expected := by
  have resultLaw := SourceCurrentAllocatedNativeNodeQueryResult.node_query_result_of_body_induction
    (fun old result => old = request → result = expected)
    request before after fuel value physical ready safe returned done
    (by
      intro bodySteps _ _next first middle result _ body
      intro _
      have pureBody : Steps bodySteps (.code (.pure expected)) first (.code (.pure result)) middle := by
        simpa only [compiled] using body
      exact (pure_trace bodySteps expected result first middle pureBody).2.1.symm)
  exact resultLaw rfl

/-- The two source auxiliary contexts return their exact open cutoff through the actual bound query. -/
theorem current_stored_universe_auxiliary_cutoff_queries
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
    (pattern : Value Symbol Guard) (_patternAvailable : Available heap pattern)
    (_patternClosed : pattern.free = []) (patternId : Nat)
    (_patternIdentity : identity pattern = some patternId)
    (_patternKind : tag pattern = 1 ∨ tag pattern = 3) :
    ∃ (bodyEntry : Interned NodeKey) (bodyRows : List (EdgeValue Symbol Guard)),
      body = .node bodyEntry bodyRows 0 [.interned entry.identity] ∧
      let universeValue : Value Symbol Guard := .mu entry body depth ordinary
      let referenceValue : Value Symbol Guard := .reference (.interned entry.identity)
      let original := SourceRecursiveIntersectionEnvironment.enter domains IntersectionEmptyDomain.emptyKey
        universeValue pattern entry.identity patternId
      let bodyFirst := SourceRecursiveIntersectionEnvironment.enter original.2 original.1.key
        body universeValue bodyEntry.identity entry.identity
      let bodyTerminal := SourceRecursiveIntersectionEnvironment.enter bodyFirst.2 bodyFirst.1.key
        universeValue referenceValue entry.identity entry.identity
      let diagonalFirst := SourceRecursiveIntersectionEnvironment.enter original.2 original.1.key
        universeValue referenceValue entry.identity entry.identity
      let diagonalTerminal := SourceRecursiveIntersectionEnvironment.enter diagonalFirst.2 diagonalFirst.1.key
        body universeValue bodyEntry.identity entry.identity
      ∀ (request : NodeRequest Symbol Guard) (cutoff : Nat × Nat),
        ((request = ⟨bodyTerminal.1, body, referenceValue⟩ ∧ cutoff = pair bodyEntry.identity entry.identity) ∨
          (request = ⟨diagonalTerminal.1, referenceValue, referenceValue⟩ ∧
            cutoff = pair entry.identity entry.identity)) →
        decision request.domain.key request.left request.right = .repeated cutoff ∧
        compileNode request = .pure (repeatedValue cutoff) ∧
        ∀ (Output : Type) (next : Value Symbol Guard → Code Symbol Guard Output)
          (before after : Checked width) (fuel : Nat) (value : Output),
          SourceCurrentAllocatedNativePhysicalCache.Valid before.native →
          NodeReady before.native.machine request →
          (∀ key, SourceRecursiveIntersectionMemo.requestKey width request.domain request.left request.right = some key →
            SourceRecursiveIntersectionMemo.KeySafe width request.domain request.left request.right) →
          Returned (fun old result => old = request → result = repeatedValue cutoff) before.native.nodes →
          execute fuel (.code (.node request next)) before = .done value after →
          ∃ (total inner outer : Nat) (middle : Checked width),
            total < fuel ∧ inner + outer = total ∧
            Steps inner (.code (requestNode request.domain request.left request.right)) before
              (.code (.pure (repeatedValue cutoff))) middle ∧
            Steps outer (.code (next (repeatedValue cutoff))) middle (.code (.pure value)) after := by
  obtain ⟨bodyEntry, _marker, arrow, rows, bodyEq, _bodyFacts⟩ :=
    SourceSynthesisCurrentUniverseBodyChildClassification.current_stored_universe_body_physical_children_after_growth
      lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
      heap facts growth
  refine ⟨bodyEntry, canonicalEdges (arrow :: rows), bodyEq, ?_⟩
  rw [bodyEq]
  have decisions := auxiliary_repeated_decisions domains cacheValid entry bodyEntry
    (canonicalEdges (arrow :: rows)) depth ordinary pattern patternId
  dsimp only at decisions ⊢
  intro request cutoff sourceCase
  have selected : decision request.domain.key request.left request.right = .repeated cutoff := by
    rcases sourceCase with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact decisions.1
    · exact decisions.2
  have compiled : compileNode request = .pure (repeatedValue cutoff) := by
    simp only [compileNode, selected]
  refine ⟨selected, compiled, ?_⟩
  intro Output next before after fuel value physical ready safe returned done
  have boundDone : execute fuel
      ((Control.code (requestNode request.domain request.left request.right)).bind next) before = .done value after := by
    simpa only [requestNode, Control.bind, Code.bind] using done
  obtain ⟨total, bounded, trace⟩ := done_trace fuel _ before after value boundDone
  obtain ⟨inner, outer, result, middle, count, innerTrace, outerTrace⟩ :=
    steps_bind_inverse total (.code (requestNode request.domain request.left request.right)) next
      before after value trace
  have innerDone := trace_done inner (.code (requestNode request.domain request.left request.right))
    before middle result innerTrace
  have exactResult := pure_query_cutoff request (repeatedValue cutoff) compiled
    before middle (inner + 1) result physical ready safe returned innerDone
  subst result
  exact ⟨total, inner, outer, middle, bounded, count, innerTrace, outerTrace⟩

end MicroCFTA.SourceCurrentAllocatedNativeAuxiliaryCutoffQueries

#check MicroCFTA.SourceCurrentAllocatedNativeAuxiliaryCutoffQueries.current_stored_universe_auxiliary_cutoff_queries
#print axioms MicroCFTA.SourceCurrentAllocatedNativeAuxiliaryCutoffQueries.current_stored_universe_auxiliary_cutoff_queries
