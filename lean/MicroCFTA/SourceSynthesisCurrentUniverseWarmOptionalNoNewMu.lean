import MicroCFTA.SourceSynthesisCurrentUniverseWarmMuAdmission
import MicroCFTA.SourceCurrentNativeWarmCMHistory
import MicroCFTA.SourceCurrentNativeWarmAuxiliaryPrefixes

namespace MicroCFTA.SourceSynthesisCurrentUniverseNativeAllocation
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedBinderProtocol (NodeKey Reference)
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceRecursiveIntersectionControl
open SourceEqualityNativeDemand
open SourceCurrentAllocatedNativePhysicalTraceCompletion (Trace)
open SourceCurrentAllocatedNativePhysicalExecution (InputsThrough)
open SourceEqualityNativeDemandOperations (FieldsThrough)
open SourceCurrentAllocatedNativeGeneralCMHistory (ClosedQualified)
open SourceCurrentAllocatedNativeSourceWarmEntry (AuthenticEntryAt MixedQualifiedAt)
open SourceCurrentAllocatedNativeContextCache (Returned)
open SourceSynthesisTypeSyntax (Library Query)
open SourceSynthesisFirstOrderConstruction (Expression)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSynthesisGeneralizeSyntax.Guard
local notation "Node" => Value Symbol Guard
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Profile" => SourceCurrentAllocatedNativeClosedResetProfile.Profile
local notation "ordinarySymbols" => SourceSynthesisUniverseCallerBoundary.ordinarySymbols
set_option autoImplicit false

/- Note [Optional writers on the retained warm state]
The actual warm owner admission classifies the same literal optional site.
The C/M and auxiliary laws use its full actual prefix as one fixed history.
The child reader retains the same request, cell, value and before-finish state.
Each branch preserves the heap of the original optional writer.
The public theorem derives the warm start facts from the actual cold prefix.
-/

private theorem original_entry_from_literal_enter
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
    (rootRequest : NodeRequest Symbol Guard) (start : Checked width) (wholeCount : Nat)
    (entry : Interned NodeKey) (body depth ordinary : Node)
    (pattern : Node) (patternClosed : pattern.free = []) (patternId : Nat)
    (patternIdentity : identity pattern = some patternId)
    (patternKind : tag pattern = 1 ∨ tag pattern = 3) (universeFirst : Bool)
    (used : Nat) (before : Checked width)
    (next : Interned IntersectionFlatMemoKeyDomain.DomainKey → Code Symbol Guard Node)
    (within : used + 1 ≤ wholeCount)
    (actual : Trace used (.code (.node rootRequest .pure))
      start
      (.code (.enter IntersectionEmptyDomain.emptyDomain
        (if universeFirst then .mu entry body depth ordinary else pattern)
        (if universeFirst then pattern else .mu entry body depth ordinary)
        (if universeFirst then entry.identity else patternId)
        (if universeFirst then patternId else entry.identity) next)) before) :
    let entered := SourceRecursiveIntersectionEnvironment.enter before.native.machine.domains
      IntersectionEmptyDomain.emptyKey
      (if universeFirst then .mu entry body depth ordinary else pattern)
      (if universeFirst then pattern else .mu entry body depth ordinary)
      (if universeFirst then entry.identity else patternId)
      (if universeFirst then patternId else entry.identity)
    let after : Checked width :=
      {before with native := advance before.native {before.native.machine with domains := entered.2}}
    Trace 1 (.code (.enter IntersectionEmptyDomain.emptyDomain
        (if universeFirst then .mu entry body depth ordinary else pattern)
        (if universeFirst then pattern else .mu entry body depth ordinary)
        (if universeFirst then entry.identity else patternId)
        (if universeFirst then patternId else entry.identity) next)) before
      (.code (next entered.1)) after →
    AuthenticEntryAt (width := width) rootRequest start wholeCount
      entry body depth ordinary pattern patternId entered.1 := by
  dsimp only
  intro one
  let universeValue : Node := .mu entry body depth ordinary
  let canonical := SourceRecursiveIntersectionEnvironment.enter before.native.machine.domains
    IntersectionEmptyDomain.emptyKey universeValue pattern entry.identity patternId
  have binderPattern : SourceRecursiveIntersectionEnvironment.binder pattern = [] := by
    cases pattern <;> simp_all [tag, SourceRecursiveIntersectionEnvironment.binder]
  have ordered : SourceRecursiveIntersectionEnvironment.enter before.native.machine.domains
      IntersectionEmptyDomain.emptyKey
      (if universeFirst then universeValue else pattern)
      (if universeFirst then pattern else universeValue)
      (if universeFirst then entry.identity else patternId)
      (if universeFirst then patternId else entry.identity) = canonical := by
    cases universeFirst with
    | true => rfl
    | false =>
      change IntersectionEmptyDomain.make before.native.machine.domains
        (SourceRecursiveIntersectionDomain.extend IntersectionEmptyDomain.emptyKey
          ((SourceRecursiveIntersectionEnvironment.binder pattern ++
            SourceRecursiveIntersectionEnvironment.binder universeValue).map Prod.fst)
          (pair patternId entry.identity)) = canonical
      simp only [canonical, SourceRecursiveIntersectionEnvironment.enter,
        SourceRecursiveIntersectionEnvironment.bindings, binderPattern, List.nil_append,
        List.append_nil, pair, Nat.min_comm, Nat.max_comm]
  refine ⟨patternClosed, patternIdentity, patternKind, universeFirst, used, before, next, ?_⟩
  dsimp only
  refine ⟨within, actual, ordered, ?_, congrArg Prod.fst ordered⟩
  simpa only [universeValue, ordered] using one

private theorem pattern_body_same (pattern : Node) (kind : tag pattern = 1 ∨ tag pattern = 3) :
    SourceRecursiveIntersectionKernel.body pattern = pattern := by
  cases pattern <;> simp_all [tag, SourceRecursiveIntersectionKernel.body]

private theorem optional_closed_codec (value : Node) (closed : value.free = []) :
    ∃ input, IntersectionFlatMemoKey.input value.referenceOf = some input := by
  cases value <;> simp_all [Value.free, Value.referenceOf, IntersectionFlatMemoKey.input]

private theorem optional_key_of_codecs {width : Nat} (request : NodeRequest Symbol Guard)
    (left : ∃ input, IntersectionFlatMemoKey.input request.left.referenceOf = some input)
    (right : ∃ input, IntersectionFlatMemoKey.input request.right.referenceOf = some input) :
    ∃ actualKey, SourceRecursiveIntersectionMemo.requestKey width
      request.domain request.left request.right = some actualKey := by
  obtain ⟨first, firstInput⟩ := left
  obtain ⟨second, secondInput⟩ := right
  exact ⟨_, IntersectionFlatMemoKeyDomain.sourceKey_complete width request.domain _ _
    first second firstInput secondInput⟩

private theorem optional_mu_controls
    (domain : IntersectionFlatMemoKeyDomain.DomainKey) (left right : Node)
    (selected : decision domain left right = .bothMu ∨
      decision domain left right = .leftMu ∨ decision domain left right = .rightMu) :
    hasEmpty left right = false ∧ reset domain left right = false ∧
      closedSelf left right = false ∧ greater left right = false ∧
      (payload left right = .bothMu ∨ payload left right = .leftMu ∨ payload left right = .rightMu) := by
  cases emptyTest : hasEmpty left right with
  | true =>
      simp only [decision, emptyTest, ite_true] at selected
      rcases selected with impossible | impossible | impossible <;> cases impossible
  | false =>
      cases resetTest : reset domain left right with
      | true =>
          simp only [decision, emptyTest, resetTest, Bool.false_eq_true, ite_false, ite_true] at selected
          rcases selected with impossible | impossible | impossible <;> cases impossible
      | false =>
          cases selfTest : closedSelf left right with
          | true =>
              simp only [decision, emptyTest, resetTest, selfTest,
                Bool.false_eq_true, ite_false, ite_true] at selected
              rcases selected with impossible | impossible | impossible <;> cases impossible
          | false =>
              cases swapTest : greater left right with
              | true =>
                  simp only [decision, emptyTest, resetTest, selfTest, swapTest,
                    Bool.false_eq_true, ite_false, ite_true] at selected
                  rcases selected with impossible | impossible | impossible <;> cases impossible
              | false =>
                  refine ⟨rfl, rfl, rfl, rfl, ?_⟩
                  simp only [decision, emptyTest, resetTest, selfTest, swapTest,
                    Bool.false_eq_true, ite_false] at selected
                  cases leftId : identity left <;> cases rightId : identity right
                  all_goals simp only [leftId, rightId] at selected
                  all_goals first
                    | rcases selected with impossible | impossible | impossible <;> cases impossible
                    | rename_i first second
                      by_cases seen : pair first second ∈ domain.seen
                      · simp only [seen, ite_true] at selected
                        rcases selected with impossible | impossible | impossible <;> cases impossible
                      · simpa only [seen, ite_false] using selected

private theorem optional_closed_owner
    (heap : InternedConstructorTemplates.State Symbol Guard)
    (entry : Interned NodeKey) (body depth ordinary : Node)
    (request : NodeRequest Symbol Guard)
    (original : ∀ own ownBody ownDepth ownOrdinary,
      Available heap (.mu own ownBody ownDepth ownOrdinary) →
      Profile entry.identity (.mu own ownBody ownDepth ownOrdinary) →
      (Value.mu own ownBody ownDepth ownOrdinary : Node) = .mu entry body depth ordinary)
    (leftAvailable : Available heap request.left) (rightAvailable : Available heap request.right)
    (qualified : ClosedQualified entry.identity request)
    (selected : decision request.domain.key request.left request.right = .bothMu ∨
      decision request.domain.key request.left request.right = .leftMu ∨
      decision request.domain.key request.left request.right = .rightMu) :
    request.domain = IntersectionEmptyDomain.emptyDomain ∧
      ∃ (pattern : Node) (patternId : Nat) (universeFirst : Bool),
        Profile entry.identity pattern ∧ identity pattern = some patternId ∧
        (tag pattern = 1 ∨ tag pattern = 3) ∧
        request.left = (if universeFirst then .mu entry body depth ordinary else pattern) ∧
        request.right = (if universeFirst then pattern else .mu entry body depth ordinary) := by
  rcases request with ⟨domain, left, right⟩
  rcases qualified with ⟨leftProfile, rightProfile, domainKind⟩
  obtain ⟨noEmpty, noReset, noSelf, _swap, recursive⟩ := optional_mu_controls domain.key left right selected
  have emptyDomain : domain = IntersectionEmptyDomain.emptyDomain := by
    rcases domainKind with same | active
    · exact same
    · have wrong : reset domain.key left right = true := by
        simp only [reset, leftProfile.1, rightProfile.1, List.isEmpty_nil,
          active, Bool.not_false, Bool.and_self]
      rw [wrong] at noReset
      cases noReset
  refine ⟨emptyDomain, ?_⟩
  cases left with
  | empty =>
      have wrong : hasEmpty (.empty : Node) right = true := rfl
      rw [wrong] at noEmpty
      cases noEmpty
  | reference name => cases leftProfile.1
  | node own rows level free =>
      cases right with
      | empty | node | union =>
          simp only [payload] at recursive
          rcases recursive with impossible | impossible | impossible <;> cases impossible
      | reference name => cases rightProfile.1
      | mu rightEntry rightBody rightDepth rightOrdinary =>
          have same := original rightEntry rightBody rightDepth rightOrdinary rightAvailable rightProfile
          exact ⟨.node own rows level free, own.identity, false, leftProfile, rfl, Or.inl rfl, rfl, same⟩
  | union own members level free =>
      cases right with
      | empty | node | union =>
          simp only [payload] at recursive
          rcases recursive with impossible | impossible | impossible <;> cases impossible
      | reference name => cases rightProfile.1
      | mu rightEntry rightBody rightDepth rightOrdinary =>
          have same := original rightEntry rightBody rightDepth rightOrdinary rightAvailable rightProfile
          exact ⟨.union own members level free, own.identity, false, leftProfile, rfl, Or.inr rfl, rfl, same⟩
  | mu own ownBody ownDepth ownOrdinary =>
      have same := original own ownBody ownDepth ownOrdinary leftAvailable leftProfile
      cases right with
      | empty =>
          have wrong : hasEmpty (.mu own ownBody ownDepth ownOrdinary) (.empty : Node) = true := rfl
          have controls := optional_mu_controls domain.key _ _ selected
          rw [wrong] at controls
          cases controls.1
      | reference name => cases rightProfile.1
      | node rightEntry rows level free =>
          exact ⟨.node rightEntry rows level free, rightEntry.identity, true, rightProfile, rfl, Or.inl rfl, same, rfl⟩
      | union rightEntry members level free =>
          exact ⟨.union rightEntry members level free, rightEntry.identity, true, rightProfile, rfl, Or.inr rfl, same, rfl⟩
      | mu rightEntry rightBody rightDepth rightOrdinary =>
          have rightSame := original rightEntry rightBody rightDepth rightOrdinary rightAvailable rightProfile
          rw [same, rightSame] at noSelf
          have closed : (Value.mu entry body depth ordinary : Node).free = [] := by
            rw [← same]
            exact leftProfile.1
          simp only [closedSelf, beq_self_eq_true, closed, List.isEmpty_nil, Bool.and_self] at noSelf
          cases noSelf

private theorem optional_mixed_owner
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
    (rootRequest : NodeRequest Symbol Guard) (start : Checked width) (wholeCount : Nat)
    (heap : InternedConstructorTemplates.State Symbol Guard)
    (entry : Interned NodeKey) (body depth ordinary : Node)
    (bodyEntry : Interned NodeKey) (bodyRows : List (EdgeValue Symbol Guard))
    (bodyShape : body = .node bodyEntry bodyRows 0 [.interned entry.identity])
    (request : NodeRequest Symbol Guard)
    (original : ∀ own ownBody ownDepth ownOrdinary,
      Available heap (.mu own ownBody ownDepth ownOrdinary) →
      Profile entry.identity (.mu own ownBody ownDepth ownOrdinary) →
      (Value.mu own ownBody ownDepth ownOrdinary : Node) = .mu entry body depth ordinary)
    (leftAvailable : Available heap request.left) (rightAvailable : Available heap request.right)
    (qualified : MixedQualifiedAt (width := width) rootRequest start wholeCount
      entry body depth ordinary request)
    (selected : decision request.domain.key request.left request.right = .bothMu ∨
      decision request.domain.key request.left request.right = .leftMu ∨
      decision request.domain.key request.left request.right = .rightMu) :
    ∃ (pattern : Node) (patternId : Nat),
      AuthenticEntryAt (width := width) rootRequest start wholeCount
        entry body depth ordinary pattern patternId request.domain ∧
      ((request.left = body ∧ request.right = .mu entry body depth ordinary) ∨
       (request.left = .mu entry body depth ordinary ∧
         request.right = .reference (.interned entry.identity))) := by
  obtain ⟨pattern, patternId, openAlias, operand, authentic, aliasKind, operandProfile,
    _height, _strict, ordered⟩ := qualified
  have operandAvailable : Available heap operand := by
    rcases ordered with ⟨_left, right⟩ | ⟨left, _right⟩
    · rw [← right]; exact rightAvailable
    · rw [← left]; exact leftAvailable
  have controls := optional_mu_controls request.domain.key request.left request.right selected
  have recursive := controls.2.2.2.2
  cases operand with
  | reference name => cases operandProfile.1
  | empty =>
      rcases aliasKind with rfl | rfl
      all_goals rcases ordered with ⟨left, right⟩ | ⟨left, right⟩
      all_goals rw [left, right] at recursive
      all_goals try rw [bodyShape] at recursive
      all_goals simp only [payload] at recursive
      all_goals rcases recursive with impossible | impossible | impossible <;> cases impossible
  | node own rows level free =>
      rcases aliasKind with rfl | rfl
      all_goals rcases ordered with ⟨left, right⟩ | ⟨left, right⟩
      all_goals rw [left, right] at recursive
      all_goals try rw [bodyShape] at recursive
      all_goals simp only [payload] at recursive
      all_goals rcases recursive with impossible | impossible | impossible <;> cases impossible
  | union own members level free =>
      rcases aliasKind with rfl | rfl
      all_goals rcases ordered with ⟨left, right⟩ | ⟨left, right⟩
      all_goals rw [left, right] at recursive
      all_goals try rw [bodyShape] at recursive
      all_goals simp only [payload] at recursive
      all_goals rcases recursive with impossible | impossible | impossible <;> cases impossible
  | mu own ownBody ownDepth ownOrdinary =>
      have same := original own ownBody ownDepth ownOrdinary operandAvailable operandProfile
      rcases aliasKind with rfl | rfl
      · rcases ordered with ⟨left, right⟩ | ⟨left, right⟩
        · exact ⟨pattern, patternId, authentic, Or.inl ⟨left, right.trans same⟩⟩
        · have wrong : greater request.left request.right = true := by
            rw [left, right, same, bodyShape]
            rfl
          rw [wrong] at controls
          cases controls.2.2.2.1
      · rcases ordered with ⟨left, right⟩ | ⟨left, right⟩
        · have wrong : greater request.left request.right = true := by
            rw [left, right, same]
            rfl
          rw [wrong] at controls
          cases controls.2.2.2.1
        · exact ⟨pattern, patternId, authentic, Or.inr ⟨left.trans same, right⟩⟩

theorem original_universe_next_warm_optional_prefix_no_new_mu
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
    (lib : Library) (query : Query) (signed : Int) (whole : Expression)
    (accepted : SourceSynthesisCurrentConstruction.firstOrderRaw lib query signed = .ok whole)
    (rootValue : Value Symbol Guard) (sourceHeap : InternedConstructorTemplates.State Symbol Guard)
    (built : InternedFreshOrdinaryConstruction.build (ordinarySymbols whole) [] empty =
      .done rootValue sourceHeap)
    (key : NodeKey) (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (stored : sourceHeap.nodeRecords key = some (.mu entry body depth ordinary))
    (oldRoot : NodeRequest Symbol Guard) (machine : Machine Symbol Guard)
    (oldRootDomain : oldRoot.domain = IntersectionEmptyDomain.emptyDomain)
    (oldRootClosed : oldRoot.left.free = [] ∧ oldRoot.right.free = [])
    (machineValid : SourceRecursiveIntersectionKernel.Valid machine)
    (sourceGrowth : Grows sourceHeap machine.heap)
    (pastInventory : InternedShallowHeap.NoNewMu sourceHeap machine.heap)
    (operations : SourceEqualityConstraintMemoAllocation.State)
    (operationsValid : SourceEqualityConstraintMemoAllocation.Valid operations)
    (oldFuel oldCount : Nat) (oldControl : Control (Value Symbol Guard))
    (oldSnapshot : Checked width) (oldBound : oldCount ≤ oldFuel)
    (oldInputs : InputsThrough oldFuel (.code (.node oldRoot .pure))
      (⟨initial width machine, operations⟩ : Checked width))
    (oldFields : FieldsThrough oldFuel (.code (.node oldRoot .pure))
      (⟨initial width machine, operations⟩ : Checked width))
    (oldActual : Trace oldCount (.code (.node oldRoot .pure))
      (⟨initial width machine, operations⟩ : Checked width) oldControl oldSnapshot)
    (newRoot : NodeRequest Symbol Guard) (newFuel : Nat)
    (newRootDomain : newRoot.domain = IntersectionEmptyDomain.emptyDomain)
    (newLeftAvailable : Available oldSnapshot.native.machine.heap newRoot.left)
    (newRightAvailable : Available oldSnapshot.native.machine.heap newRoot.right)
    (newLeftClosed : newRoot.left.free = []) (newRightClosed : newRoot.right.free = [])
    (newInputs : InputsThrough newFuel (.code (.node newRoot .pure)) oldSnapshot)
    (newFields : FieldsThrough newFuel (.code (.node newRoot .pure)) oldSnapshot)
    (used : Nat) (current : Checked width)
    (binder : Nat × Nat) (child : Value Symbol Guard)
    (next : Value Symbol Guard → Code Symbol Guard (Value Symbol Guard))
    (bounded : used + 1 ≤ newFuel)
    (actual : Trace used (.code (.node newRoot .pure)) oldSnapshot
      (.code (.optionalBinder binder child next)) current) :
    InternedShallowHeap.NoNewMu current.native.machine.heap
      (SourceRecursiveIntersectionMaybeMu.maybeMu binder child current.native.machine.heap).state
 := by
  let initialState : Checked width := oldSnapshot
  let readerControl : Control (Value Symbol Guard) := .code (.optionalBinder binder child next)
  let coldInitial : Checked width := ⟨initial width machine, operations⟩
  have coldPhysical := SourceCurrentAllocatedNativePhysicalCache.initial_valid (width := width) machine machineValid
  have oldOperations := SourceCurrentAllocatedNativePrefixOperations.prefix_operations_before_bind
    oldFuel oldCount (.code (.node oldRoot .pure)) oldControl .pure coldInitial oldSnapshot sourceHeap
    coldPhysical oldInputs oldFields operationsValid sourceGrowth
    (by simpa only [Control.bind_pure] using oldActual.steps) oldBound
  have initialPhysical := oldOperations.2.1
  have warmGrowth := oldOperations.2.2.2.1
  obtain ⟨queryUsed, childCount, queried, callerNext, queryBefore, handle, chosen, running,
      first, second, ownerData⟩ :=
    SourceCurrentNativeConsistentOptionalOwner.request newRoot used initialState current
      binder child next initialPhysical actual
  dsimp only at ownerData
  obtain ⟨total, queryActual, queryInputs, _selected, _demanded, _suspended, _evaluating,
      _machineSame, queryStep, selectedMu, leftIdentity, rightIdentity, pairSame,
      enterInputs, enterStep, childActual, _nextSame, _ownerRetained⟩ := ownerData
  let compilerBefore : Checked width := ⟨running, queryBefore.operations⟩
  let entered := SourceRecursiveIntersectionEnvironment.enter compilerBefore.native.machine.domains
    queried.domain.key queried.left queried.right first second
  let childBefore : Checked width :=
    {compilerBefore with
      native := advance compilerBefore.native ({compilerBefore.native.machine with domains := entered.2})}
  let childRequest : NodeRequest Symbol Guard :=
    ⟨entered.1, SourceRecursiveIntersectionKernel.body queried.left,
      SourceRecursiveIntersectionKernel.body queried.right⟩
  let finishNext : Node → Code Symbol Guard Node := fun value => .finishNode handle value (callerNext value)
  let optionalNext : Node → Code Symbol Guard Node := fun value =>
    (Code.optionalBinder (pair first second) value (.pure : Node → Code Symbol Guard Node)).bind finishNext
  have queryPhysical := SourceCurrentNativeEnterCommonOperand.checked_trace_extension queryActual initialPhysical
  have queryGrowth := grows_trans warmGrowth queryPhysical.2.heap
  have readerPhysical := SourceCurrentNativeEnterCommonOperand.checked_trace_extension actual initialPhysical
  have readerGrowth := grows_trans warmGrowth readerPhysical.2.heap
  have compiled : compileNode queried = compileMu queried.domain queried.left queried.right := by
    rcases selectedMu with selected | selected | selected <;> simp only [compileNode, selected]
  have dispatch : Trace 1 (.code (.node queried callerNext)) queryBefore
      (.code ((compileMu queried.domain queried.left queried.right).bind finishNext)) compilerBefore := by
    refine .cons _ _ _ _ _ _ 0 queryInputs ?_ (.refl _ _)
    simpa only [compiled, finishNext] using queryStep
  have compilerOrigin := queryActual.trans dispatch
  have enteredOnce : Trace 1 (.code (compileMu queried.domain queried.left queried.right)) compilerBefore
      (.code ((requestNode childRequest.domain childRequest.left childRequest.right).bind
        (fun value => .optionalBinder (pair first second) value .pure))) childBefore :=
    .cons _ _ _ _ _ _ 0 enterInputs enterStep (.refl _ _)
  have childOrigin : Trace (queryUsed + 2) (.code (.node newRoot .pure)) initialState
      (.code ((requestNode childRequest.domain childRequest.left childRequest.right).bind optionalNext)) childBefore := by
    have combined := compilerOrigin.trans (enteredOnce.bind finishNext)
    have countSame : queryUsed + 1 + 1 = queryUsed + 2 := by omega
    rw [countSame] at combined
    simpa only [Control.bind, requestNode, Code.bind, optionalNext] using combined
  have compilerPhysical := SourceCurrentNativeEnterCommonOperand.checked_trace_extension compilerOrigin initialPhysical
  have childPhysical := SourceCurrentNativeEnterCommonOperand.checked_trace_extension childOrigin initialPhysical
  have enteredKey : entered.1.key = SourceRecursiveIntersectionDomain.extend queried.domain.key
      ((SourceRecursiveIntersectionEnvironment.bindings queried.left queried.right).map Prod.fst)
      (pair first second) :=
    SourceRecursiveIntersectionSchedule.entered_key compilerBefore.native.machine.domains
      compilerPhysical.1.machine.2 queried.domain.key queried.left queried.right first second
  have childAvailable := SourceCurrentNativeOpenRequestResults.node_result childCount childRequest
    childBefore current child childPhysical.1 childActual
  obtain ⟨bodyEntry, marker, arrow, sourceRows, bodyShape, _bodyAvailable, _markerShape,
      _arrowChildren, _arrowKey, _catalog, _markerClosed, _markerAvailable, _markerAtoms,
      _rowKinds, _arrowRetained⟩ :=
    SourceSynthesisCurrentUniverseBodyChildClassification.current_stored_universe_body_physical_children_after_growth
      lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
      machine.heap machineValid.1 sourceGrowth
  let bodyRows := canonicalEdges (arrow :: sourceRows)
  have bodyRead : body = .node bodyEntry bodyRows 0 [.interned entry.identity] := bodyShape
  have bodyIdentity : identity body = some bodyEntry.identity := by rw [bodyRead]; rfl
  have universeAvailable : Available machine.heap (.mu entry body depth ordinary) :=
    machineValid.1.cached.nodes key _ (sourceGrowth.nodeRecords key _ stored)
  have bodyApart : bodyEntry.identity ≠ entry.identity := by
    apply SourceSynthesisUniverseBodyReferenceControl.body_identity_ne
      entry bodyEntry bodyRows depth ordinary machine machineValid.1
    change Available machine.heap (.mu entry (.node bodyEntry bodyRows 0 [.interned entry.identity]) depth ordinary)
    rw [← bodyRead]
    exact universeAvailable
  have offDiagonal : pair bodyEntry.identity entry.identity ≠ pair entry.identity entry.identity := by
    intro same
    have lower := congrArg Prod.fst same
    have upper := congrArg Prod.snd same
    simp only [pair, Nat.min_self, Nat.max_self] at lower upper
    exact bodyApart (by omega)
  have originalMu (own : Interned NodeKey) (ownBody ownDepth ownOrdinary : Node)
      (available : Available queryBefore.native.machine.heap (.mu own ownBody ownDepth ownOrdinary))
      (profile : Profile entry.identity (.mu own ownBody ownDepth ownOrdinary)) :
      (Value.mu own ownBody ownDepth ownOrdinary : Node) = .mu entry body depth ordinary :=
    SourceSynthesisCurrentUniverseClosedMuClassification.current_stored_universe_closed_mu_eq_after_growth
      lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
      queryBefore.native.machine.heap queryPhysical.1.machine.1 queryGrowth
      own ownBody ownDepth ownOrdinary available profile.1 profile.2
  have bodyCodec : ∃ input, IntersectionFlatMemoKey.input body.referenceOf = some input := by
    rw [bodyRead]
    exact ⟨.node bodyEntry.identity, rfl⟩
  have readChild
      (nodeLaw : NodeRequest Symbol Guard → Node → Prop)
      (edgeLaw : EdgeRequest Symbol Guard → EdgeValue Symbol Guard → Prop)
      (past : Returned nodeLaw current.native.nodes ∧ Returned edgeLaw current.native.edges)
      (keyed : ∃ actualKey, SourceRecursiveIntersectionMemo.requestKey width
        childRequest.domain childRequest.left childRequest.right = some actualKey) :
      nodeLaw childRequest child := by
    obtain ⟨actualKey, keyed⟩ := keyed
    exact (SourceCurrentAllocatedNativeSamePrefixKeyedChildResult.keyed_child_law_at_actual_warm_reader
      nodeLaw edgeLaw newRoot oldSnapshot initialPhysical newFuel used (queryUsed + 2) childCount
      readerControl current (by omega) actual past childRequest actualKey keyed optionalNext childBefore
      current child (by omega) childOrigin.steps childActual.steps).1
  have warmAuxiliary := SourceCurrentNativeWarmAuxiliaryPrefixes.auxiliary_payloads_at_every_actual_warm_prefix
    lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
    bodyEntry.identity bodyIdentity oldRoot machine oldRootDomain oldRootClosed machineValid sourceGrowth
    operations operationsValid oldFuel oldCount oldControl oldSnapshot oldBound oldInputs oldFields oldActual
    newRoot newFuel used readerControl current (by omega) newInputs newFields actual
    used readerControl current (Nat.le_refl _) actual
  have admitted := original_universe_next_warm_mu_query_prefix_admission
    lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
    oldRoot machine oldRootDomain oldRootClosed machineValid sourceGrowth pastInventory
    operations operationsValid oldFuel oldCount oldControl oldSnapshot oldBound oldInputs oldFields oldActual
    newRoot newFuel newRootDomain newLeftAvailable newRightAvailable newLeftClosed newRightClosed
    newInputs newFields used queryUsed readerControl current queried callerNext queryBefore
    (by omega) actual (by omega) queryActual selectedMu
  rw [pairSame]
  rcases admitted with qualified | auxiliary
  · rcases qualified with closed | mixed
    · obtain ⟨domainSame, pattern, patternId, universeFirst, patternProfile, patternIdentity,
        patternKind, leftSame, rightSame⟩ := optional_closed_owner queryBefore.native.machine.heap
        entry body depth ordinary queried originalMu queryInputs.1.2.1 queryInputs.1.2.2 closed selectedMu
      have patternBody : SourceRecursiveIntersectionKernel.body pattern = pattern :=
        pattern_body_same pattern patternKind
      have firstSame : first = if universeFirst then entry.identity else patternId := by
        rw [leftSame] at leftIdentity
        cases universeFirst with
        | false => exact Option.some.inj (leftIdentity.symm.trans patternIdentity)
        | true => exact Option.some.inj leftIdentity.symm
      have secondSame : second = if universeFirst then patternId else entry.identity := by
        rw [rightSame] at rightIdentity
        cases universeFirst with
        | false => exact Option.some.inj rightIdentity.symm
        | true => exact Option.some.inj (rightIdentity.symm.trans patternIdentity)
      have enteredNext : compileMu queried.domain queried.left queried.right =
          .enter queried.domain queried.left queried.right first second
            (fun domain => (requestNode domain
              (SourceRecursiveIntersectionKernel.body queried.left)
              (SourceRecursiveIntersectionKernel.body queried.right)).bind
              (fun value => .optionalBinder (pair first second) value .pure)) := by
        simp only [compileMu, leftIdentity, rightIdentity, requestNode, Code.bind]
      have entryPrefix : Trace (queryUsed + 1) (.code (.node newRoot .pure)) initialState
          (.code (.enter IntersectionEmptyDomain.emptyDomain
            (if universeFirst then .mu entry body depth ordinary else pattern)
            (if universeFirst then pattern else .mu entry body depth ordinary)
            (if universeFirst then entry.identity else patternId)
            (if universeFirst then patternId else entry.identity)
            (fun domain => ((requestNode domain
              (SourceRecursiveIntersectionKernel.body queried.left)
              (SourceRecursiveIntersectionKernel.body queried.right)).bind
              (fun value => .optionalBinder (pair first second) value .pure)).bind finishNext)))
          compilerBefore := by
        have literalOrigin := compilerOrigin
        rw [enteredNext] at literalOrigin
        simpa only [requestNode, Code.bind, domainSame, leftSame, rightSame, firstSame, secondSame]
          using literalOrigin
      have event : Trace 1
          (.code (.enter IntersectionEmptyDomain.emptyDomain
            (if universeFirst then .mu entry body depth ordinary else pattern)
            (if universeFirst then pattern else .mu entry body depth ordinary)
            (if universeFirst then entry.identity else patternId)
            (if universeFirst then patternId else entry.identity)
            (fun domain => ((requestNode domain
              (SourceRecursiveIntersectionKernel.body queried.left)
              (SourceRecursiveIntersectionKernel.body queried.right)).bind
              (fun value => .optionalBinder (pair first second) value .pure)).bind finishNext)))
          compilerBefore (.code ((requestNode childRequest.domain childRequest.left childRequest.right).bind optionalNext))
          childBefore := by
        have literalEvent := enteredOnce.bind finishNext
        rw [enteredNext] at literalEvent
        simpa only [Control.bind, requestNode, Code.bind, domainSame, leftSame, rightSame,
          firstSame, secondSame, optionalNext] using literalEvent
      have authentic : AuthenticEntryAt (width := width) newRoot oldSnapshot used
          entry body depth ordinary pattern patternId entered.1 := by
        have deriveEntry := original_entry_from_literal_enter newRoot oldSnapshot used
          entry body depth ordinary pattern patternProfile.1 patternId patternIdentity patternKind universeFirst
          (queryUsed + 1) compilerBefore
          (fun domain => ((requestNode domain
            (SourceRecursiveIntersectionKernel.body queried.left)
            (SourceRecursiveIntersectionKernel.body queried.right)).bind
            (fun value => .optionalBinder (pair first second) value .pure)).bind finishNext)
          (by omega) entryPrefix
        have authenticAt := deriveEntry (by
          simpa only [entered, childBefore, childRequest, domainSame, leftSame, rightSame,
            firstSame, secondSame, optionalNext, Control.bind, requestNode, Code.bind,
            IntersectionEmptyDomain.emptyDomain] using event)
        simpa only [entered, domainSame, leftSame, rightSame, firstSame, secondSame,
          IntersectionEmptyDomain.emptyDomain] using authenticAt
      have childLeft : childRequest.left = if universeFirst then body else pattern := by
        change SourceRecursiveIntersectionKernel.body queried.left = _
        rw [leftSame]
        cases universeFirst with
        | false => exact patternBody
        | true => rfl
      have childRight : childRequest.right = if universeFirst then pattern else body := by
        change SourceRecursiveIntersectionKernel.body queried.right = _
        rw [rightSame]
        cases universeFirst with
        | false => rfl
        | true => exact patternBody
      have childQualified : MixedQualifiedAt (width := width) newRoot oldSnapshot used
          entry body depth ordinary childRequest := by
        refine ⟨pattern, patternId, body, pattern, authentic, Or.inl rfl,
          patternProfile, Nat.le_refl _, ?_, ?_⟩
        · intro impossible
          rw [bodyRead] at impossible
          cases impossible
        · cases universeFirst with
          | false => exact Or.inr ⟨childLeft, childRight⟩
          | true => exact Or.inl ⟨childLeft, childRight⟩
      have childKey : ∃ actualKey, SourceRecursiveIntersectionMemo.requestKey width
          childRequest.domain childRequest.left childRequest.right = some actualKey := by
        cases universeFirst with
        | false =>
            exact optional_key_of_codecs childRequest
              (by rw [childLeft]; exact optional_closed_codec pattern patternProfile.1)
              (by rw [childRight]; exact bodyCodec)
        | true =>
            exact optional_key_of_codecs childRequest
              (by rw [childLeft]; exact bodyCodec)
              (by rw [childRight]; exact optional_closed_codec pattern patternProfile.1)
      have cmPast := SourceCurrentNativeWarmCMHistory.current_stored_universe_warm_cm_returned_at_every_actual_prefix
        lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
        oldRoot machine oldRootDomain oldRootClosed machineValid sourceGrowth pastInventory
        operations operationsValid oldFuel oldCount oldControl oldSnapshot oldBound oldInputs oldFields oldActual
        newRoot newFuel used readerControl current (by omega) newInputs newFields actual
      have resultProfile := (readChild _ _ cmPast.1 childKey).2 childQualified
      have unused := SourceRecursiveIntersectionMaybeMu.unused (pair first second) child
        current.native.machine.heap (by rw [resultProfile.1]; exact List.not_mem_nil)
      rw [unused]
      exact InternedShallowHeap.noNewMu_refl _
    · obtain ⟨pattern, patternId, authentic, alternatives⟩ := optional_mixed_owner
        newRoot oldSnapshot used queryBefore.native.machine.heap entry body depth ordinary
        bodyEntry bodyRows bodyRead queried originalMu queryInputs.1.2.1 queryInputs.1.2.2 mixed selectedMu
      rcases alternatives with ⟨leftSame, rightSame⟩ | ⟨leftSame, rightSame⟩
      · have firstSame : first = bodyEntry.identity := by
          rw [leftSame, bodyIdentity] at leftIdentity
          exact Option.some.inj leftIdentity.symm
        have secondSame : second = entry.identity := by
          rw [rightSame] at rightIdentity
          exact Option.some.inj rightIdentity.symm
        have childLeft : childRequest.left = body := by
          simp only [childRequest, leftSame, bodyRead, SourceRecursiveIntersectionKernel.body]
        have childRight : childRequest.right = body := by
          simp only [childRequest, rightSame, SourceRecursiveIntersectionKernel.body]
        have childKeySame : childRequest.domain.key = SourceRecursiveIntersectionDomain.extend queried.domain.key
            [entry.identity] (pair bodyEntry.identity entry.identity) := by
          simpa only [childRequest, leftSame, rightSame, firstSame, secondSame, bodyRead,
            SourceRecursiveIntersectionEnvironment.bindings, SourceRecursiveIntersectionEnvironment.binder,
            List.nil_append, List.map_cons, List.map_nil] using enteredKey
        have payloads := warmAuxiliary pattern patternId queried.domain authentic
        have past := And.intro payloads.1 payloads.2.1
        have childKey := optional_key_of_codecs (width := width) childRequest
          (by rw [childLeft]; exact bodyCodec) (by rw [childRight]; exact bodyCodec)
        have product := (readChild _ _ past childKey).2.2.2 childKeySame childLeft childRight
        have reclosed := SourceCurrentAllocatedNativeCoherentOpenBodyResult.stored_open_product_optional_reclosure
          lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
          current readerPhysical.1.machine.1 readerGrowth bodyEntry.identity entry.identity child childAvailable product
        rw [firstSame, secondSame, reclosed.1]
        exact InternedShallowHeap.noNewMu_refl _
      · have firstSame : first = entry.identity := by
          rw [leftSame] at leftIdentity
          exact Option.some.inj leftIdentity.symm
        have secondSame : second = entry.identity := by
          rw [rightSame] at rightIdentity
          exact Option.some.inj rightIdentity.symm
        have childLeft : childRequest.left = body := by
          simp only [childRequest, leftSame, SourceRecursiveIntersectionKernel.body]
        have childRight : childRequest.right = .reference (.interned entry.identity) := by
          simp only [childRequest, rightSame, SourceRecursiveIntersectionKernel.body]
        have childKeySame : childRequest.domain.key = SourceRecursiveIntersectionDomain.extend queried.domain.key
            [entry.identity] (pair entry.identity entry.identity) := by
          simpa only [childRequest, leftSame, rightSame, firstSame, secondSame,
            SourceRecursiveIntersectionEnvironment.bindings, SourceRecursiveIntersectionEnvironment.binder,
            List.append_nil, List.map_cons, List.map_nil] using enteredKey
        have payloads := warmAuxiliary pattern patternId queried.domain authentic
        have past := And.intro payloads.2.2.1 payloads.2.2.2
        have childKey := optional_key_of_codecs (width := width) childRequest
          (by rw [childLeft]; exact bodyCodec) (by rw [childRight]; exact ⟨.ref entry.identity, rfl⟩)
        have product := (readChild _ _ past childKey).2 childKeySame childLeft childRight
        have reclosed := SourceCurrentAllocatedNativeCoherentOpenBodyResult.stored_open_product_optional_reclosure
          lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
          current readerPhysical.1.machine.1 readerGrowth entry.identity entry.identity child childAvailable product
        rw [firstSame, secondSame, reclosed.1]
        exact InternedShallowHeap.noNewMu_refl _
  · obtain ⟨pattern, patternId, bodyId, originalDomain, bodyIdRead, authentic, alternatives⟩ := auxiliary
    have bodyIdSame : bodyId = bodyEntry.identity := Option.some.inj (bodyIdRead.symm.trans bodyIdentity)
    subst bodyId
    rcases alternatives with ⟨atKey, leftSame, rightSame⟩ | ⟨atKey, leftSame, rightSame⟩
    · have firstSame : first = entry.identity := by
        rw [leftSame] at leftIdentity
        exact Option.some.inj leftIdentity.symm
      have secondSame : second = entry.identity := by
        rw [rightSame] at rightIdentity
        exact Option.some.inj rightIdentity.symm
      have childLeft : childRequest.left = body := by
        simp only [childRequest, leftSame, SourceRecursiveIntersectionKernel.body]
      have childRight : childRequest.right = .reference (.interned entry.identity) := by
        simp only [childRequest, rightSame, SourceRecursiveIntersectionKernel.body]
      have childKeySame : childRequest.domain.key = SourceRecursiveIntersectionDomain.extend
          (SourceRecursiveIntersectionDomain.extend originalDomain.key [entry.identity]
            (pair bodyEntry.identity entry.identity)) [entry.identity] (pair entry.identity entry.identity) := by
        simpa only [childRequest, leftSame, rightSame, firstSame, secondSame, atKey,
          SourceRecursiveIntersectionEnvironment.bindings, SourceRecursiveIntersectionEnvironment.binder,
          List.append_nil, List.map_cons, List.map_nil] using enteredKey
      have repeatedSeen : pair bodyEntry.identity entry.identity ∈ childRequest.domain.key.seen := by
        rw [childKeySame]
        exact (SourceRecursiveIntersectionDomain.extend_seen _ _ _ _).mpr (Or.inr
          ((SourceRecursiveIntersectionDomain.extend_seen _ _ _ _).mpr (Or.inl rfl)))
      have pure : compileNode childRequest = .pure (repeatedValue (pair bodyEntry.identity entry.identity)) := by
        have order : compare (1 : Nat) 4 = .lt := by decide
        have selected : decision childRequest.domain.key childRequest.left childRequest.right =
            .repeated (pair bodyEntry.identity entry.identity) := by
          rw [childLeft, childRight, bodyRead]
          simp [decision, hasEmpty, reset, closedSelf, greater,
            SourceRecursiveIntersectionControl.compareValue, tag, identity, Value.referenceOf,
            Value.free, repeatedSeen, order]
        simp only [compileNode, selected]
      have payloads := warmAuxiliary pattern patternId originalDomain authentic
      have past := And.intro payloads.1 payloads.2.1
      have childKey := optional_key_of_codecs (width := width) childRequest
        (by rw [childLeft]; exact bodyCodec) (by rw [childRight]; exact ⟨.ref entry.identity, rfl⟩)
      have childSame := (readChild _ _ past childKey).1.2 _ pure
      have absent : Reference.intersection (pair entry.identity entry.identity).1
          (pair entry.identity entry.identity).2 ∉ child.free := by
        rw [childSame]
        intro member
        have same := List.mem_singleton.mp member
        have fieldsSame := Reference.intersection.inj same
        exact offDiagonal (Prod.ext fieldsSame.1.symm fieldsSame.2.symm)
      rw [firstSame, secondSame, SourceRecursiveIntersectionMaybeMu.unused _ _ _ absent]
      exact InternedShallowHeap.noNewMu_refl _
    · have firstSame : first = bodyEntry.identity := by
        rw [leftSame, bodyIdentity] at leftIdentity
        exact Option.some.inj leftIdentity.symm
      have secondSame : second = entry.identity := by
        rw [rightSame] at rightIdentity
        exact Option.some.inj rightIdentity.symm
      have childLeft : childRequest.left = body := by
        simp only [childRequest, leftSame, bodyRead, SourceRecursiveIntersectionKernel.body]
      have childRight : childRequest.right = body := by
        simp only [childRequest, rightSame, SourceRecursiveIntersectionKernel.body]
      have childKeySame : childRequest.domain.key = SourceRecursiveIntersectionDomain.extend
          (SourceRecursiveIntersectionDomain.extend originalDomain.key [entry.identity]
            (pair entry.identity entry.identity)) [entry.identity] (pair bodyEntry.identity entry.identity) := by
        simpa only [childRequest, leftSame, rightSame, firstSame, secondSame, atKey, bodyRead,
          SourceRecursiveIntersectionEnvironment.bindings, SourceRecursiveIntersectionEnvironment.binder,
          List.nil_append, List.map_cons, List.map_nil] using enteredKey
      have payloads := warmAuxiliary pattern patternId originalDomain authentic
      have past := And.intro payloads.2.2.1 payloads.2.2.2
      have childKey := optional_key_of_codecs (width := width) childRequest
        (by rw [childLeft]; exact bodyCodec) (by rw [childRight]; exact bodyCodec)
      have product := (readChild _ _ past childKey).1.1.2 childKeySame childLeft childRight
      obtain ⟨productEntry, products, _aligned, _functional, childSame⟩ := product
      have absent : Reference.intersection (pair bodyEntry.identity entry.identity).1
          (pair bodyEntry.identity entry.identity).2 ∉ child.free := by
        rw [childSame]
        intro member
        have same := List.mem_singleton.mp member
        have fieldsSame := Reference.intersection.inj same
        exact offDiagonal (Prod.ext fieldsSame.1 fieldsSame.2)
      rw [firstSame, secondSame, SourceRecursiveIntersectionMaybeMu.unused _ _ _ absent]
      exact InternedShallowHeap.noNewMu_refl _

end MicroCFTA.SourceSynthesisCurrentUniverseNativeAllocation
