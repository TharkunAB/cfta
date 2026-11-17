import MicroCFTA.SourceSynthesisCurrentUniverseColdNoNewMu
import MicroCFTA.SourceCurrentNativeWarmCMDefinitions

/- Note [Admission at an actual warm root]
The carrier follows the existing Code and actual rooted prefixes.
It quantifies every returned payload in each continuation.
The complete warm start replaces cold initialization in all four carriers.
The source wrapper derives its current root Profiles from the old prefix.
No semantic result law or future query invariant is an admission premise.
-/

namespace MicroCFTA.SourceCurrentNativeWarmAdmission
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedBinderProtocol (NodeKey)
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceEqualityNativeDemand
open SourceCurrentAllocatedNativePhysicalTraceCompletion (Trace)
open SourceCurrentAllocatedNativePhysicalExecution (InputsThrough)
open SourceEqualityNativeDemandOperations (FieldsThrough)
open SourceCurrentAllocatedNativeSourceWarmEntry (AuthenticEntryAt)
open SourceCurrentNativeWarmCMDefinitions (Qualified)
open SourceSynthesisTypeSyntax (Library Query)
open SourceSynthesisFirstOrderConstruction (Expression)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSynthesisGeneralizeSyntax.Guard
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Profile" => SourceCurrentAllocatedNativeClosedResetProfile.Profile
local notation "ordinarySymbols" => SourceSynthesisUniverseCallerBoundary.ordinarySymbols
set_option autoImplicit false

/- Note [Actual source call admission]
Query results do not become operands of later compiled queries.
The compiler uses original operands, actual source reads and entered domains.
The carrier checks those calls and their literal continuations only.
Enter and read obligations use actual rooted prefixes within the fixed trace.
The carrier does not assume a result law or an optional body invariant.
-/
private def NodeAdmission
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
    (rootRequest : NodeRequest Symbol Guard) (start : Checked width)
    (wholeCount : Nat)
    (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard) (bodyId : Nat)
    (request : NodeRequest Symbol Guard) : Prop :=
  Qualified (width := width) rootRequest start wholeCount entry body depth ordinary request ∨
    ∃ (fullPattern : Value Symbol Guard) (patternId : Nat)
      (originalDomain : Interned IntersectionFlatMemoKeyDomain.DomainKey),
      AuthenticEntryAt (width := width) rootRequest start wholeCount
        entry body depth ordinary fullPattern patternId originalDomain ∧
      let universeValue : Value Symbol Guard := .mu entry body depth ordinary
      let referenceValue : Value Symbol Guard := .reference (.interned entry.identity)
      let e := SourceRecursiveIntersectionControl.pair bodyId entry.identity
      let d := SourceRecursiveIntersectionControl.pair entry.identity entry.identity
      let bodyFirst := SourceRecursiveIntersectionDomain.extend originalDomain.key [entry.identity] e
      let diagonalFirst := SourceRecursiveIntersectionDomain.extend originalDomain.key [entry.identity] d
      let bodyTerminal := SourceRecursiveIntersectionDomain.extend bodyFirst [entry.identity] d
      let diagonalTerminal := SourceRecursiveIntersectionDomain.extend diagonalFirst [entry.identity] e
      (request.domain.key = bodyFirst ∧
        ((request.left = body ∧ request.right = body) ∨
         (request.left = referenceValue ∧ request.right = referenceValue) ∨
         (request.left = universeValue ∧ request.right = referenceValue))) ∨
      (request.domain.key = bodyTerminal ∧ request.left = body ∧ request.right = referenceValue) ∨
      (request.domain.key = diagonalFirst ∧
        ((request.left = body ∧ request.right = referenceValue) ∨
         (request.left = body ∧ request.right = universeValue))) ∨
      (request.domain.key = diagonalTerminal ∧
        ((request.left = body ∧ request.right = body) ∨
         (request.left = referenceValue ∧ request.right = referenceValue) ∨
         (request.left = universeValue ∧ request.right = referenceValue)))

private def EdgeAdmission
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
    (rootRequest : NodeRequest Symbol Guard) (start : Checked width)
    (wholeCount : Nat)
    (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard) (bodyId : Nat)
    (request : EdgeRequest Symbol Guard) : Prop :=
  request.left.children.length = request.right.children.length →
    ∀ children ∈ request.left.children.zip request.right.children,
      NodeAdmission (width := width) rootRequest start wholeCount
        entry body depth ordinary bodyId ⟨request.domain, children.1, children.2⟩

private def CodeAdmission
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat} {A : Type}
    (rootRequest : NodeRequest Symbol Guard) (start : Checked width)
    (wholeCount : Nat)
    (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard) (bodyId : Nat) :
    Code Symbol Guard A → Prop
  | .pure _ | .fail _ => True
  | .work _ next | .optionalBinder _ _ next =>
      ∀ value, CodeAdmission (width := width) rootRequest start wholeCount entry body depth ordinary bodyId (next value)
  | .node request next =>
      NodeAdmission (width := width) rootRequest start wholeCount entry body depth ordinary bodyId request ∧
      ∀ value, CodeAdmission (width := width) rootRequest start wholeCount entry body depth ordinary bodyId (next value)
  | .edge request next =>
      EdgeAdmission (width := width) rootRequest start wholeCount entry body depth ordinary bodyId request ∧
      ∀ value, CodeAdmission (width := width) rootRequest start wholeCount entry body depth ordinary bodyId (next value)
  | .enter domain left right first second next =>
      ∀ (used : Nat) (before : Checked width)
        (actualNext : Interned IntersectionFlatMemoKeyDomain.DomainKey → Code Symbol Guard (Value Symbol Guard)),
        used + 1 ≤ wholeCount →
        Trace used (.code (.node rootRequest .pure))
          start
          (.code (.enter domain left right first second actualNext)) before →
        let entered := SourceRecursiveIntersectionEnvironment.enter before.native.machine.domains
          domain.key left right first second
        let after : Checked width :=
          {before with native := advance before.native {before.native.machine with domains := entered.2}}
        Trace 1 (.code (.enter domain left right first second actualNext)) before
          (.code (actualNext entered.1)) after →
        CodeAdmission (width := width) rootRequest start wholeCount entry body depth ordinary bodyId (next entered.1)
  | .read name next =>
      ∀ (used : Nat) (before : Checked width)
        (actualNext : Option (Value Symbol Guard) → Code Symbol Guard (Value Symbol Guard)),
        used + 1 ≤ wholeCount →
        Trace used (.code (.node rootRequest .pure))
          start
          (.code (.read name actualNext)) before →
        CodeAdmission (width := width) rootRequest start wholeCount entry body depth ordinary bodyId
          (next (SourcePreparedSharedRows.read before.native.machine.heap name))
  | .finishNode _ _ next | .finishEdge _ _ next =>
      CodeAdmission (width := width) rootRequest start wholeCount entry body depth ordinary bodyId next

private def ControlAdmission
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
    (rootRequest : NodeRequest Symbol Guard) (start : Checked width)
    (wholeCount : Nat)
    (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard) (bodyId : Nat) :
    Control (Value Symbol Guard) → Prop
  | .code code => CodeAdmission (width := width) rootRequest start wholeCount entry body depth ordinary bodyId code
  | .edgeBody request next =>
      EdgeAdmission (width := width) rootRequest start wholeCount entry body depth ordinary bodyId request ∧
      ∀ value, CodeAdmission (width := width) rootRequest start wholeCount entry body depth ordinary bodyId (next value)

section CarrierProofs
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
variable (rootRequest : NodeRequest Symbol Guard) (start : Checked width)
  (wholeCount : Nat)
  (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard) (bodyId : Nat)

private theorem code_admission_bind {A B : Type}
    (code : Code Symbol Guard A) (next : A → Code Symbol Guard B)
    (original : CodeAdmission (width := width) rootRequest start wholeCount
      entry body depth ordinary bodyId code)
    (continuation : ∀ value, CodeAdmission (width := width) rootRequest start wholeCount
      entry body depth ordinary bodyId (next value)) :
    CodeAdmission (width := width) rootRequest start wholeCount
      entry body depth ordinary bodyId (code.bind next) := by
  induction code with
  | pure value => exact continuation value
  | fail failure => trivial
  | work job resume ih | optionalBinder key value resume ih =>
      intro result
      exact ih result (original result)
  | node request resume ih | edge request resume ih =>
      refine ⟨original.1, ?_⟩
      intro result
      exact ih result (original.2 result)
  | enter domain left right first second resume ih =>
      intro used before actualNext within actual
      dsimp only
      intro one
      exact ih _ (original used before actualNext within actual one)
  | read name resume ih =>
      intro used before actualNext within actual
      exact ih _ (original used before actualNext within actual)
  | finishNode handle value rest ih | finishEdge handle value rest ih => exact ih original

private theorem code_admission_walk {A B : Type}
    (call : A → Code Symbol Guard B) (values : List A)
    (calls : ∀ value ∈ values, CodeAdmission (width := width) rootRequest start wholeCount
      entry body depth ordinary bodyId (call value)) :
    CodeAdmission (width := width) rootRequest start wholeCount
      entry body depth ordinary bodyId (walk call values) := by
  induction values with
  | nil => trivial
  | cons first rest ih =>
      apply code_admission_bind rootRequest start wholeCount entry body depth ordinary bodyId
      · exact calls first List.mem_cons_self
      · intro value
        apply code_admission_bind rootRequest start wholeCount entry body depth ordinary bodyId
        · exact ih (fun member included => calls member (List.mem_cons_of_mem first included))
        · intro values
          trivial

private theorem checked_children_admission
    (request : EdgeRequest Symbol Guard)
    (combined : SourceEqualityConjoinAllocation.Constraint FullSyntax.Formula)
    (admitted : EdgeAdmission (width := width) rootRequest start wholeCount
      entry body depth ordinary bodyId request)
    (arity : request.left.children.length = request.right.children.length) :
    CodeAdmission (width := width) rootRequest start wholeCount
      entry body depth ordinary bodyId
      (SourceEqualityNativeCheckedCode.children request.domain request.left request.right combined) := by
  unfold SourceEqualityNativeCheckedCode.children
  apply code_admission_bind rootRequest start wholeCount entry body depth ordinary bodyId
  · apply code_admission_walk rootRequest start wholeCount entry body depth ordinary bodyId
    intro children included
    exact ⟨admitted arity children included, fun _ => trivial⟩
  · intro values row
    trivial

private theorem checked_sentinel_admission (row : EdgeValue Symbol Guard) :
    CodeAdmission (width := width) rootRequest start wholeCount entry body depth ordinary bodyId
      (SourceEqualityNativeCheckedCode.sentinel row) := by
  intro value
  trivial

private theorem checked_body_yield_admission {A : Type}
    (request : EdgeRequest Symbol Guard)
    (next : EdgeValue Symbol Guard → Code Symbol Guard A)
    (before after : Checked width) (control : Control A)
    (admitted : EdgeAdmission (width := width) rootRequest start wholeCount
      entry body depth ordinary bodyId request)
    (continuation : ∀ row, CodeAdmission (width := width) rootRequest start wholeCount
      entry body depth ordinary bodyId (next row))
    (one : SourceEqualityNativeDemand.body request next before = .yielded control after) :
    ∃ code, control = .code code ∧ CodeAdmission (width := width) rootRequest start wholeCount
      entry body depth ordinary bodyId code := by
  unfold SourceEqualityNativeDemand.body at one
  split at one
  · cases one
    refine ⟨_, rfl, ?_⟩
    exact code_admission_bind rootRequest start wholeCount entry body depth ordinary bodyId
      _ next (checked_sentinel_admission rootRequest start wholeCount
        entry body depth ordinary bodyId request.left) continuation
  · rename_i sameArity
    have arity : request.left.children.length = request.right.children.length := Classical.not_not.mp sameArity
    split at one
    · cases one
    · cases one
    · split at one
      · cases one
      · cases one
      · dsimp only at one
        split at one
        · cases one
        · cases one
          refine ⟨_, rfl, ?_⟩
          exact code_admission_bind rootRequest start wholeCount entry body depth ordinary bodyId
            _ next (checked_sentinel_admission rootRequest start wholeCount
              entry body depth ordinary bodyId request.left) continuation
        · cases one
          refine ⟨_, rfl, ?_⟩
          exact code_admission_bind rootRequest start wholeCount entry body depth ordinary bodyId
            _ next (checked_sentinel_admission rootRequest start wholeCount
              entry body depth ordinary bodyId request.left) continuation
        · cases one
          refine ⟨_, rfl, ?_⟩
          exact code_admission_bind rootRequest start wholeCount entry body depth ordinary bodyId
            _ next (checked_children_admission rootRequest start wholeCount
              entry body depth ordinary bodyId request _ admitted arity) continuation
end CarrierProofs

end MicroCFTA.SourceCurrentNativeWarmAdmission

namespace MicroCFTA.SourceCurrentNativeWarmAdmission
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedBinderProtocol (NodeKey)
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceEqualityNativeDemand
open SourceCurrentAllocatedNativePhysicalTraceCompletion (Trace)
open SourceCurrentAllocatedNativePhysicalExecution (InputsThrough)
open SourceEqualityNativeDemandOperations (FieldsThrough)
open SourceCurrentAllocatedNativeSourceWarmEntry (AuthenticEntryAt)
open SourceCurrentNativeWarmCMDefinitions (Qualified)
open SourceSynthesisTypeSyntax (Library Query)
open SourceSynthesisFirstOrderConstruction (Expression)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSynthesisGeneralizeSyntax.Guard
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Profile" => SourceCurrentAllocatedNativeClosedResetProfile.Profile
local notation "ordinarySymbols" => SourceSynthesisUniverseCallerBoundary.ordinarySymbols
open InternedNestedFacts InternedEdgeResidency
open SourceRecursiveIntersectionControl (identity tag pair decision payload)
open SourceCurrentAllocatedNativeGeneralCMHistory (ClosedQualified)
open SourceCurrentAllocatedNativeSourceWarmEntry (MixedQualifiedAt)
open SourceSynthesisUniversePrefixHeight (height)
local notation "Node" => Value Symbol Guard

section SourceCuts
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
variable (rootRequest : NodeRequest Symbol Guard) (start : Checked width)
  (initialPhysical : SourceCurrentAllocatedNativePhysicalCache.Valid start.native)
  (wholeCount : Nat)
  (entry : Interned NodeKey) (body depth ordinary : Node) (bodyId : Nat)

include initialPhysical in
private theorem physical_at_root_prefix
    (sourceHeap : InternedConstructorTemplates.State Symbol Guard)
    (sourceGrowth : Grows sourceHeap start.native.machine.heap)
    (used : Nat) (control : Control Node) (before : Checked width)
    (actual : Trace used (.code (.node rootRequest .pure))
      start control before) :
    SourceCurrentAllocatedNativePhysicalCache.Valid before.native ∧
      Grows sourceHeap before.native.machine.heap := by
  have reached := SourceCurrentNativeEnterCommonOperand.checked_trace_extension actual initialPhysical
  exact ⟨reached.1, grows_trans sourceGrowth reached.2.heap⟩

include initialPhysical in
private theorem original_universe_read_at_prefix
    (sourceHeap : InternedConstructorTemplates.State Symbol Guard)
    (sourceGrowth : Grows sourceHeap start.native.machine.heap) (key : NodeKey)
    (stored : sourceHeap.nodeRecords key = some (.mu entry body depth ordinary))
    (used : Nat) (control : Control Node) (before : Checked width)
    (actual : Trace used (.code (.node rootRequest .pure))
      start control before) :
    SourcePreparedSharedRows.read before.native.machine.heap entry.identity =
      some (.mu entry body depth ordinary) := by
  have reached := physical_at_root_prefix rootRequest start initialPhysical sourceHeap sourceGrowth
    used control before actual
  have available : Available before.native.machine.heap (.mu entry body depth ordinary) :=
    reached.1.machine.1.cached.nodes key _ (reached.2.nodeRecords key _ stored)
  exact SourcePreparedSharedRows.read_identity before.native.machine.heap reached.1.machine.1
    (.mu entry body depth ordinary) available entry.identity rfl

include initialPhysical in
private theorem authentic_domain_key
    (pattern : Node) (patternId : Nat)
    (domain : Interned IntersectionFlatMemoKeyDomain.DomainKey)
    (authentic : AuthenticEntryAt (width := width) rootRequest start wholeCount
      entry body depth ordinary pattern patternId domain) :
    domain.key = SourceRecursiveIntersectionDomain.extend IntersectionEmptyDomain.emptyKey
      [entry.identity] (pair entry.identity patternId) := by
  obtain ⟨_closed, _identity, kind, _side, used, before, _next, data⟩ := authentic
  dsimp only at data
  obtain ⟨_within, actual, _ordered, _one, sameDomain⟩ := data
  have physical := SourceCurrentNativeEnterCommonOperand.checked_trace_extension actual
    (initialPhysical)
  have binderPattern : SourceRecursiveIntersectionEnvironment.binder pattern = [] := by
    cases pattern <;> simp_all [tag, SourceRecursiveIntersectionEnvironment.binder]
  have enteredKey := SourceRecursiveIntersectionSchedule.entered_key before.native.machine.domains
    physical.1.machine.2 IntersectionEmptyDomain.emptyKey (.mu entry body depth ordinary) pattern
    entry.identity patternId
  have bindingNames : (SourceRecursiveIntersectionEnvironment.bindings
      (.mu entry body depth ordinary) pattern).map Prod.fst = [entry.identity] := by
    change ([(entry.identity, Value.mu entry body depth ordinary)] ++
      SourceRecursiveIntersectionEnvironment.binder pattern).map Prod.fst = [entry.identity]
    rw [binderPattern]
    rfl
  rw [sameDomain]
  simpa only [bindingNames] using enteredKey

include initialPhysical in
private theorem authentic_domain_nonempty
    (pattern : Node) (patternId : Nat)
    (domain : Interned IntersectionFlatMemoKeyDomain.DomainKey)
    (authentic : AuthenticEntryAt (width := width) rootRequest start wholeCount
      entry body depth ordinary pattern patternId domain) :
    domain.key.free.isEmpty = false := by
  have keyed := authentic_domain_key rootRequest start initialPhysical wholeCount
    entry body depth ordinary pattern patternId domain authentic
  have named : entry.identity ∈ SourceRecursiveIntersectionDomain.names domain.key := by
    rw [keyed]
    exact (SourceRecursiveIntersectionDomain.extend_names _ _ _ _).mpr (Or.inl List.mem_cons_self)
  cases freeMap : domain.key.free with
  | nil =>
      simp only [SourceRecursiveIntersectionDomain.names, freeMap, List.map_nil, List.not_mem_nil] at named
  | cons first rest => rfl

private theorem original_entry_from_literal_enter
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

omit [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] in
private theorem pattern_body_same (pattern : Node) (kind : tag pattern = 1 ∨ tag pattern = 3) :
    SourceRecursiveIntersectionKernel.body pattern = pattern := by
  cases pattern <;> simp_all [tag, SourceRecursiveIntersectionKernel.body]

private theorem closed_mu_enter_admission
    (bodyEntry : Interned NodeKey) (bodyRows : List (EdgeValue Symbol Guard))
    (bodyShape : body = .node bodyEntry bodyRows 0 [.interned entry.identity])
    (pattern : Node) (profile : Profile entry.identity pattern) (patternId : Nat)
    (patternIdentity : identity pattern = some patternId)
    (patternKind : tag pattern = 1 ∨ tag pattern = 3) (universeFirst : Bool) :
    CodeAdmission (width := width) rootRequest start wholeCount entry body depth ordinary bodyId
      (compileMu IntersectionEmptyDomain.emptyDomain
        (if universeFirst then .mu entry body depth ordinary else pattern)
        (if universeFirst then pattern else .mu entry body depth ordinary)) := by
  have leftIdentity : identity (if universeFirst then .mu entry body depth ordinary else pattern) =
      some (if universeFirst then entry.identity else patternId) := by
    cases universeFirst <;> first | exact patternIdentity | rfl
  have rightIdentity : identity (if universeFirst then pattern else .mu entry body depth ordinary) =
      some (if universeFirst then patternId else entry.identity) := by
    cases universeFirst <;> first | exact patternIdentity | rfl
  simp only [compileMu, leftIdentity, rightIdentity, CodeAdmission]
  intro used before actualNext within actual one
  have authentic := original_entry_from_literal_enter rootRequest start wholeCount
    entry body depth ordinary pattern profile.1 patternId patternIdentity patternKind universeFirst
    used before actualNext within actual one
  refine ⟨Or.inl (Or.inr ?_), ?_⟩
  · refine ⟨pattern, patternId, body, pattern, authentic, Or.inl rfl, profile, Nat.le_refl _, ?_, ?_⟩
    · intro impossible
      rw [bodyShape] at impossible
      cases impossible
    · have bodyPattern := pattern_body_same pattern patternKind
      cases universeFirst with
      | true => exact Or.inl ⟨rfl, bodyPattern⟩
      | false => exact Or.inr ⟨bodyPattern, rfl⟩
  · intro value result
    trivial
end SourceCuts
end MicroCFTA.SourceCurrentNativeWarmAdmission

namespace MicroCFTA.SourceCurrentNativeWarmAdmission
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedBinderProtocol (NodeKey)
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceEqualityNativeDemand
open SourceCurrentAllocatedNativePhysicalTraceCompletion (Trace)
open SourceCurrentAllocatedNativePhysicalExecution (InputsThrough)
open SourceEqualityNativeDemandOperations (FieldsThrough)
open SourceCurrentAllocatedNativeSourceWarmEntry (AuthenticEntryAt)
open SourceCurrentNativeWarmCMDefinitions (Qualified)
open SourceSynthesisTypeSyntax (Library Query)
open SourceSynthesisFirstOrderConstruction (Expression)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSynthesisGeneralizeSyntax.Guard
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Profile" => SourceCurrentAllocatedNativeClosedResetProfile.Profile
local notation "ordinarySymbols" => SourceSynthesisUniverseCallerBoundary.ordinarySymbols
open InternedNestedFacts InternedEdgeResidency
open SourceRecursiveIntersectionControl (identity tag pair decision payload)
open SourceCurrentAllocatedNativeGeneralCMHistory (ClosedQualified)
open SourceCurrentAllocatedNativeSourceWarmEntry (MixedQualifiedAt)
open SourceSynthesisUniversePrefixHeight (height)
local notation "Node" => Value Symbol Guard

section Descents
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
variable (rootRequest : NodeRequest Symbol Guard) (start : Checked width)
  (wholeCount : Nat)
  (entry : Interned NodeKey) (body depth ordinary : Node) (bodyId : Nat)

private theorem code_admission_rows
    (domain : Interned IntersectionFlatMemoKeyDomain.DomainKey)
    (left right : List (EdgeValue Symbol Guard))
    (each : ∀ rows ∈ SourceRecursiveIntersectionKernel.pairs left right,
      EdgeAdmission (width := width) rootRequest start wholeCount
        entry body depth ordinary bodyId ⟨domain, rows.1, rows.2⟩) :
    CodeAdmission (width := width) rootRequest start wholeCount
      entry body depth ordinary bodyId (compileRows domain left right) := by
  unfold compileRows
  apply code_admission_bind rootRequest start wholeCount entry body depth ordinary bodyId
  · apply code_admission_walk rootRequest start wholeCount entry body depth ordinary bodyId
    intro rows included
    exact ⟨each rows included, fun _ => trivial⟩
  · intro values result
    trivial

private theorem closed_rows_admission
    (heap : InternedConstructorTemplates.State Symbol Guard) (facts : Facts heap)
    (domain : Interned IntersectionFlatMemoKeyDomain.DomainKey)
    (domainKind : domain = IntersectionEmptyDomain.emptyDomain ∨ domain.key.free.isEmpty = false)
    (leftEntry rightEntry : Interned NodeKey) (leftRows rightRows : List (EdgeValue Symbol Guard))
    (leftDepth rightDepth : Nat) (leftFree rightFree : List InternedBinderProtocol.Reference)
    (leftAvailable : Available heap (.node leftEntry leftRows leftDepth leftFree))
    (rightAvailable : Available heap (.node rightEntry rightRows rightDepth rightFree))
    (leftProfile : Profile entry.identity (.node leftEntry leftRows leftDepth leftFree))
    (rightProfile : Profile entry.identity (.node rightEntry rightRows rightDepth rightFree)) :
    CodeAdmission (width := width) rootRequest start wholeCount entry body depth ordinary bodyId
      (compileRows domain leftRows rightRows) := by
  apply code_admission_rows rootRequest start wholeCount entry body depth ordinary bodyId
  intro rows included _arity children zipped
  have rowMembers := (SourceRecursiveIntersectionKernel.pairs_member leftRows rightRows rows).mp included
  have childMembers := List.of_mem_zip zipped
  have first := SourceSynthesisCurrentUniverseAtomInductionSteps.node_child_closed_atoms
    heap facts entry.identity leftEntry leftRows leftDepth leftFree leftAvailable
    leftProfile.1 leftProfile.2 rows.1 rowMembers.1 children.1 childMembers.1
  have second := SourceSynthesisCurrentUniverseAtomInductionSteps.node_child_closed_atoms
    heap facts entry.identity rightEntry rightRows rightDepth rightFree rightAvailable
    rightProfile.1 rightProfile.2 rows.2 rowMembers.2.1 children.2 childMembers.2
  exact Or.inl (Or.inl ⟨⟨first.2.1, first.2.2⟩, ⟨second.2.1, second.2.2⟩, domainKind⟩)

private theorem closed_union_admission
    (heap : InternedConstructorTemplates.State Symbol Guard) (facts : Facts heap)
    (domain : Interned IntersectionFlatMemoKeyDomain.DomainKey)
    (domainKind : domain = IntersectionEmptyDomain.emptyDomain ∨ domain.key.free.isEmpty = false)
    (unionEntry : Interned NodeKey) (members : List Node) (level : Nat)
    (free : List InternedBinderProtocol.Reference) (other : Node) (unionFirst : Bool)
    (available : Available heap (.union unionEntry members level free))
    (profile : Profile entry.identity (.union unionEntry members level free))
    (otherProfile : Profile entry.identity other) :
    CodeAdmission (width := width) rootRequest start wholeCount entry body depth ordinary bodyId
      ((walk (fun member => if unionFirst then requestNode domain member other
        else requestNode domain other member) members).bind fun values => .work (makeUnion values) .pure) := by
  apply code_admission_bind rootRequest start wholeCount entry body depth ordinary bodyId
  · apply code_admission_walk rootRequest start wholeCount entry body depth ordinary bodyId
    intro member included
    have inherited := SourceSynthesisCurrentUniverseAtomInductionSteps.union_member_closed_atoms
      heap facts entry.identity unionEntry members level free available profile.1 profile.2 member included
    have memberProfile : Profile entry.identity member := ⟨inherited.2.1, inherited.2.2⟩
    cases unionFirst with
    | false => exact ⟨Or.inl (Or.inl ⟨otherProfile, memberProfile, domainKind⟩), fun _ => trivial⟩
    | true => exact ⟨Or.inl (Or.inl ⟨memberProfile, otherProfile, domainKind⟩), fun _ => trivial⟩
  · intro values result
    trivial

private theorem mixed_union_admission
    (heap : InternedConstructorTemplates.State Symbol Guard) (facts : Facts heap)
    (pattern : Node) (patternId : Nat) (domain : Interned IntersectionFlatMemoKeyDomain.DomainKey)
    (authentic : AuthenticEntryAt (width := width) rootRequest start wholeCount
      entry body depth ordinary pattern patternId domain)
    (alias : Node) (aliasKind : alias = body ∨ alias = .reference (.interned entry.identity))
    (unionEntry : Interned NodeKey) (members : List Node) (level : Nat)
    (free : List InternedBinderProtocol.Reference) (aliasFirst : Bool)
    (available : Available heap (.union unionEntry members level free))
    (profile : Profile entry.identity (.union unionEntry members level free))
    (parentHeight : height (.union unionEntry members level free) ≤ height pattern) :
    CodeAdmission (width := width) rootRequest start wholeCount entry body depth ordinary bodyId
      ((walk (fun member => if aliasFirst then requestNode domain alias member
        else requestNode domain member alias) members).bind fun values => .work (makeUnion values) .pure) := by
  apply code_admission_bind rootRequest start wholeCount entry body depth ordinary bodyId
  · apply code_admission_walk rootRequest start wholeCount entry body depth ordinary bodyId
    intro member included
    have inherited := SourceSynthesisCurrentUniverseAtomInductionSteps.union_member_closed_atoms
      heap facts entry.identity unionEntry members level free available profile.1 profile.2 member included
    have memberProfile : Profile entry.identity member := ⟨inherited.2.1, inherited.2.2⟩
    have smaller := SourceSynthesisUniversePrefixHeight.member_lt unionEntry members level free member included
    have strict : height member < height pattern := Nat.lt_of_lt_of_le smaller parentHeight
    have mixed : MixedQualifiedAt (width := width) rootRequest start wholeCount
        entry body depth ordinary (if aliasFirst then ⟨domain, alias, member⟩ else ⟨domain, member, alias⟩) := by
      cases aliasFirst with
      | false => exact ⟨pattern, patternId, alias, member, authentic, aliasKind, memberProfile,
          Nat.le_of_lt strict, fun _ => strict, Or.inr ⟨rfl, rfl⟩⟩
      | true => exact ⟨pattern, patternId, alias, member, authentic, aliasKind, memberProfile,
          Nat.le_of_lt strict, fun _ => strict, Or.inl ⟨rfl, rfl⟩⟩
    cases aliasFirst <;> exact ⟨Or.inl (Or.inr mixed), fun _ => trivial⟩
  · intro values result
    trivial

private theorem mixed_rows_admission
    (initialPhysical : SourceCurrentAllocatedNativePhysicalCache.Valid start.native)
    (heap : InternedConstructorTemplates.State Symbol Guard) (facts : Facts heap)
    (bodyRows : List (EdgeValue Symbol Guard))
    (sourceChildren : ∀ row ∈ bodyRows, ∀ child ∈ row.children,
      child = .reference (.interned entry.identity) ∨ Profile entry.identity child)
    (pattern : Node) (patternId : Nat) (domain : Interned IntersectionFlatMemoKeyDomain.DomainKey)
    (authentic : AuthenticEntryAt (width := width) rootRequest start wholeCount
      entry body depth ordinary pattern patternId domain)
    (operandEntry : Interned NodeKey) (operandRows : List (EdgeValue Symbol Guard)) (level : Nat)
    (free : List InternedBinderProtocol.Reference) (bodyFirst : Bool)
    (available : Available heap (.node operandEntry operandRows level free))
    (profile : Profile entry.identity (.node operandEntry operandRows level free))
    (parentHeight : height (.node operandEntry operandRows level free) ≤ height pattern) :
    CodeAdmission (width := width) rootRequest start wholeCount entry body depth ordinary bodyId
      (compileRows domain (if bodyFirst then bodyRows else operandRows)
        (if bodyFirst then operandRows else bodyRows)) := by
  have nonempty := authentic_domain_nonempty rootRequest start initialPhysical wholeCount
    entry body depth ordinary pattern patternId domain authentic
  apply code_admission_rows rootRequest start wholeCount entry body depth ordinary bodyId
  intro rows included _arity children zipped
  have rowMembers := (SourceRecursiveIntersectionKernel.pairs_member
    (if bodyFirst then bodyRows else operandRows) (if bodyFirst then operandRows else bodyRows) rows).mp included
  have childMembers := List.of_mem_zip zipped
  cases bodyFirst with
  | true =>
    have inherited := SourceSynthesisCurrentUniverseAtomInductionSteps.node_child_closed_atoms
      heap facts entry.identity operandEntry operandRows level free available profile.1 profile.2
      rows.2 rowMembers.2.1 children.2 childMembers.2
    have childProfile : Profile entry.identity children.2 := ⟨inherited.2.1, inherited.2.2⟩
    rcases sourceChildren rows.1 rowMembers.1 children.1 childMembers.1 with reference | closed
    · have smaller := SourceSynthesisUniversePrefixHeight.child_lt operandEntry operandRows level free
        rows.2 rowMembers.2.1 children.2 childMembers.2
      have strict : height children.2 < height pattern := Nat.lt_of_lt_of_le smaller parentHeight
      exact Or.inl (Or.inr ⟨pattern, patternId, .reference (.interned entry.identity), children.2,
        authentic, Or.inr rfl, childProfile, Nat.le_of_lt strict, fun _ => strict, Or.inl ⟨reference, rfl⟩⟩)
    · exact Or.inl (Or.inl ⟨closed, childProfile, Or.inr nonempty⟩)
  | false =>
    have inherited := SourceSynthesisCurrentUniverseAtomInductionSteps.node_child_closed_atoms
      heap facts entry.identity operandEntry operandRows level free available profile.1 profile.2
      rows.1 rowMembers.1 children.1 childMembers.1
    have childProfile : Profile entry.identity children.1 := ⟨inherited.2.1, inherited.2.2⟩
    rcases sourceChildren rows.2 rowMembers.2.1 children.2 childMembers.2 with reference | closed
    · have smaller := SourceSynthesisUniversePrefixHeight.child_lt operandEntry operandRows level free
        rows.1 rowMembers.1 children.1 childMembers.1
      have strict : height children.1 < height pattern := Nat.lt_of_lt_of_le smaller parentHeight
      exact Or.inl (Or.inr ⟨pattern, patternId, .reference (.interned entry.identity), children.1,
        authentic, Or.inr rfl, childProfile, Nat.le_of_lt strict, fun _ => strict, Or.inr ⟨rfl, reference⟩⟩)
    · exact Or.inl (Or.inl ⟨childProfile, closed, Or.inr nonempty⟩)
end Descents
end MicroCFTA.SourceCurrentNativeWarmAdmission

namespace MicroCFTA.SourceCurrentNativeWarmAdmission
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedBinderProtocol (NodeKey)
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceEqualityNativeDemand
open SourceCurrentAllocatedNativePhysicalTraceCompletion (Trace)
open SourceCurrentAllocatedNativePhysicalExecution (InputsThrough)
open SourceEqualityNativeDemandOperations (FieldsThrough)
open SourceCurrentAllocatedNativeSourceWarmEntry (AuthenticEntryAt)
open SourceCurrentNativeWarmCMDefinitions (Qualified)
open SourceSynthesisTypeSyntax (Library Query)
open SourceSynthesisFirstOrderConstruction (Expression)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSynthesisGeneralizeSyntax.Guard
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Profile" => SourceCurrentAllocatedNativeClosedResetProfile.Profile
local notation "ordinarySymbols" => SourceSynthesisUniverseCallerBoundary.ordinarySymbols
open InternedNestedFacts InternedEdgeResidency
open SourceRecursiveIntersectionControl (identity tag pair decision payload)
open SourceCurrentAllocatedNativeGeneralCMHistory (ClosedQualified)
open SourceCurrentAllocatedNativeSourceWarmEntry (MixedQualifiedAt)
open SourceSynthesisUniversePrefixHeight (height)
local notation "Node" => Value Symbol Guard

section ClosedCompiler
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
variable (rootRequest : NodeRequest Symbol Guard) (start : Checked width)
  (wholeCount : Nat)
  (entry : Interned NodeKey) (body depth ordinary : Node) (bodyId : Nat)

private theorem closed_compile_admission
    (lib : Library) (query : Query) (signed : Int) (whole : Expression)
    (accepted : SourceSynthesisCurrentConstruction.firstOrderRaw lib query signed = .ok whole)
    (rootValue : Node) (sourceHeap : InternedConstructorTemplates.State Symbol Guard)
    (built : InternedFreshOrdinaryConstruction.build (ordinarySymbols whole) [] empty = .done rootValue sourceHeap)
    (key : NodeKey) (stored : sourceHeap.nodeRecords key = some (.mu entry body depth ordinary))
    (bodyEntry : Interned NodeKey) (bodyRows : List (EdgeValue Symbol Guard))
    (bodyShape : body = .node bodyEntry bodyRows 0 [.interned entry.identity])
    (universeProfile : Profile entry.identity (.mu entry body depth ordinary))
    (heap : InternedConstructorTemplates.State Symbol Guard) (facts : Facts heap)
    (growth : Grows sourceHeap heap)
    (request : NodeRequest Symbol Guard)
    (leftAvailable : Available heap request.left) (rightAvailable : Available heap request.right)
    (qualified : ClosedQualified entry.identity request) :
    CodeAdmission (width := width) rootRequest start wholeCount entry body depth ordinary bodyId
      (compileNode request) := by
  rcases request with ⟨domain, left, right⟩
  rcases qualified with ⟨leftProfile, rightProfile, domainKind⟩
  have muOriginal (own : Interned NodeKey) (storedBody storedDepth storedOrdinary : Node)
      (available : Available heap (.mu own storedBody storedDepth storedOrdinary))
      (profile : Profile entry.identity (.mu own storedBody storedDepth storedOrdinary)) :
      (Value.mu own storedBody storedDepth storedOrdinary : Node) = .mu entry body depth ordinary :=
    SourceSynthesisCurrentUniverseClosedMuClassification.current_stored_universe_closed_mu_eq_after_growth
      lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
      heap facts growth own storedBody storedDepth storedOrdinary available profile.1 profile.2
  cases emptyTest : SourceRecursiveIntersectionControl.hasEmpty left right with
  | true =>
    simp only [compileNode, decision, emptyTest, ite_true, CodeAdmission]
  | false =>
    cases resetTest : SourceRecursiveIntersectionControl.reset domain.key left right with
    | true =>
      simp only [compileNode, decision, emptyTest, resetTest, Bool.false_eq_true, ite_false, ite_true,
        requestNode, CodeAdmission]
      exact ⟨Or.inl (Or.inl ⟨leftProfile, rightProfile, Or.inl rfl⟩), fun _ => trivial⟩
    | false =>
      have emptyDomain : domain = IntersectionEmptyDomain.emptyDomain := by
        rcases domainKind with same | active
        · exact same
        · have resetTrue : SourceRecursiveIntersectionControl.reset domain.key left right = true := by
            simp only [SourceRecursiveIntersectionControl.reset, leftProfile.1, rightProfile.1,
              List.isEmpty_nil, active, Bool.not_false, Bool.and_self]
          rw [resetTrue] at resetTest
          cases resetTest
      subst domain
      cases selfTest : SourceRecursiveIntersectionControl.closedSelf left right with
      | true =>
        simp only [compileNode, decision, emptyTest, resetTest, selfTest,
          Bool.false_eq_true, ite_false, ite_true, CodeAdmission]
      | false =>
        cases swapTest : SourceRecursiveIntersectionControl.greater left right with
        | true =>
          simp only [compileNode, decision, emptyTest, resetTest, selfTest, swapTest,
            Bool.false_eq_true, ite_false, ite_true, requestNode, CodeAdmission]
          exact ⟨Or.inl (Or.inl ⟨rightProfile, leftProfile, Or.inl rfl⟩), fun _ => trivial⟩
        | false =>
          have emptySeen : IntersectionEmptyDomain.emptyDomain.key.seen = [] := rfl
          simp only [compileNode, decision, emptyTest, resetTest, selfTest, swapTest,
            Bool.false_eq_true, ite_false]
          cases left with
          | empty => simp only [identity, SourceRecursiveIntersectionCode.unsupported, CodeAdmission]
          | reference name => cases leftProfile.1
          | node leftEntry leftRows leftDepth leftFree =>
            cases right with
            | empty => simp only [identity, SourceRecursiveIntersectionCode.unsupported, CodeAdmission]
            | reference name => cases rightProfile.1
            | node rightEntry rightRows rightDepth rightFree =>
              simp only [identity, emptySeen, List.not_mem_nil, ite_false, payload]
              exact closed_rows_admission rootRequest start wholeCount entry body depth ordinary bodyId
                heap facts IntersectionEmptyDomain.emptyDomain (Or.inl rfl)
                leftEntry rightEntry leftRows rightRows leftDepth rightDepth leftFree rightFree
                leftAvailable rightAvailable leftProfile rightProfile
            | union rightEntry members level free =>
              simp only [identity, emptySeen, List.not_mem_nil, ite_false, payload]
              exact closed_union_admission rootRequest start wholeCount entry body depth ordinary bodyId
                heap facts IntersectionEmptyDomain.emptyDomain (Or.inl rfl) rightEntry members level free
                (.node leftEntry leftRows leftDepth leftFree) false rightAvailable rightProfile leftProfile
            | mu own storedBody storedDepth storedOrdinary =>
              simp only [identity, emptySeen, List.not_mem_nil, ite_false, payload]
              have same := muOriginal own storedBody storedDepth storedOrdinary rightAvailable rightProfile
              rw [same]
              exact closed_mu_enter_admission rootRequest start wholeCount entry body depth ordinary bodyId
                bodyEntry bodyRows bodyShape (.node leftEntry leftRows leftDepth leftFree) leftProfile
                leftEntry.identity rfl (Or.inl rfl) false
          | union leftEntry members level free =>
            cases right with
            | empty => simp only [identity, SourceRecursiveIntersectionCode.unsupported, CodeAdmission]
            | reference name => cases rightProfile.1
            | node rightEntry rightRows rightDepth rightFree =>
              simp only [identity, emptySeen, List.not_mem_nil, ite_false, payload]
              exact closed_union_admission rootRequest start wholeCount entry body depth ordinary bodyId
                heap facts IntersectionEmptyDomain.emptyDomain (Or.inl rfl) leftEntry members level free
                (.node rightEntry rightRows rightDepth rightFree) true leftAvailable leftProfile rightProfile
            | union rightEntry otherMembers otherLevel otherFree =>
              simp only [identity, emptySeen, List.not_mem_nil, ite_false, payload]
              exact closed_union_admission rootRequest start wholeCount entry body depth ordinary bodyId
                heap facts IntersectionEmptyDomain.emptyDomain (Or.inl rfl) leftEntry members level free
                (.union rightEntry otherMembers otherLevel otherFree) true leftAvailable leftProfile rightProfile
            | mu own storedBody storedDepth storedOrdinary =>
              simp only [identity, emptySeen, List.not_mem_nil, ite_false, payload]
              have same := muOriginal own storedBody storedDepth storedOrdinary rightAvailable rightProfile
              rw [same]
              exact closed_mu_enter_admission rootRequest start wholeCount entry body depth ordinary bodyId
                bodyEntry bodyRows bodyShape (.union leftEntry members level free) leftProfile
                leftEntry.identity rfl (Or.inr rfl) false
          | mu own storedBody storedDepth storedOrdinary =>
            have sameLeft := muOriginal own storedBody storedDepth storedOrdinary leftAvailable leftProfile
            cases right with
            | empty => simp only [identity, SourceRecursiveIntersectionCode.unsupported, CodeAdmission]
            | reference name => cases rightProfile.1
            | node rightEntry rightRows rightDepth rightFree =>
              simp only [identity, emptySeen, List.not_mem_nil, ite_false, payload]
              rw [sameLeft]
              exact closed_mu_enter_admission rootRequest start wholeCount entry body depth ordinary bodyId
                bodyEntry bodyRows bodyShape (.node rightEntry rightRows rightDepth rightFree) rightProfile
                rightEntry.identity rfl (Or.inl rfl) true
            | union rightEntry members level free =>
              simp only [identity, emptySeen, List.not_mem_nil, ite_false, payload]
              rw [sameLeft]
              exact closed_mu_enter_admission rootRequest start wholeCount entry body depth ordinary bodyId
                bodyEntry bodyRows bodyShape (.union rightEntry members level free) rightProfile
                rightEntry.identity rfl (Or.inr rfl) true
            | mu rightOwn rightBody rightDepth rightOrdinary =>
              have sameRight := muOriginal rightOwn rightBody rightDepth rightOrdinary rightAvailable rightProfile
              rw [sameLeft, sameRight] at selfTest
              simp only [SourceRecursiveIntersectionControl.closedSelf, Value.referenceOf, beq_self_eq_true,
                universeProfile.1, List.isEmpty_nil, Bool.and_self, Bool.true_eq_false] at selfTest
end ClosedCompiler
end MicroCFTA.SourceCurrentNativeWarmAdmission

namespace MicroCFTA.SourceCurrentNativeWarmAdmission
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedBinderProtocol (NodeKey)
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceEqualityNativeDemand
open SourceCurrentAllocatedNativePhysicalTraceCompletion (Trace)
open SourceCurrentAllocatedNativePhysicalExecution (InputsThrough)
open SourceEqualityNativeDemandOperations (FieldsThrough)
open SourceCurrentAllocatedNativeSourceWarmEntry (AuthenticEntryAt)
open SourceCurrentNativeWarmCMDefinitions (Qualified)
open SourceSynthesisTypeSyntax (Library Query)
open SourceSynthesisFirstOrderConstruction (Expression)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSynthesisGeneralizeSyntax.Guard
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Profile" => SourceCurrentAllocatedNativeClosedResetProfile.Profile
local notation "ordinarySymbols" => SourceSynthesisUniverseCallerBoundary.ordinarySymbols
open InternedNestedFacts InternedEdgeResidency
open SourceRecursiveIntersectionControl (identity tag pair decision payload)
open SourceCurrentAllocatedNativeGeneralCMHistory (ClosedQualified)
open SourceCurrentAllocatedNativeSourceWarmEntry (MixedQualifiedAt)
open SourceSynthesisUniversePrefixHeight (height)
local notation "Node" => Value Symbol Guard

section AuxiliaryEntries
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
variable (rootRequest : NodeRequest Symbol Guard) (start : Checked width)
  (initialPhysical : SourceCurrentAllocatedNativePhysicalCache.Valid start.native)
  (wholeCount : Nat)
  (entry : Interned NodeKey) (body depth ordinary : Node) (bodyId : Nat)

include initialPhysical in
private theorem source_reference_admission
    (sourceHeap : InternedConstructorTemplates.State Symbol Guard)
    (sourceGrowth : Grows sourceHeap start.native.machine.heap) (key : NodeKey)
    (stored : sourceHeap.nodeRecords key = some (.mu entry body depth ordinary))
    (domain : Interned IntersectionFlatMemoKeyDomain.DomainKey) (other : Node) (left : Bool)
    (admitted : NodeAdmission (width := width) rootRequest start wholeCount entry body depth ordinary bodyId
      (if left then ⟨domain, .mu entry body depth ordinary, other⟩
        else ⟨domain, other, .mu entry body depth ordinary⟩)) :
    CodeAdmission (width := width) rootRequest start wholeCount entry body depth ordinary bodyId
      (compileReference domain entry.identity other left) := by
  unfold compileReference
  split
  · intro used before actualNext within actual
    have read := original_universe_read_at_prefix rootRequest start initialPhysical
      entry body depth ordinary sourceHeap sourceGrowth key stored used
      (.code (.read entry.identity actualNext)) before actual
    rw [read]
    cases left <;> exact ⟨admitted, fun _ => trivial⟩
  · trivial

include initialPhysical in
private theorem body_mu_enter_admission
    (bodyEntry : Interned NodeKey) (bodyRows : List (EdgeValue Symbol Guard))
    (bodyShape : body = .node bodyEntry bodyRows 0 [.interned entry.identity])
    (bodyIdentity : identity body = some bodyId)
    (pattern : Node) (patternId : Nat) (originalDomain domain : Interned IntersectionFlatMemoKeyDomain.DomainKey)
    (authentic : AuthenticEntryAt (width := width) rootRequest start wholeCount
      entry body depth ordinary pattern patternId originalDomain)
    (incoming : domain.key = originalDomain.key ∨
      domain.key = SourceRecursiveIntersectionDomain.extend originalDomain.key [entry.identity]
        (pair entry.identity entry.identity)) :
    CodeAdmission (width := width) rootRequest start wholeCount entry body depth ordinary bodyId
      (compileMu domain body (.mu entry body depth ordinary)) := by
  simp only [compileMu]
  rw [bodyIdentity]
  simp only [identity, CodeAdmission]
  intro used before actualNext within actual one
  have physical := SourceCurrentNativeEnterCommonOperand.checked_trace_extension actual
    (initialPhysical)
  have enteredKey := SourceRecursiveIntersectionSchedule.entered_key before.native.machine.domains
    physical.1.machine.2 domain.key body (.mu entry body depth ordinary) bodyId entry.identity
  have binderBody : SourceRecursiveIntersectionEnvironment.binder body = [] := by rw [bodyShape]; rfl
  have bindingNames : (SourceRecursiveIntersectionEnvironment.bindings
      body (.mu entry body depth ordinary)).map Prod.fst = [entry.identity] := by
    change (SourceRecursiveIntersectionEnvironment.binder body ++
      [(entry.identity, Value.mu entry body depth ordinary)]).map Prod.fst = [entry.identity]
    rw [binderBody]
    rfl
  rw [bindingNames] at enteredKey
  have sameBody : SourceRecursiveIntersectionKernel.body body = body := by rw [bodyShape]; rfl
  refine ⟨?_, ?_⟩
  · have admitted : NodeAdmission (width := width) rootRequest start wholeCount
        entry body depth ordinary bodyId
        ⟨(SourceRecursiveIntersectionEnvironment.enter before.native.machine.domains domain.key body
          (.mu entry body depth ordinary) bodyId entry.identity).1, body, body⟩ := by
      right
      refine ⟨pattern, patternId, originalDomain, authentic, ?_⟩
      dsimp only
      rcases incoming with original | diagonal
      · left
        exact ⟨by rw [enteredKey, original], Or.inl ⟨rfl, rfl⟩⟩
      · right; right; right
        exact ⟨by rw [enteredKey, diagonal], Or.inl ⟨rfl, rfl⟩⟩
    have universeBody : SourceRecursiveIntersectionKernel.body (.mu entry body depth ordinary) = body := rfl
    simpa only [sameBody, universeBody] using admitted
  · intro value result
    trivial

include initialPhysical in
private theorem universe_reference_enter_admission
    (pattern : Node) (patternId : Nat) (originalDomain domain : Interned IntersectionFlatMemoKeyDomain.DomainKey)
    (authentic : AuthenticEntryAt (width := width) rootRequest start wholeCount
      entry body depth ordinary pattern patternId originalDomain)
    (incoming : domain.key = originalDomain.key ∨
      domain.key = SourceRecursiveIntersectionDomain.extend originalDomain.key [entry.identity]
        (pair bodyId entry.identity)) :
    CodeAdmission (width := width) rootRequest start wholeCount entry body depth ordinary bodyId
      (compileMu domain (.mu entry body depth ordinary) (.reference (.interned entry.identity))) := by
  simp only [compileMu, identity, CodeAdmission]
  intro used before actualNext within actual one
  have physical := SourceCurrentNativeEnterCommonOperand.checked_trace_extension actual
    (initialPhysical)
  have enteredKey := SourceRecursiveIntersectionSchedule.entered_key before.native.machine.domains
    physical.1.machine.2 domain.key (.mu entry body depth ordinary) (.reference (.interned entry.identity))
    entry.identity entry.identity
  simp only [SourceRecursiveIntersectionEnvironment.bindings,
    SourceRecursiveIntersectionEnvironment.binder, List.append_nil, List.map_cons, List.map_nil] at enteredKey
  refine ⟨Or.inr ⟨pattern, patternId, originalDomain, authentic, ?_⟩, ?_⟩
  · dsimp only
    rcases incoming with original | bodyFirst
    · right; right; left
      exact ⟨by rw [enteredKey, original], Or.inl ⟨rfl, rfl⟩⟩
    · right; left
      exact ⟨by rw [enteredKey, bodyFirst], rfl, rfl⟩
  · intro value result
    trivial

omit [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] in
private theorem zip_self_pair {A : Type} (values : List A) (pair : A × A)
    (included : pair ∈ values.zip values) : pair.1 = pair.2 := by
  induction values with
  | nil => cases included
  | cons first rest ih =>
    simp only [List.zip_cons_cons, List.mem_cons] at included
    rcases included with same | tail
    · cases same
      rfl
    · exact ih tail

omit [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] in
private theorem extended_key_nonempty
    (domain : Interned IntersectionFlatMemoKeyDomain.DomainKey)
    (source : IntersectionFlatMemoKeyDomain.DomainKey) (binder : Nat × Nat)
    (same : domain.key = SourceRecursiveIntersectionDomain.extend source [entry.identity] binder) :
    domain.key.free.isEmpty = false := by
  have named : entry.identity ∈ SourceRecursiveIntersectionDomain.names domain.key := by
    rw [same]
    exact (SourceRecursiveIntersectionDomain.extend_names _ _ _ _).mpr (Or.inl List.mem_cons_self)
  cases freeMap : domain.key.free with
  | nil =>
    simp only [SourceRecursiveIntersectionDomain.names, freeMap, List.map_nil, List.not_mem_nil] at named
  | cons first rest => rfl

private theorem auxiliary_rows_admission
    (rows : List (EdgeValue Symbol Guard))
    (sourceChildren : ∀ row ∈ rows, ∀ child ∈ row.children,
      child = .reference (.interned entry.identity) ∨ Profile entry.identity child)
    (matched : ∀ pair ∈ SourceRecursiveIntersectionKernel.pairs rows rows,
      pair.1 = pair.2 ∨ pair.1.children.length ≠ pair.2.children.length)
    (pattern : Node) (patternId : Nat) (originalDomain domain : Interned IntersectionFlatMemoKeyDomain.DomainKey)
    (authentic : AuthenticEntryAt (width := width) rootRequest start wholeCount
      entry body depth ordinary pattern patternId originalDomain)
    (keyKind : domain.key = SourceRecursiveIntersectionDomain.extend originalDomain.key [entry.identity]
        (pair bodyId entry.identity) ∨
      domain.key = SourceRecursiveIntersectionDomain.extend
        (SourceRecursiveIntersectionDomain.extend originalDomain.key [entry.identity] (pair entry.identity entry.identity))
        [entry.identity] (pair bodyId entry.identity)) :
    CodeAdmission (width := width) rootRequest start wholeCount entry body depth ordinary bodyId
      (compileRows domain rows rows) := by
  have nonempty : domain.key.free.isEmpty = false := by
    rcases keyKind with first | terminal
    · exact extended_key_nonempty entry domain _ _ first
    · exact extended_key_nonempty entry domain _ _ terminal
  apply code_admission_rows rootRequest start wholeCount entry body depth ordinary bodyId
  intro rowPair member arity children included
  rcases matched rowPair member with self | mismatch
  · have rowMembers := (SourceRecursiveIntersectionKernel.pairs_member rows rows rowPair).mp member
    have zipped : children ∈ rowPair.1.children.zip rowPair.1.children := by simpa only [self] using included
    have equal := zip_self_pair rowPair.1.children children zipped
    have inRow := (List.of_mem_zip included).1
    rcases sourceChildren rowPair.1 rowMembers.1 children.1 inRow with reference | closed
    · right
      refine ⟨pattern, patternId, originalDomain, authentic, ?_⟩
      dsimp only
      rcases keyKind with first | terminal
      · left
        exact ⟨first, Or.inr (Or.inl ⟨reference, equal.symm.trans reference⟩)⟩
      · right; right; right
        exact ⟨terminal, Or.inr (Or.inl ⟨reference, equal.symm.trans reference⟩)⟩
    · left; left
      exact ⟨closed, equal ▸ closed, Or.inr nonempty⟩
  · exact (mismatch arity).elim
end AuxiliaryEntries
end MicroCFTA.SourceCurrentNativeWarmAdmission

namespace MicroCFTA.SourceCurrentNativeWarmAdmission
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedBinderProtocol (NodeKey)
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceEqualityNativeDemand
open SourceCurrentAllocatedNativePhysicalTraceCompletion (Trace)
open SourceCurrentAllocatedNativePhysicalExecution (InputsThrough)
open SourceEqualityNativeDemandOperations (FieldsThrough)
open SourceCurrentAllocatedNativeSourceWarmEntry (AuthenticEntryAt)
open SourceCurrentNativeWarmCMDefinitions (Qualified)
open SourceSynthesisTypeSyntax (Library Query)
open SourceSynthesisFirstOrderConstruction (Expression)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSynthesisGeneralizeSyntax.Guard
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Profile" => SourceCurrentAllocatedNativeClosedResetProfile.Profile
local notation "ordinarySymbols" => SourceSynthesisUniverseCallerBoundary.ordinarySymbols
open InternedNestedFacts InternedEdgeResidency
open SourceRecursiveIntersectionControl (identity tag pair decision payload)
open SourceCurrentAllocatedNativeGeneralCMHistory (ClosedQualified)
open SourceCurrentAllocatedNativeSourceWarmEntry (MixedQualifiedAt)
open SourceSynthesisUniversePrefixHeight (height)
local notation "Node" => Value Symbol Guard

section MixedCompiler
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
variable (rootRequest : NodeRequest Symbol Guard) (start : Checked width)
  (initialPhysical : SourceCurrentAllocatedNativePhysicalCache.Valid start.native)
  (wholeCount : Nat)
  (entry : Interned NodeKey) (body depth ordinary : Node) (bodyId : Nat)

include initialPhysical in
private theorem mixed_compile_admission
    (lib : Library) (query : Query) (signed : Int) (whole : Expression)
    (accepted : SourceSynthesisCurrentConstruction.firstOrderRaw lib query signed = .ok whole)
    (rootValue : Node) (sourceHeap : InternedConstructorTemplates.State Symbol Guard)
    (built : InternedFreshOrdinaryConstruction.build (ordinarySymbols whole) [] empty = .done rootValue sourceHeap)
    (key : NodeKey) (stored : sourceHeap.nodeRecords key = some (.mu entry body depth ordinary))
    (initialGrowth : Grows sourceHeap start.native.machine.heap)
    (bodyEntry : Interned NodeKey) (bodyRows : List (EdgeValue Symbol Guard))
    (bodyShape : body = .node bodyEntry bodyRows 0 [.interned entry.identity])
    (bodyIdentity : identity body = some bodyId)
    (sourceChildren : ∀ row ∈ bodyRows, ∀ child ∈ row.children,
      child = .reference (.interned entry.identity) ∨ Profile entry.identity child)
    (universeProfile : Profile entry.identity (.mu entry body depth ordinary))
    (heap : InternedConstructorTemplates.State Symbol Guard) (facts : Facts heap) (growth : Grows sourceHeap heap)
    (request : NodeRequest Symbol Guard)
    (leftAvailable : Available heap request.left) (rightAvailable : Available heap request.right)
    (qualified : MixedQualifiedAt (width := width) rootRequest start wholeCount
      entry body depth ordinary request) :
    CodeAdmission (width := width) rootRequest start wholeCount entry body depth ordinary bodyId
      (compileNode request) := by
  rcases request with ⟨domain, left, right⟩
  dsimp only at leftAvailable rightAvailable
  dsimp only [MixedQualifiedAt] at qualified
  obtain ⟨pattern, patternId, alias, operand, authentic, aliasKind, operandProfile,
    operandHeight, strictAlias, ordered⟩ := qualified
  have nonempty := authentic_domain_nonempty rootRequest start initialPhysical wholeCount
    entry body depth ordinary pattern patternId domain authentic
  have operandAvailable : Available heap operand := by
    rcases ordered with ⟨leftEq, rightEq⟩ | ⟨leftEq, rightEq⟩
    · rw [rightEq] at rightAvailable
      exact rightAvailable
    · rw [leftEq] at leftAvailable
      exact leftAvailable
  have muOriginal (own : Interned NodeKey) (storedBody storedDepth storedOrdinary : Node)
      (available : Available heap (.mu own storedBody storedDepth storedOrdinary))
      (profile : Profile entry.identity (.mu own storedBody storedDepth storedOrdinary)) :
      (Value.mu own storedBody storedDepth storedOrdinary : Node) = .mu entry body depth ordinary :=
    SourceSynthesisCurrentUniverseClosedMuClassification.current_stored_universe_closed_mu_eq_after_growth
      lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
      heap facts growth own storedBody storedDepth storedOrdinary available profile.1 profile.2
  cases emptyTest : SourceRecursiveIntersectionControl.hasEmpty left right with
  | true => simp only [compileNode, decision, emptyTest, ite_true, CodeAdmission]
  | false =>
    have resetFalse : SourceRecursiveIntersectionControl.reset domain.key left right = false := by
      rcases ordered with ⟨leftEq, rightEq⟩ | ⟨leftEq, rightEq⟩
      all_goals
        rw [leftEq, rightEq]
        rcases aliasKind with same | same
        · simp [same, bodyShape, SourceRecursiveIntersectionControl.reset, Value.free]
        · simp [same, SourceRecursiveIntersectionControl.reset, Value.free]
    cases selfTest : SourceRecursiveIntersectionControl.closedSelf left right with
    | true =>
      simp only [compileNode, decision, emptyTest, resetFalse, selfTest,
        Bool.false_eq_true, ite_false, ite_true, CodeAdmission]
    | false =>
      cases swapTest : SourceRecursiveIntersectionControl.greater left right with
      | true =>
        simp only [compileNode, decision, emptyTest, resetFalse, selfTest, swapTest,
          Bool.false_eq_true, ite_false, ite_true, requestNode, CodeAdmission]
        refine ⟨Or.inl (Or.inr ⟨pattern, patternId, alias, operand, authentic, aliasKind,
          operandProfile, operandHeight, strictAlias, ?_⟩), fun _ => trivial⟩
        rcases ordered with ⟨first, second⟩ | ⟨first, second⟩
        · exact Or.inr ⟨second, first⟩
        · exact Or.inl ⟨second, first⟩
      | false =>
        simp only [compileNode, decision, emptyTest, resetFalse, selfTest, swapTest,
          Bool.false_eq_true, ite_false]
        rcases aliasKind with bodyAlias | referenceAlias
        · subst alias
          rcases ordered with ⟨leftEq, rightEq⟩ | ⟨leftEq, rightEq⟩
          · rw [leftEq, rightEq]
            cases operand with
            | empty =>
              rw [bodyIdentity]
              simp only [identity, SourceRecursiveIntersectionCode.unsupported, CodeAdmission]
            | reference name => cases operandProfile.1
            | node own rows level free =>
              rw [bodyIdentity]
              simp only [identity]
              by_cases seen : pair bodyId own.identity ∈ domain.key.seen
              · simp only [seen, ite_true, CodeAdmission]
              · simp only [seen, ite_false]
                simp only [bodyShape, payload]
                simpa [bodyShape] using mixed_rows_admission rootRequest start wholeCount entry body depth ordinary bodyId
                    initialPhysical heap facts bodyRows sourceChildren pattern patternId domain authentic
                    own rows level free true operandAvailable operandProfile operandHeight
            | union own members level free =>
              rw [bodyIdentity]
              simp only [identity]
              by_cases seen : pair bodyId own.identity ∈ domain.key.seen
              · simp only [seen, ite_true, CodeAdmission]
              · simp only [seen, ite_false]
                simp only [bodyShape, payload]
                simpa [bodyShape] using mixed_union_admission rootRequest start wholeCount entry body depth ordinary bodyId
                    heap facts pattern patternId domain authentic body (Or.inl rfl) own members level free
                    true operandAvailable operandProfile operandHeight
            | mu own storedBody storedDepth storedOrdinary =>
              rw [bodyIdentity]
              simp only [identity]
              by_cases seen : pair bodyId own.identity ∈ domain.key.seen
              · simp only [seen, ite_true, CodeAdmission]
              · simp only [seen, ite_false]
                simp only [bodyShape, payload]
                have same := muOriginal own storedBody storedDepth storedOrdinary operandAvailable operandProfile
                rw [same]
                simpa only [bodyShape] using body_mu_enter_admission rootRequest start initialPhysical wholeCount
                  entry body depth ordinary bodyId bodyEntry bodyRows bodyShape bodyIdentity
                  pattern patternId domain domain authentic (Or.inl rfl)
          · rw [leftEq, rightEq]
            cases operand with
            | empty =>
              rw [bodyIdentity]
              simp only [identity, SourceRecursiveIntersectionCode.unsupported, CodeAdmission]
            | reference name => cases operandProfile.1
            | node own rows level free =>
              rw [bodyIdentity]
              simp only [identity]
              by_cases seen : pair own.identity bodyId ∈ domain.key.seen
              · simp only [seen, ite_true, CodeAdmission]
              · simp only [seen, ite_false]
                simp only [bodyShape, payload]
                simpa [bodyShape] using mixed_rows_admission rootRequest start wholeCount entry body depth ordinary bodyId
                    initialPhysical heap facts bodyRows sourceChildren pattern patternId domain authentic
                    own rows level free false operandAvailable operandProfile operandHeight
            | union own members level free =>
              rw [bodyIdentity]
              simp only [identity]
              by_cases seen : pair own.identity bodyId ∈ domain.key.seen
              · simp only [seen, ite_true, CodeAdmission]
              · simp only [seen, ite_false]
                simp only [bodyShape, payload]
                simpa [bodyShape] using mixed_union_admission rootRequest start wholeCount entry body depth ordinary bodyId
                    heap facts pattern patternId domain authentic body (Or.inl rfl) own members level free
                    false operandAvailable operandProfile operandHeight
            | mu own storedBody storedDepth storedOrdinary =>
              rw [bodyIdentity]
              simp only [identity]
              by_cases seen : pair own.identity bodyId ∈ domain.key.seen
              · simp only [seen, ite_true, CodeAdmission]
              · simp only [seen, ite_false]
                simp only [bodyShape, payload]
                have same := muOriginal own storedBody storedDepth storedOrdinary operandAvailable operandProfile
                have wrongOrder := swapTest
                rw [leftEq, rightEq, same, bodyShape] at wrongOrder
                have tagOrder : compare (2 : Nat) 1 = .gt := by decide
                simp [SourceRecursiveIntersectionControl.greater, SourceRecursiveIntersectionControl.compareValue, tag, tagOrder] at wrongOrder
        · subst alias
          rcases ordered with ⟨leftEq, rightEq⟩ | ⟨leftEq, rightEq⟩
          · rw [leftEq, rightEq]
            cases operand with
            | empty => simp only [identity, SourceRecursiveIntersectionCode.unsupported, CodeAdmission]
            | reference name => cases operandProfile.1
            | node own rows level free =>
              simp only [identity]
              by_cases seen : pair entry.identity own.identity ∈ domain.key.seen
              · simp only [seen, ite_true, CodeAdmission]
              · simp only [seen, ite_false]
                simp only [payload]
                apply source_reference_admission rootRequest start initialPhysical wholeCount
                  entry body depth ordinary bodyId sourceHeap initialGrowth key stored domain
                  (.node own rows level free) true
                exact Or.inl (Or.inl ⟨universeProfile, operandProfile, Or.inr nonempty⟩)
            | union own members level free =>
              simp only [identity]
              by_cases seen : pair entry.identity own.identity ∈ domain.key.seen
              · simp only [seen, ite_true, CodeAdmission]
              · simp only [seen, ite_false]
                simp only [payload]
                exact mixed_union_admission rootRequest start wholeCount entry body depth ordinary bodyId
                  heap facts pattern patternId domain authentic (.reference (.interned entry.identity)) (Or.inr rfl)
                  own members level free true operandAvailable operandProfile operandHeight
            | mu own storedBody storedDepth storedOrdinary =>
              simp only [identity]
              by_cases seen : pair entry.identity own.identity ∈ domain.key.seen
              · simp only [seen, ite_true, CodeAdmission]
              · simp only [seen, ite_false]
                simp only [payload]
                have same := muOriginal own storedBody storedDepth storedOrdinary operandAvailable operandProfile
                have wrongOrder := swapTest
                rw [leftEq, rightEq, same] at wrongOrder
                have tagOrder : compare (4 : Nat) 2 = .gt := by decide
                simp [SourceRecursiveIntersectionControl.greater, SourceRecursiveIntersectionControl.compareValue, tag, tagOrder] at wrongOrder
          · rw [leftEq, rightEq]
            cases operand with
            | empty => simp only [identity, SourceRecursiveIntersectionCode.unsupported, CodeAdmission]
            | reference name => cases operandProfile.1
            | node own rows level free =>
              simp only [identity]
              by_cases seen : pair own.identity entry.identity ∈ domain.key.seen
              · simp only [seen, ite_true, CodeAdmission]
              · simp only [seen, ite_false]
                simp only [payload]
                apply source_reference_admission rootRequest start initialPhysical wholeCount
                  entry body depth ordinary bodyId sourceHeap initialGrowth key stored domain
                  (.node own rows level free) false
                exact Or.inl (Or.inl ⟨operandProfile, universeProfile, Or.inr nonempty⟩)
            | union own members level free =>
              simp only [identity]
              by_cases seen : pair own.identity entry.identity ∈ domain.key.seen
              · simp only [seen, ite_true, CodeAdmission]
              · simp only [seen, ite_false]
                simp only [payload]
                exact mixed_union_admission rootRequest start wholeCount entry body depth ordinary bodyId
                  heap facts pattern patternId domain authentic (.reference (.interned entry.identity)) (Or.inr rfl)
                  own members level free false operandAvailable operandProfile operandHeight
            | mu own storedBody storedDepth storedOrdinary =>
              simp only [identity]
              by_cases seen : pair own.identity entry.identity ∈ domain.key.seen
              · simp only [seen, ite_true, CodeAdmission]
              · simp only [seen, ite_false]
                simp only [payload]
                have same := muOriginal own storedBody storedDepth storedOrdinary operandAvailable operandProfile
                rw [same]
                exact universe_reference_enter_admission rootRequest start initialPhysical wholeCount
                  entry body depth ordinary bodyId pattern patternId domain domain authentic (Or.inl rfl)
end MixedCompiler
end MicroCFTA.SourceCurrentNativeWarmAdmission

namespace MicroCFTA.SourceCurrentNativeWarmAdmission
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedBinderProtocol (NodeKey)
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceEqualityNativeDemand
open SourceCurrentAllocatedNativePhysicalTraceCompletion (Trace)
open SourceCurrentAllocatedNativePhysicalExecution (InputsThrough)
open SourceEqualityNativeDemandOperations (FieldsThrough)
open SourceCurrentAllocatedNativeSourceWarmEntry (AuthenticEntryAt)
open SourceCurrentNativeWarmCMDefinitions (Qualified)
open SourceSynthesisTypeSyntax (Library Query)
open SourceSynthesisFirstOrderConstruction (Expression)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSynthesisGeneralizeSyntax.Guard
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Profile" => SourceCurrentAllocatedNativeClosedResetProfile.Profile
local notation "ordinarySymbols" => SourceSynthesisUniverseCallerBoundary.ordinarySymbols
open InternedNestedFacts InternedEdgeResidency
open SourceRecursiveIntersectionControl (identity tag pair decision payload)
open SourceCurrentAllocatedNativeGeneralCMHistory (ClosedQualified)
open SourceCurrentAllocatedNativeSourceWarmEntry (MixedQualifiedAt)
open SourceSynthesisUniversePrefixHeight (height)
local notation "Node" => Value Symbol Guard

section AuxiliaryCompiler
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
variable (rootRequest : NodeRequest Symbol Guard) (start : Checked width)
  (initialPhysical : SourceCurrentAllocatedNativePhysicalCache.Valid start.native)
  (wholeCount : Nat)
  (entry : Interned NodeKey) (body depth ordinary : Node) (bodyId : Nat)

omit [DecidableEq (EdgeKey Symbol Guard)] in
private theorem body_self_code (domain : Interned IntersectionFlatMemoKeyDomain.DomainKey)
    (own : Interned NodeKey) (rows : List (EdgeValue Symbol Guard)) :
    compileNode ⟨domain, .node own rows 0 [.interned entry.identity], .node own rows 0 [.interned entry.identity]⟩ =
      if pair own.identity own.identity ∈ domain.key.seen then .pure (SourceRecursiveIntersectionControl.repeatedValue
        (pair own.identity own.identity)) else compileRows domain rows rows := by
  have selected : decision domain.key (.node own rows 0 [.interned entry.identity]) (.node own rows 0 [.interned entry.identity]) =
      if pair own.identity own.identity ∈ domain.key.seen then .repeated (pair own.identity own.identity) else .ordinary := by
    simp [decision, SourceRecursiveIntersectionControl.hasEmpty, SourceRecursiveIntersectionControl.reset,
      SourceRecursiveIntersectionControl.closedSelf, SourceRecursiveIntersectionControl.greater,
      SourceRecursiveIntersectionControl.compareValue, tag, identity, payload, Value.referenceOf, Value.free]
  by_cases seen : pair own.identity own.identity ∈ domain.key.seen
  · simp only [compileNode, selected, seen, ite_true]
  · simp only [compileNode, selected, seen, ite_false]

omit [DecidableEq (EdgeKey Symbol Guard)] in
private theorem reference_self_code (domain : Interned IntersectionFlatMemoKeyDomain.DomainKey) :
    compileNode (⟨domain, .reference (.interned entry.identity), .reference (.interned entry.identity)⟩ :
      NodeRequest Symbol Guard) =
      if pair entry.identity entry.identity ∈ domain.key.seen then .pure (SourceRecursiveIntersectionControl.repeatedValue
        (pair entry.identity entry.identity))
      else compileReference domain entry.identity (.reference (.interned entry.identity)) true := by
  have empty : SourceRecursiveIntersectionControl.hasEmpty
      (.reference (.interned entry.identity) : Node) (.reference (.interned entry.identity)) = false := rfl
  have restart : SourceRecursiveIntersectionControl.reset domain.key
      (.reference (.interned entry.identity) : Node) (.reference (.interned entry.identity)) = false := rfl
  have self : SourceRecursiveIntersectionControl.closedSelf
      (.reference (.interned entry.identity) : Node) (.reference (.interned entry.identity)) = false := by
    simp [SourceRecursiveIntersectionControl.closedSelf, Value.free]
  have order : SourceRecursiveIntersectionControl.greater
      (.reference (.interned entry.identity) : Node) (.reference (.interned entry.identity)) = false := by
    simp [SourceRecursiveIntersectionControl.greater, SourceRecursiveIntersectionControl.compareValue,
      tag, SourceRecursiveIntersectionSchedule.reference_interned]
  have selected : decision domain.key
      (.reference (.interned entry.identity) : Node) (.reference (.interned entry.identity)) =
      if pair entry.identity entry.identity ∈ domain.key.seen then
        .repeated (pair entry.identity entry.identity) else .leftReference := by
    simp [decision, empty, restart, self, order, identity, payload]
  by_cases seen : pair entry.identity entry.identity ∈ domain.key.seen
  · simp only [compileNode, selected, seen, ite_true]
  · simp only [compileNode, selected, seen, ite_false]

omit [DecidableEq (EdgeKey Symbol Guard)] in
private theorem universe_reference_code (domain : Interned IntersectionFlatMemoKeyDomain.DomainKey) :
    compileNode ⟨domain, .mu entry body depth ordinary, .reference (.interned entry.identity)⟩ =
      if pair entry.identity entry.identity ∈ domain.key.seen then .pure (SourceRecursiveIntersectionControl.repeatedValue
        (pair entry.identity entry.identity))
      else compileMu domain (.mu entry body depth ordinary) (.reference (.interned entry.identity)) := by
  have tagOrder : compare (2 : Nat) 4 = .lt := by decide
  have selected : decision domain.key (.mu entry body depth ordinary) (.reference (.interned entry.identity)) =
      if pair entry.identity entry.identity ∈ domain.key.seen then .repeated (pair entry.identity entry.identity) else .leftMu := by
    simp [decision, SourceRecursiveIntersectionControl.hasEmpty, SourceRecursiveIntersectionControl.reset,
      SourceRecursiveIntersectionControl.closedSelf, SourceRecursiveIntersectionControl.greater,
      SourceRecursiveIntersectionControl.compareValue, tag, identity, payload, Value.referenceOf, Value.free, tagOrder]
  by_cases seen : pair entry.identity entry.identity ∈ domain.key.seen
  · simp only [compileNode, selected, seen, ite_true]
  · simp only [compileNode, selected, seen, ite_false]

omit [DecidableEq (EdgeKey Symbol Guard)] in
private theorem body_reference_code (domain : Interned IntersectionFlatMemoKeyDomain.DomainKey)
    (own : Interned NodeKey) (rows : List (EdgeValue Symbol Guard)) :
    compileNode ⟨domain, .node own rows 0 [.interned entry.identity], .reference (.interned entry.identity)⟩ =
      if pair own.identity entry.identity ∈ domain.key.seen then .pure (SourceRecursiveIntersectionControl.repeatedValue
        (pair own.identity entry.identity))
      else compileReference domain entry.identity (.node own rows 0 [.interned entry.identity]) false := by
  have tagOrder : compare (1 : Nat) 4 = .lt := by decide
  have selected : decision domain.key (.node own rows 0 [.interned entry.identity]) (.reference (.interned entry.identity)) =
      if pair own.identity entry.identity ∈ domain.key.seen then .repeated (pair own.identity entry.identity) else .rightReference := by
    simp [decision, SourceRecursiveIntersectionControl.hasEmpty, SourceRecursiveIntersectionControl.reset,
      SourceRecursiveIntersectionControl.closedSelf, SourceRecursiveIntersectionControl.greater,
      SourceRecursiveIntersectionControl.compareValue, tag, identity, payload, Value.referenceOf, Value.free, tagOrder]
  by_cases seen : pair own.identity entry.identity ∈ domain.key.seen
  · simp only [compileNode, selected, seen, ite_true]
  · simp only [compileNode, selected, seen, ite_false]

omit [DecidableEq (EdgeKey Symbol Guard)] in
private theorem body_universe_code (domain : Interned IntersectionFlatMemoKeyDomain.DomainKey)
    (own : Interned NodeKey) (rows : List (EdgeValue Symbol Guard)) :
    compileNode ⟨domain, .node own rows 0 [.interned entry.identity], .mu entry body depth ordinary⟩ =
      if pair own.identity entry.identity ∈ domain.key.seen then .pure (SourceRecursiveIntersectionControl.repeatedValue
        (pair own.identity entry.identity))
      else compileMu domain (.node own rows 0 [.interned entry.identity]) (.mu entry body depth ordinary) := by
  have tagOrder : compare (1 : Nat) 2 = .lt := by decide
  have selected : decision domain.key (.node own rows 0 [.interned entry.identity]) (.mu entry body depth ordinary) =
      if pair own.identity entry.identity ∈ domain.key.seen then .repeated (pair own.identity entry.identity) else .rightMu := by
    simp [decision, SourceRecursiveIntersectionControl.hasEmpty, SourceRecursiveIntersectionControl.reset,
      SourceRecursiveIntersectionControl.closedSelf, SourceRecursiveIntersectionControl.greater,
      SourceRecursiveIntersectionControl.compareValue, tag, identity, payload, Value.referenceOf, Value.free, tagOrder]
  by_cases seen : pair own.identity entry.identity ∈ domain.key.seen
  · simp only [compileNode, selected, seen, ite_true]
  · simp only [compileNode, selected, seen, ite_false]

include initialPhysical in
private theorem auxiliary_compile_admission
    (sourceHeap : InternedConstructorTemplates.State Symbol Guard)
    (sourceGrowth : Grows sourceHeap start.native.machine.heap) (key : NodeKey)
    (stored : sourceHeap.nodeRecords key = some (.mu entry body depth ordinary))
    (bodyEntry : Interned NodeKey) (bodyRows : List (EdgeValue Symbol Guard))
    (bodyShape : body = .node bodyEntry bodyRows 0 [.interned entry.identity])
    (bodyIdentity : identity body = some bodyId)
    (sourceChildren : ∀ row ∈ bodyRows, ∀ child ∈ row.children,
      child = .reference (.interned entry.identity) ∨ Profile entry.identity child)
    (matched : ∀ pair ∈ SourceRecursiveIntersectionKernel.pairs bodyRows bodyRows,
      pair.1 = pair.2 ∨ pair.1.children.length ≠ pair.2.children.length)
    (request : NodeRequest Symbol Guard)
    (auxiliary : ∃ (pattern : Node) (patternId : Nat) (originalDomain : Interned IntersectionFlatMemoKeyDomain.DomainKey),
      AuthenticEntryAt (width := width) rootRequest start wholeCount entry body depth ordinary
        pattern patternId originalDomain ∧
      let universeValue : Node := .mu entry body depth ordinary
      let referenceValue : Node := .reference (.interned entry.identity)
      let e := pair bodyId entry.identity
      let d := pair entry.identity entry.identity
      let first := SourceRecursiveIntersectionDomain.extend originalDomain.key [entry.identity] e
      let diagonal := SourceRecursiveIntersectionDomain.extend originalDomain.key [entry.identity] d
      let bodyTerminal := SourceRecursiveIntersectionDomain.extend first [entry.identity] d
      let terminal := SourceRecursiveIntersectionDomain.extend diagonal [entry.identity] e
      (request.domain.key = first ∧ ((request.left = body ∧ request.right = body) ∨
        (request.left = referenceValue ∧ request.right = referenceValue) ∨
        (request.left = universeValue ∧ request.right = referenceValue))) ∨
      (request.domain.key = bodyTerminal ∧ request.left = body ∧ request.right = referenceValue) ∨
      (request.domain.key = diagonal ∧ ((request.left = body ∧ request.right = referenceValue) ∨
        (request.left = body ∧ request.right = universeValue))) ∨
      (request.domain.key = terminal ∧ ((request.left = body ∧ request.right = body) ∨
        (request.left = referenceValue ∧ request.right = referenceValue) ∨
        (request.left = universeValue ∧ request.right = referenceValue)))) :
    CodeAdmission (width := width) rootRequest start wholeCount entry body depth ordinary bodyId
      (compileNode request) := by
  have bodyIdEq : bodyEntry.identity = bodyId := by
    apply Option.some.inj
    calc
      some bodyEntry.identity = identity body := by rw [bodyShape]; rfl
      _ = some bodyId := bodyIdentity
  subst bodyId
  have bodySelf (domain : Interned IntersectionFlatMemoKeyDomain.DomainKey) :
      compileNode ⟨domain, body, body⟩ =
        if pair bodyEntry.identity bodyEntry.identity ∈ domain.key.seen then
          .pure (SourceRecursiveIntersectionControl.repeatedValue (pair bodyEntry.identity bodyEntry.identity))
        else compileRows domain bodyRows bodyRows := by
    simpa only [bodyShape] using body_self_code entry domain bodyEntry bodyRows
  have bodyReference (domain : Interned IntersectionFlatMemoKeyDomain.DomainKey) :
      compileNode ⟨domain, body, .reference (.interned entry.identity)⟩ =
        if pair bodyEntry.identity entry.identity ∈ domain.key.seen then
          .pure (SourceRecursiveIntersectionControl.repeatedValue (pair bodyEntry.identity entry.identity))
        else compileReference domain entry.identity body false := by
    simpa only [bodyShape] using body_reference_code entry domain bodyEntry bodyRows
  have bodyUniverse (domain : Interned IntersectionFlatMemoKeyDomain.DomainKey) :
      compileNode ⟨domain, body, .mu entry body depth ordinary⟩ =
        if pair bodyEntry.identity entry.identity ∈ domain.key.seen then
          .pure (SourceRecursiveIntersectionControl.repeatedValue (pair bodyEntry.identity entry.identity))
        else compileMu domain body (.mu entry body depth ordinary) := by
    simpa only [bodyShape] using body_universe_code entry body depth ordinary domain bodyEntry bodyRows
  rcases request with ⟨domain, left, right⟩
  obtain ⟨pattern, patternId, originalDomain, authentic, contextCases⟩ := auxiliary
  dsimp only at contextCases
  rcases contextCases with first | bodyTerminal | diagonal | terminal
  · rcases first with ⟨atKey, alternatives⟩
    rcases alternatives with ⟨leftEq, rightEq⟩ | ⟨leftEq, rightEq⟩ | ⟨leftEq, rightEq⟩
    · rw [leftEq, rightEq]
      rw [bodySelf domain]
      split
      · trivial
      · exact auxiliary_rows_admission rootRequest start wholeCount entry body depth ordinary bodyEntry.identity
          bodyRows sourceChildren matched pattern patternId originalDomain domain authentic (Or.inl atKey)
    · rw [leftEq, rightEq, reference_self_code entry domain]
      split
      · trivial
      · apply source_reference_admission rootRequest start initialPhysical wholeCount entry body depth ordinary
          bodyEntry.identity sourceHeap sourceGrowth key stored domain (.reference (.interned entry.identity)) true
        right
        refine ⟨pattern, patternId, originalDomain, authentic, ?_⟩
        dsimp only
        exact Or.inl ⟨atKey, Or.inr (Or.inr ⟨rfl, rfl⟩)⟩
    · rw [leftEq, rightEq, universe_reference_code entry body depth ordinary domain]
      split
      · trivial
      · exact universe_reference_enter_admission rootRequest start initialPhysical wholeCount
          entry body depth ordinary bodyEntry.identity pattern patternId originalDomain domain authentic (Or.inr atKey)
  · rcases bodyTerminal with ⟨atKey, leftEq, rightEq⟩
    have seen : pair bodyEntry.identity entry.identity ∈ domain.key.seen := by
      rw [atKey]
      exact (SourceRecursiveIntersectionDomain.extend_seen _ _ _ _).mpr (Or.inr
        ((SourceRecursiveIntersectionDomain.extend_seen _ _ _ _).mpr (Or.inl rfl)))
    rw [leftEq, rightEq]
    rw [bodyReference domain, ite_eq_left seen]
    trivial
  · rcases diagonal with ⟨atKey, alternatives⟩
    rcases alternatives with ⟨leftEq, rightEq⟩ | ⟨leftEq, rightEq⟩
    · rw [leftEq, rightEq]
      rw [bodyReference domain]
      split
      · trivial
      · apply source_reference_admission rootRequest start initialPhysical wholeCount entry body depth ordinary
          bodyEntry.identity sourceHeap sourceGrowth key stored domain body false
        right
        refine ⟨pattern, patternId, originalDomain, authentic, ?_⟩
        dsimp only
        exact Or.inr (Or.inr (Or.inl ⟨atKey, Or.inr ⟨rfl, rfl⟩⟩))
    · rw [leftEq, rightEq]
      rw [bodyUniverse domain]
      split
      · trivial
      · exact body_mu_enter_admission rootRequest start initialPhysical wholeCount
          entry body depth ordinary bodyEntry.identity bodyEntry bodyRows bodyShape bodyIdentity
          pattern patternId originalDomain domain authentic (Or.inr atKey)
  · rcases terminal with ⟨atKey, alternatives⟩
    have seen : pair entry.identity entry.identity ∈ domain.key.seen := by
      rw [atKey]
      exact (SourceRecursiveIntersectionDomain.extend_seen _ _ _ _).mpr (Or.inr
        ((SourceRecursiveIntersectionDomain.extend_seen _ _ _ _).mpr (Or.inl rfl)))
    rcases alternatives with ⟨leftEq, rightEq⟩ | ⟨leftEq, rightEq⟩ | ⟨leftEq, rightEq⟩
    · rw [leftEq, rightEq]
      rw [bodySelf domain]
      split
      · trivial
      · exact auxiliary_rows_admission rootRequest start wholeCount entry body depth ordinary bodyEntry.identity
          bodyRows sourceChildren matched pattern patternId originalDomain domain authentic (Or.inr atKey)
    · rw [leftEq, rightEq, reference_self_code entry domain, ite_eq_left seen]
      trivial
    · rw [leftEq, rightEq, universe_reference_code entry body depth ordinary domain, ite_eq_left seen]
      trivial
end AuxiliaryCompiler
end MicroCFTA.SourceCurrentNativeWarmAdmission

namespace MicroCFTA.SourceCurrentNativeWarmAdmission
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedBinderProtocol (NodeKey)
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceEqualityNativeDemand
open SourceCurrentAllocatedNativePhysicalTraceCompletion (Trace)
open SourceCurrentAllocatedNativePhysicalExecution (InputsThrough)
open SourceEqualityNativeDemandOperations (FieldsThrough)
open SourceCurrentAllocatedNativeSourceWarmEntry (AuthenticEntryAt)
open SourceCurrentNativeWarmCMDefinitions (Qualified)
open SourceSynthesisTypeSyntax (Library Query)
open SourceSynthesisFirstOrderConstruction (Expression)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSynthesisGeneralizeSyntax.Guard
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Profile" => SourceCurrentAllocatedNativeClosedResetProfile.Profile
local notation "ordinarySymbols" => SourceSynthesisUniverseCallerBoundary.ordinarySymbols
open InternedNestedFacts InternedEdgeResidency
open SourceRecursiveIntersectionControl (identity tag pair decision payload)
open SourceCurrentAllocatedNativeGeneralCMHistory (ClosedQualified)
open SourceCurrentAllocatedNativeSourceWarmEntry (MixedQualifiedAt)
open SourceSynthesisUniversePrefixHeight (height)
local notation "Node" => Value Symbol Guard

section PrefixInduction
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
variable (rootRequest : NodeRequest Symbol Guard) (start : Checked width)
  (initialPhysical : SourceCurrentAllocatedNativePhysicalCache.Valid start.native)
  (wholeCount : Nat)
  (entry : Interned NodeKey) (body depth ordinary : Node) (bodyId : Nat)
variable (lib : Library) (query : Query) (signed : Int) (whole : Expression)
  (accepted : SourceSynthesisCurrentConstruction.firstOrderRaw lib query signed = .ok whole)
  (rootValue : Node) (sourceHeap : InternedConstructorTemplates.State Symbol Guard)
  (built : InternedFreshOrdinaryConstruction.build (ordinarySymbols whole) [] empty = .done rootValue sourceHeap)
  (key : NodeKey) (stored : sourceHeap.nodeRecords key = some (.mu entry body depth ordinary))
  (sourceGrowth : Grows sourceHeap start.native.machine.heap)
  (bodyEntry : Interned NodeKey) (bodyRows : List (EdgeValue Symbol Guard))
  (bodyShape : body = .node bodyEntry bodyRows 0 [.interned entry.identity])
  (bodyIdentity : identity body = some bodyId)
  (sourceChildren : ∀ row ∈ bodyRows, ∀ child ∈ row.children,
    child = .reference (.interned entry.identity) ∨ Profile entry.identity child)
  (matched : ∀ pair ∈ SourceRecursiveIntersectionKernel.pairs bodyRows bodyRows,
    pair.1 = pair.2 ∨ pair.1.children.length ≠ pair.2.children.length)
  (universeProfile : Profile entry.identity (.mu entry body depth ordinary))

include initialPhysical accepted built stored sourceGrowth bodyShape bodyIdentity sourceChildren matched universeProfile

private theorem source_compile_admission
    (heap : InternedConstructorTemplates.State Symbol Guard) (facts : Facts heap) (growth : Grows sourceHeap heap)
    (request : NodeRequest Symbol Guard)
    (leftAvailable : Available heap request.left) (rightAvailable : Available heap request.right)
    (admitted : NodeAdmission (width := width) rootRequest start wholeCount entry body depth ordinary bodyId request) :
    CodeAdmission (width := width) rootRequest start wholeCount entry body depth ordinary bodyId
      (compileNode request) := by
  rcases admitted with closed | auxiliary
  · rcases closed with closed | mixed
    · exact closed_compile_admission rootRequest start wholeCount entry body depth ordinary bodyId
        lib query signed whole accepted rootValue sourceHeap built key stored bodyEntry bodyRows bodyShape
        universeProfile heap facts growth request leftAvailable rightAvailable closed
    · exact mixed_compile_admission rootRequest start initialPhysical wholeCount entry body depth ordinary bodyId
        lib query signed whole accepted rootValue sourceHeap built key stored sourceGrowth bodyEntry bodyRows bodyShape
        bodyIdentity sourceChildren universeProfile heap facts growth request leftAvailable rightAvailable mixed
  · exact auxiliary_compile_admission rootRequest start initialPhysical wholeCount entry body depth ordinary bodyId
      sourceHeap sourceGrowth key stored bodyEntry bodyRows bodyShape bodyIdentity sourceChildren matched request auxiliary

private theorem step_admission
    (used : Nat) (control nextControl : Control Node) (before after : Checked width)
    (within : used + 1 ≤ wholeCount)
    (prefixActual : Trace used (.code (.node rootRequest .pure))
      start control before)
    (inputs : SourceCurrentAllocatedNativePhysicalExecution.Inputs control before)
    (one : SourceEqualityNativeDemand.step control before = .yielded nextControl after)
    (admitted : ControlAdmission (width := width) rootRequest start wholeCount
      entry body depth ordinary bodyId control) :
    ControlAdmission (width := width) rootRequest start wholeCount
      entry body depth ordinary bodyId nextControl := by
  have reached := physical_at_root_prefix rootRequest start initialPhysical sourceHeap sourceGrowth
    used control before prefixActual
  cases control with
  | edgeBody request next =>
    obtain ⟨code, same, certificate⟩ := checked_body_yield_admission rootRequest start wholeCount
      entry body depth ordinary bodyId request next before after nextControl admitted.1 admitted.2 one
    rw [same]
    exact certificate
  | code code =>
    cases code with
    | pure value | fail failure =>
      simp only [SourceEqualityNativeDemand.step, SourceRecursiveIntersectionNative.step, SourceEqualityNativeDemand.lift] at one
      cases one
    | work job next =>
      simp only [SourceEqualityNativeDemand.step, SourceRecursiveIntersectionNative.step, SourceEqualityNativeDemand.lift] at one
      cases one
      exact admitted _
    | read name next =>
      simp only [SourceEqualityNativeDemand.step, SourceRecursiveIntersectionNative.step, SourceEqualityNativeDemand.lift] at one
      cases one
      exact admitted used before next within prefixActual
    | enter domain left right first second next =>
      simp only [SourceEqualityNativeDemand.step, SourceRecursiveIntersectionNative.step, SourceEqualityNativeDemand.lift] at one
      cases one
      apply admitted used before next within prefixActual
      exact Trace.cons _ _ _ _ _ _ 0 inputs rfl (.refl _ _)
    | optionalBinder binder value next =>
      cases constructed : SourceRecursiveIntersectionMaybeMu.maybeMu binder value before.native.machine.heap with
      | pending key heap =>
        simp only [SourceEqualityNativeDemand.step, SourceRecursiveIntersectionNative.step,
          constructed, SourceEqualityNativeDemand.lift] at one
        cases one
      | done value heap =>
        simp only [SourceEqualityNativeDemand.step, SourceRecursiveIntersectionNative.step,
          constructed, SourceEqualityNativeDemand.lift] at one
        cases one
        exact admitted value
    | finishNode handle value next | finishEdge handle value next =>
      simp only [SourceEqualityNativeDemand.step, SourceRecursiveIntersectionNative.step, SourceEqualityNativeDemand.lift] at one
      cases one
      exact admitted
    | node request next =>
      have compiled := source_compile_admission rootRequest start initialPhysical wholeCount
        entry body depth ordinary bodyId lib query signed whole accepted rootValue sourceHeap built key stored
        sourceGrowth bodyEntry bodyRows bodyShape bodyIdentity sourceChildren matched universeProfile
        before.native.machine.heap reached.1.machine.1 reached.2 request inputs.1.2.1 inputs.1.2.2 admitted.1
      cases selected : lookupNode width request before.native with
      | mk selection chosen =>
        cases selection with
        | direct actual =>
          have same := (SourceRecursiveIntersectionNative.lookupNode_direct request actual before.native chosen selected).1
          subst actual
          simp only [SourceEqualityNativeDemand.step, SourceRecursiveIntersectionNative.step,
            selected, SourceEqualityNativeDemand.lift] at one
          cases one
          exact code_admission_bind rootRequest start wholeCount entry body depth ordinary bodyId
            _ next compiled admitted.2
        | memoized handle =>
          obtain ⟨key, keyed, _published, _sameMachine⟩ :=
            SourceRecursiveIntersectionNative.lookupNode_memoized request before.native chosen handle selected
          cases demanded : demandNode handle chosen with
          | mk observation running =>
            cases observation with
            | absent | busy =>
              simp only [SourceEqualityNativeDemand.step, SourceRecursiveIntersectionNative.step,
                selected, demanded, SourceEqualityNativeDemand.lift] at one
              cases one
            | ready value =>
              simp only [SourceEqualityNativeDemand.step, SourceRecursiveIntersectionNative.step,
                selected, demanded, SourceEqualityNativeDemand.lift] at one
              cases one
              exact admitted.2 value
            | evaluate actual =>
              have same := SourceCurrentAllocatedNativePhysicalCache.node_started request actual before.native chosen running
                handle reached.1 inputs.1 (inputs.2 key keyed) selected demanded
              subst actual
              simp only [SourceEqualityNativeDemand.step, SourceRecursiveIntersectionNative.step,
                selected, demanded, SourceEqualityNativeDemand.lift] at one
              cases one
              apply code_admission_bind rootRequest start wholeCount entry body depth ordinary bodyId
                _ _ compiled
              intro value
              exact admitted.2 value
    | edge request next =>
      cases selected : lookupEdge width request before.native with
      | mk handle chosen =>
        cases demanded : demandEdge handle chosen with
        | mk observation running =>
          cases observation with
          | absent | busy =>
            simp only [SourceEqualityNativeDemand.step, selected, demanded] at one
            cases one
          | ready value =>
            simp only [SourceEqualityNativeDemand.step, selected, demanded] at one
            cases one
            exact admitted.2 value
          | evaluate actual =>
            have same := SourceCurrentAllocatedNativePhysicalCache.edge_started request actual before.native chosen running
              handle reached.1 inputs.1 inputs.2 selected demanded
            subst actual
            simp only [SourceEqualityNativeDemand.step, selected, demanded] at one
            cases one
            exact ⟨admitted.1, fun value => admitted.2 value⟩

private theorem trace_admission
    (count prefixUsed : Nat) (control final : Control Node) (before after : Checked width)
    (prefixActual : Trace prefixUsed (.code (.node rootRequest .pure))
      start control before)
    (actual : Trace count control before final after)
    (within : prefixUsed + count ≤ wholeCount)
    (admitted : ControlAdmission (width := width) rootRequest start wholeCount
      entry body depth ordinary bodyId control) :
    ControlAdmission (width := width) rootRequest start wholeCount
      entry body depth ordinary bodyId final := by
  induction actual generalizing prefixUsed with
  | refl => exact admitted
  | cons control before next reached final after count inputs one tail ih =>
    have nextAdmission := step_admission rootRequest start initialPhysical wholeCount entry body depth ordinary bodyId
      lib query signed whole accepted rootValue sourceHeap built key stored sourceGrowth bodyEntry bodyRows bodyShape
      bodyIdentity sourceChildren matched universeProfile prefixUsed control next before reached (by omega)
      prefixActual inputs one admitted
    have nextPrefix : Trace (prefixUsed + 1) (.code (.node rootRequest .pure))
        start next reached :=
      prefixActual.trans (Trace.cons _ _ _ _ _ _ 0 inputs one (.refl _ _))
    exact ih (prefixUsed + 1) nextPrefix (by omega) nextAdmission
end PrefixInduction
end MicroCFTA.SourceCurrentNativeWarmAdmission

namespace MicroCFTA.SourceCurrentNativeWarmAdmission
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedBinderProtocol (NodeKey)
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceEqualityNativeDemand
open SourceCurrentAllocatedNativeSourceWarmEntry (AuthenticEntryAt)
open SourceCurrentNativeWarmCMDefinitions (Qualified)
open SourceRecursiveIntersectionControl (identity tag pair decision payload)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSynthesisGeneralizeSyntax.Guard
local notation "Node" => Value Symbol Guard
local notation "Checked" => SourceEqualityNativeDemand.State

private theorem mu_payload_of_decision
    (domain : IntersectionFlatMemoKeyDomain.DomainKey) (left right : Node)
    (selected : decision domain left right = .bothMu ∨
      decision domain left right = .leftMu ∨ decision domain left right = .rightMu) :
    payload left right = .bothMu ∨ payload left right = .leftMu ∨ payload left right = .rightMu := by
  cases emptyTest : SourceRecursiveIntersectionControl.hasEmpty left right with
  | true =>
    simp only [decision, emptyTest, ite_true] at selected
    rcases selected with impossible | impossible | impossible <;> cases impossible
  | false =>
    simp only [decision, emptyTest, Bool.false_eq_true, ite_false] at selected
    cases resetTest : SourceRecursiveIntersectionControl.reset domain left right with
    | true =>
      simp only [resetTest, ite_true] at selected
      rcases selected with impossible | impossible | impossible <;> cases impossible
    | false =>
      simp only [resetTest, Bool.false_eq_true, ite_false] at selected
      cases selfTest : SourceRecursiveIntersectionControl.closedSelf left right with
      | true =>
        simp only [selfTest, ite_true] at selected
        rcases selected with impossible | impossible | impossible <;> cases impossible
      | false =>
        simp only [selfTest, Bool.false_eq_true, ite_false] at selected
        cases swapTest : SourceRecursiveIntersectionControl.greater left right with
        | true =>
          simp only [swapTest, ite_true] at selected
          rcases selected with impossible | impossible | impossible <;> cases impossible
        | false =>
          simp only [swapTest, Bool.false_eq_true, ite_false] at selected
          cases leftId : identity left with
          | none =>
            simp only [leftId] at selected
            rcases selected with impossible | impossible | impossible <;> cases impossible
          | some first =>
            cases rightId : identity right with
            | none =>
              simp only [leftId, rightId] at selected
              rcases selected with impossible | impossible | impossible <;> cases impossible
            | some second =>
              simp only [leftId, rightId] at selected
              by_cases seen : pair first second ∈ domain.seen
              · simp only [seen, ite_true] at selected
                rcases selected with impossible | impossible | impossible <;> cases impossible
              · simpa only [seen, ite_false] using selected

private theorem node_admission_mu_projection
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
    (rootRequest : NodeRequest Symbol Guard) (start : Checked width)
    (wholeCount : Nat)
    (entry : Interned NodeKey) (body depth ordinary : Node) (bodyId : Nat)
    (bodyEntry : Interned NodeKey) (bodyRows : List (EdgeValue Symbol Guard))
    (bodyShape : body = .node bodyEntry bodyRows 0 [.interned entry.identity])
    (request : NodeRequest Symbol Guard)
    (admitted : NodeAdmission (width := width) rootRequest start wholeCount
      entry body depth ordinary bodyId request)
    (selected : decision request.domain.key request.left request.right = .bothMu ∨
      decision request.domain.key request.left request.right = .leftMu ∨
      decision request.domain.key request.left request.right = .rightMu) :
    Qualified (width := width) rootRequest start wholeCount entry body depth ordinary request ∨
      ∃ (pattern : Node) (patternId : Nat)
        (originalDomain : Interned IntersectionFlatMemoKeyDomain.DomainKey),
        AuthenticEntryAt (width := width) rootRequest start wholeCount
          entry body depth ordinary pattern patternId originalDomain ∧
        ((request.domain.key = SourceRecursiveIntersectionDomain.extend originalDomain.key [entry.identity]
            (pair bodyId entry.identity) ∧
          request.left = .mu entry body depth ordinary ∧
          request.right = .reference (.interned entry.identity)) ∨
         (request.domain.key = SourceRecursiveIntersectionDomain.extend originalDomain.key [entry.identity]
            (pair entry.identity entry.identity) ∧
          request.left = body ∧ request.right = .mu entry body depth ordinary)) := by
  rcases admitted with qualified | auxiliary
  · exact Or.inl qualified
  · obtain ⟨pattern, patternId, originalDomain, authentic, contextCases⟩ := auxiliary
    dsimp only at contextCases
    have actualPayload := mu_payload_of_decision request.domain.key request.left request.right selected
    rcases contextCases with first | bodyTerminal | diagonal | terminal
    · rcases first with ⟨atKey, alternatives⟩
      rcases alternatives with ⟨leftEq, rightEq⟩ | ⟨leftEq, rightEq⟩ | ⟨leftEq, rightEq⟩
      · rw [leftEq, rightEq, bodyShape] at actualPayload
        simp only [payload] at actualPayload
        rcases actualPayload with impossible | impossible | impossible <;> cases impossible
      · rw [leftEq, rightEq] at actualPayload
        simp only [payload] at actualPayload
        rcases actualPayload with impossible | impossible | impossible <;> cases impossible
      · exact Or.inr ⟨pattern, patternId, originalDomain, authentic, Or.inl ⟨atKey, leftEq, rightEq⟩⟩
    · rcases bodyTerminal with ⟨_atKey, leftEq, rightEq⟩
      rw [leftEq, rightEq, bodyShape] at actualPayload
      simp only [payload] at actualPayload
      rcases actualPayload with impossible | impossible | impossible <;> cases impossible
    · rcases diagonal with ⟨atKey, alternatives⟩
      rcases alternatives with ⟨leftEq, rightEq⟩ | ⟨leftEq, rightEq⟩
      · rw [leftEq, rightEq, bodyShape] at actualPayload
        simp only [payload] at actualPayload
        rcases actualPayload with impossible | impossible | impossible <;> cases impossible
      · exact Or.inr ⟨pattern, patternId, originalDomain, authentic, Or.inr ⟨atKey, leftEq, rightEq⟩⟩
    · rcases terminal with ⟨atKey, alternatives⟩
      rcases alternatives with ⟨leftEq, rightEq⟩ | ⟨leftEq, rightEq⟩ | ⟨leftEq, rightEq⟩
      · rw [leftEq, rightEq, bodyShape] at actualPayload
        simp only [payload] at actualPayload
        rcases actualPayload with impossible | impossible | impossible <;> cases impossible
      · rw [leftEq, rightEq] at actualPayload
        simp only [payload] at actualPayload
        rcases actualPayload with impossible | impossible | impossible <;> cases impossible
      · have seen : pair entry.identity entry.identity ∈ request.domain.key.seen := by
          rw [atKey]
          exact (SourceRecursiveIntersectionDomain.extend_seen _ _ _ _).mpr (Or.inr
            ((SourceRecursiveIntersectionDomain.extend_seen _ _ _ _).mpr (Or.inl rfl)))
        have tagOrder : compare (2 : Nat) 4 = .lt := by decide
        have repeated : decision request.domain.key (.mu entry body depth ordinary)
            (.reference (.interned entry.identity)) = .repeated (pair entry.identity entry.identity) := by
          simp [decision, SourceRecursiveIntersectionControl.hasEmpty, SourceRecursiveIntersectionControl.reset,
            SourceRecursiveIntersectionControl.closedSelf, SourceRecursiveIntersectionControl.greater,
            SourceRecursiveIntersectionControl.compareValue, tag, identity, Value.referenceOf, Value.free, seen, tagOrder]
        rw [leftEq, rightEq, repeated] at selected
        rcases selected with impossible | impossible | impossible <;> cases impossible

end MicroCFTA.SourceCurrentNativeWarmAdmission

namespace MicroCFTA.SourceCurrentNativeWarmAdmission
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedBinderProtocol (NodeKey)
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceEqualityNativeDemand
open SourceCurrentAllocatedNativePhysicalTraceCompletion (Trace)
open SourceCurrentAllocatedNativePhysicalExecution (InputsThrough)
open SourceEqualityNativeDemandOperations (FieldsThrough)
open SourceCurrentAllocatedNativeSourceWarmEntry (AuthenticEntryAt)
open SourceCurrentNativeWarmCMDefinitions (Qualified)
open SourceSynthesisTypeSyntax (Library Query)
open SourceSynthesisFirstOrderConstruction (Expression)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSynthesisGeneralizeSyntax.Guard
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Profile" => SourceCurrentAllocatedNativeClosedResetProfile.Profile
local notation "ordinarySymbols" => SourceSynthesisUniverseCallerBoundary.ordinarySymbols
set_option autoImplicit false

/- Note [Mu owner admission at the original reader]
The selected Mu query and the original entry use one fixed actual-root trace.
The entry retains the full original pattern and its actual allocated domain.
The two auxiliary cases compare domain keys. They do not identify handles.
The result is an admission fact about the reached request. It is not a
semantic result hypothesis for a later child or optional instruction.
-/
private theorem warm_mu_query_prefix_admission
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
    (lib : Library) (query : Query) (signed : Int) (whole : Expression)
    (accepted : SourceSynthesisCurrentConstruction.firstOrderRaw lib query signed = .ok whole)
    (rootValue : Value Symbol Guard) (sourceHeap : InternedConstructorTemplates.State Symbol Guard)
    (built : InternedFreshOrdinaryConstruction.build (ordinarySymbols whole) [] empty =
      .done rootValue sourceHeap)
    (key : NodeKey) (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (stored : sourceHeap.nodeRecords key = some (.mu entry body depth ordinary))
    (rootRequest : NodeRequest Symbol Guard) (start : Checked width)
    (initialPhysical : SourceCurrentAllocatedNativePhysicalCache.Valid start.native)
    (sourceGrowth : Grows sourceHeap start.native.machine.heap)
    (rootDomain : rootRequest.domain = IntersectionEmptyDomain.emptyDomain)
    (leftProfile : Profile entry.identity rootRequest.left)
    (rightProfile : Profile entry.identity rootRequest.right)
    (operationsValid : SourceEqualityConstraintMemoAllocation.Valid start.operations)
    (fuel wholeCount queryUsed : Nat)
    (readerControl : Control (Value Symbol Guard)) (reader : Checked width)
    (queried : NodeRequest Symbol Guard)
    (queryNext : Value Symbol Guard → Code Symbol Guard (Value Symbol Guard))
    (queryBefore : Checked width)
    (wholeBound : wholeCount ≤ fuel)
    (wholeActual : Trace wholeCount (.code (.node rootRequest .pure))
      start readerControl reader)
    (queryBound : queryUsed ≤ wholeCount)
    (queryActual : Trace queryUsed (.code (.node rootRequest .pure))
      start
      (.code (.node queried queryNext)) queryBefore)
    (selectedMu :
      SourceRecursiveIntersectionControl.decision queried.domain.key queried.left queried.right = .bothMu ∨
      SourceRecursiveIntersectionControl.decision queried.domain.key queried.left queried.right = .leftMu ∨
      SourceRecursiveIntersectionControl.decision queried.domain.key queried.left queried.right = .rightMu)
    (inputs : InputsThrough fuel (.code (.node rootRequest .pure))
      start)
    (fields : FieldsThrough fuel (.code (.node rootRequest .pure))
      start) :
    Qualified (width := width) rootRequest start wholeCount entry body depth ordinary queried ∨
      ∃ (fullPattern : Value Symbol Guard) (patternId bodyId : Nat)
        (originalDomain : Interned IntersectionFlatMemoKeyDomain.DomainKey),
        SourceRecursiveIntersectionControl.identity body = some bodyId ∧
        AuthenticEntryAt (width := width) rootRequest start wholeCount
          entry body depth ordinary fullPattern patternId originalDomain ∧
        ((queried.domain.key = SourceRecursiveIntersectionDomain.extend originalDomain.key [entry.identity]
            (SourceRecursiveIntersectionControl.pair bodyId entry.identity) ∧
          queried.left = .mu entry body depth ordinary ∧
          queried.right = .reference (.interned entry.identity)) ∨
         (queried.domain.key = SourceRecursiveIntersectionDomain.extend originalDomain.key [entry.identity]
            (SourceRecursiveIntersectionControl.pair entry.identity entry.identity) ∧
          queried.left = body ∧ queried.right = .mu entry body depth ordinary)) := by
  have _retainedAdmissions := And.intro operationsValid
    (And.intro wholeBound (And.intro wholeActual (And.intro inputs fields)))
  have universeAvailable : Available start.native.machine.heap (.mu entry body depth ordinary) :=
    initialPhysical.machine.1.cached.nodes key _ (sourceGrowth.nodeRecords key _ stored)
  have universeAtoms : ∀ atom ∈ InternedBoundaryAtoms.atoms (.mu entry body depth ordinary),
      atom = .mu entry.identity := by
    intro atom occurrence
    simpa only [InternedBoundaryAtoms.atoms, List.mem_singleton] using occurrence
  have universeClosed : (Value.mu entry body depth ordinary).free = [] :=
    SourceSynthesisCurrentUniverseStartupAtoms.current_stored_universe_boundary_atoms_closed_after_growth
      lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
      start.native.machine.heap initialPhysical.machine.1 sourceGrowth (.mu entry body depth ordinary) universeAvailable universeAtoms
  have universeProfile : Profile entry.identity (.mu entry body depth ordinary) :=
    ⟨universeClosed, universeAtoms⟩
  obtain ⟨bodyEntry, bodyRows, bodyShape, matched⟩ :=
    SourceSynthesisCurrentUniverseBodyMatchedPairs.current_stored_universe_body_matching_pairs
      lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
      start.native.machine.heap initialPhysical.machine.1 sourceGrowth
  obtain ⟨classifiedEntry, marker, arrow, descriptors, classifiedShape, _bodyAvailable,
      _markerShape, _arrowChildren, _arrowKey, _catalog, _markerClosed, _markerAvailable,
      _markerAtoms, childKinds, _arrowRetained⟩ :=
    SourceSynthesisCurrentUniverseBodyChildClassification.current_stored_universe_body_physical_children_after_growth
      lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
      start.native.machine.heap initialPhysical.machine.1 sourceGrowth
  have sameRows : bodyRows = InternedConstructorTemplates.canonicalEdges (arrow :: descriptors) :=
    (Value.node.inj (bodyShape.symm.trans classifiedShape)).2.1
  have sourceChildren : ∀ row ∈ bodyRows, ∀ child ∈ row.children,
      child = .reference (.interned entry.identity) ∨ Profile entry.identity child := by
    intro row included child member
    rw [sameRows] at included
    rcases (childKinds row included).2.2 child member with reference | closed
    · exact Or.inl reference
    · obtain ⟨_sameMarker, _available, free, atomless⟩ := closed
      right
      refine ⟨free, ?_⟩
      intro atom occurrence
      rw [atomless] at occurrence
      cases occurrence
  let bodyId := bodyEntry.identity
  have bodyIdentity : SourceRecursiveIntersectionControl.identity body = some bodyId := by
    rw [bodyShape]
    rfl
  have initialAdmission : ControlAdmission (width := width) rootRequest start wholeCount
      entry body depth ordinary bodyId (.code (.node rootRequest .pure)) := by
    change NodeAdmission (width := width) rootRequest start wholeCount
      entry body depth ordinary bodyId rootRequest ∧ _
    exact ⟨Or.inl (Or.inl ⟨leftProfile, rightProfile, Or.inl rootDomain⟩), fun _ => True.intro⟩
  have reached := trace_admission rootRequest start initialPhysical wholeCount
    entry body depth ordinary bodyId lib query signed whole accepted rootValue sourceHeap built key stored
    sourceGrowth bodyEntry bodyRows bodyShape bodyIdentity sourceChildren matched universeProfile
    queryUsed 0 (.code (.node rootRequest .pure)) (.code (.node queried queryNext))
    start queryBefore (.refl _ _) queryActual
    (by simpa only [Nat.zero_add] using queryBound) initialAdmission
  change NodeAdmission (width := width) rootRequest start wholeCount
    entry body depth ordinary bodyId queried ∧ _ at reached
  rcases node_admission_mu_projection rootRequest start wholeCount entry body depth ordinary bodyId
      bodyEntry bodyRows bodyShape queried reached.1 selectedMu with qualified | auxiliary
  · exact Or.inl qualified
  · obtain ⟨fullPattern, patternId, originalDomain, authentic, alternatives⟩ := auxiliary
    exact Or.inr ⟨fullPattern, patternId, bodyId, originalDomain, bodyIdentity, authentic, alternatives⟩

end MicroCFTA.SourceCurrentNativeWarmAdmission


namespace MicroCFTA.SourceSynthesisCurrentUniverseNativeAllocation
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedBinderProtocol (NodeKey)
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceEqualityNativeDemand
open SourceCurrentAllocatedNativePhysicalTraceCompletion (Trace)
open SourceCurrentAllocatedNativePhysicalExecution (Inputs InputsThrough)
open SourceEqualityNativeDemandOperations (FieldsThrough)
open SourceSynthesisTypeSyntax (Library Query)
open SourceSynthesisFirstOrderConstruction (Expression)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSynthesisGeneralizeSyntax.Guard
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Profile" => SourceCurrentAllocatedNativeClosedResetProfile.Profile
local notation "ordinarySymbols" => SourceSynthesisUniverseCallerBoundary.ordinarySymbols
set_option autoImplicit false

/- Note [Admission after one actual cold prefix]
The old root starts with empty memo families. Its bounded prefix supplies
physical validity, heap growth and operation validity at the warm start.
Cold NoNewMu and the past inventory supply the new root Profiles there.
The new carrier keeps this complete start and the fixed new history.
No returned-value meaning is needed for query admission.
-/
theorem original_universe_next_warm_mu_query_prefix_admission
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
    (wholeCount queryUsed : Nat)
    (readerControl : Control (Value Symbol Guard)) (reader : Checked width)
    (queried : NodeRequest Symbol Guard)
    (queryNext : Value Symbol Guard → Code Symbol Guard (Value Symbol Guard))
    (queryBefore : Checked width)
    (wholeBound : wholeCount ≤ newFuel)
    (wholeActual : Trace wholeCount (.code (.node newRoot .pure))
      oldSnapshot readerControl reader)
    (queryBound : queryUsed ≤ wholeCount)
    (queryActual : Trace queryUsed (.code (.node newRoot .pure)) oldSnapshot
      (.code (.node queried queryNext)) queryBefore)
    (selectedMu :
      SourceRecursiveIntersectionControl.decision queried.domain.key queried.left queried.right = .bothMu ∨
      SourceRecursiveIntersectionControl.decision queried.domain.key queried.left queried.right = .leftMu ∨
      SourceRecursiveIntersectionControl.decision queried.domain.key queried.left queried.right = .rightMu) :
    SourceCurrentNativeWarmCMDefinitions.Qualified (width := width)
      newRoot oldSnapshot wholeCount entry body depth ordinary queried ∨
      ∃ (fullPattern : Value Symbol Guard) (patternId bodyId : Nat)
        (originalDomain : Interned IntersectionFlatMemoKeyDomain.DomainKey),
        SourceRecursiveIntersectionControl.identity body = some bodyId ∧
        SourceCurrentAllocatedNativeSourceWarmEntry.AuthenticEntryAt (width := width)
          newRoot oldSnapshot wholeCount entry body depth ordinary fullPattern patternId originalDomain ∧
        ((queried.domain.key = SourceRecursiveIntersectionDomain.extend originalDomain.key [entry.identity]
            (SourceRecursiveIntersectionControl.pair bodyId entry.identity) ∧
          queried.left = .mu entry body depth ordinary ∧
          queried.right = .reference (.interned entry.identity)) ∨
         (queried.domain.key = SourceRecursiveIntersectionDomain.extend originalDomain.key [entry.identity]
            (SourceRecursiveIntersectionControl.pair entry.identity entry.identity) ∧
          queried.left = body ∧ queried.right = .mu entry body depth ordinary)) := by
  let coldInitial : Checked width := ⟨initial width machine, operations⟩
  have coldPhysical : SourceCurrentAllocatedNativePhysicalCache.Valid (initial width machine) :=
    SourceCurrentAllocatedNativePhysicalCache.initial_valid machine machineValid
  have oldCurrent : Inputs (.code (.node oldRoot .pure)) coldInitial := by
    cases oldFuel with
    | zero => exact oldInputs
    | succ remaining => exact oldInputs.1
  have oldLeftAvailable : Available machine.heap oldRoot.left := oldCurrent.1.2.1
  have oldRightAvailable : Available machine.heap oldRoot.right := oldCurrent.1.2.2
  have oldLeftProfile : Profile entry.identity oldRoot.left :=
    ⟨oldRootClosed.1,
      SourceSynthesisCurrentUniverseStartupAtoms.current_stored_universe_closed_atoms_after_no_new_mu
        lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
        machine.heap machineValid.1.coherent pastInventory oldRoot.left oldLeftAvailable oldRootClosed.1⟩
  have oldRightProfile : Profile entry.identity oldRoot.right :=
    ⟨oldRootClosed.2,
      SourceSynthesisCurrentUniverseStartupAtoms.current_stored_universe_closed_atoms_after_no_new_mu
        lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
        machine.heap machineValid.1.coherent pastInventory oldRoot.right oldRightAvailable oldRootClosed.2⟩
  have oldOperations := SourceCurrentAllocatedNativePrefixOperations.prefix_operations_before_bind
    oldFuel oldCount (.code (.node oldRoot .pure)) oldControl .pure coldInitial oldSnapshot sourceHeap
    coldPhysical oldInputs oldFields operationsValid sourceGrowth
    (by simpa only [Control.bind_pure] using oldActual.steps) oldBound
  have coldInventory := original_universe_cold_query_no_new_mu
    lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
    oldRoot machine machineValid sourceGrowth oldRootDomain oldLeftProfile oldRightProfile
    operations operationsValid oldFuel oldInputs oldFields
  have warmInventory : InternedShallowHeap.NoNewMu sourceHeap oldSnapshot.native.machine.heap :=
    InternedShallowHeap.noNewMu_trans pastInventory
      (coldInventory.2 oldCount oldControl oldSnapshot oldBound oldActual)
  have newLeftProfile : Profile entry.identity newRoot.left :=
    ⟨newLeftClosed,
      SourceSynthesisCurrentUniverseStartupAtoms.current_stored_universe_closed_atoms_after_no_new_mu
        lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
        oldSnapshot.native.machine.heap oldOperations.2.1.machine.1.coherent warmInventory
        newRoot.left newLeftAvailable newLeftClosed⟩
  have newRightProfile : Profile entry.identity newRoot.right :=
    ⟨newRightClosed,
      SourceSynthesisCurrentUniverseStartupAtoms.current_stored_universe_closed_atoms_after_no_new_mu
        lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
        oldSnapshot.native.machine.heap oldOperations.2.1.machine.1.coherent warmInventory
        newRoot.right newRightAvailable newRightClosed⟩
  exact SourceCurrentNativeWarmAdmission.warm_mu_query_prefix_admission
    lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
    newRoot oldSnapshot oldOperations.2.1 oldOperations.2.2.2.1
    newRootDomain newLeftProfile newRightProfile oldOperations.2.2.2.2.1
    newFuel wholeCount queryUsed readerControl reader queried queryNext queryBefore
    wholeBound wholeActual queryBound queryActual selectedMu newInputs newFields

end MicroCFTA.SourceSynthesisCurrentUniverseNativeAllocation

namespace MicroCFTA.SourceCurrentNativeWarmAdmission
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedBinderProtocol (NodeKey)
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceEqualityNativeDemand
open SourceCurrentAllocatedNativeSourceWarmEntry (AuthenticEntryAt)
open SourceCurrentNativeWarmCMDefinitions (Qualified)
open SourceCurrentAllocatedNativePhysicalTraceCompletion (Trace)
open SourceCurrentAllocatedNativePhysicalExecution (InputsThrough)
open SourceEqualityNativeDemandOperations (FieldsThrough)
open SourceSynthesisTypeSyntax (Library Query)
open SourceSynthesisFirstOrderConstruction (Expression)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSynthesisGeneralizeSyntax.Guard
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Profile" => SourceCurrentAllocatedNativeClosedResetProfile.Profile
local notation "ordinarySymbols" => SourceSynthesisUniverseCallerBoundary.ordinarySymbols
set_option autoImplicit false

/- Note [Complete call admission from a retained start]
The actual start retains both memo tables and its physical state.
Past source inventory supplies closed root Profiles at this start.
The existing control carrier then follows the literal bounded prefix.
The node export retains all auxiliary alternatives in one entry bundle.
The edge export retains every ordered child pair and its actual domain.
No returned-value meaning or future inventory is an input.
-/
private theorem warm_source_control_prefix_full_admission
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
    (lib : Library) (query : Query) (signed : Int) (whole : Expression)
    (accepted : SourceSynthesisCurrentConstruction.firstOrderRaw lib query signed = .ok whole)
    (rootValue : Value Symbol Guard) (sourceHeap : InternedConstructorTemplates.State Symbol Guard)
    (built : InternedFreshOrdinaryConstruction.build (ordinarySymbols whole) [] empty =
      .done rootValue sourceHeap)
    (key : NodeKey) (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (stored : sourceHeap.nodeRecords key = some (.mu entry body depth ordinary))
    (rootRequest : NodeRequest Symbol Guard) (start : Checked width)
    (initialPhysical : SourceCurrentAllocatedNativePhysicalCache.Valid start.native)
    (sourceGrowth : Grows sourceHeap start.native.machine.heap)
    (pastInventory : InternedShallowHeap.NoNewMu sourceHeap start.native.machine.heap)
    (rootDomain : rootRequest.domain = IntersectionEmptyDomain.emptyDomain)
    (leftAvailable : Available start.native.machine.heap rootRequest.left)
    (rightAvailable : Available start.native.machine.heap rootRequest.right)
    (leftClosed : rootRequest.left.free = []) (rightClosed : rootRequest.right.free = [])
    (fuel wholeCount queryUsed : Nat)
    (wholeBound : wholeCount ≤ fuel)
    (inputs : InputsThrough fuel (.code (.node rootRequest .pure)) start)
    (fields : FieldsThrough fuel (.code (.node rootRequest .pure)) start)
    (control : Control (Value Symbol Guard)) (queryBefore : Checked width)
    (queryBound : queryUsed ≤ wholeCount)
    (queryActual : Trace queryUsed (.code (.node rootRequest .pure))
      start control queryBefore) :
    ∃ bodyId : Nat, SourceRecursiveIntersectionControl.identity body = some bodyId ∧
      ControlAdmission (width := width) rootRequest start wholeCount
        entry body depth ordinary bodyId control
 := by
  have _retainedPlans := And.intro wholeBound (And.intro inputs fields)
  have leftProfile : Profile entry.identity rootRequest.left :=
    ⟨leftClosed,
      SourceSynthesisCurrentUniverseStartupAtoms.current_stored_universe_closed_atoms_after_no_new_mu
        lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
        start.native.machine.heap initialPhysical.machine.1.coherent pastInventory
        rootRequest.left leftAvailable leftClosed⟩
  have rightProfile : Profile entry.identity rootRequest.right :=
    ⟨rightClosed,
      SourceSynthesisCurrentUniverseStartupAtoms.current_stored_universe_closed_atoms_after_no_new_mu
        lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
        start.native.machine.heap initialPhysical.machine.1.coherent pastInventory
        rootRequest.right rightAvailable rightClosed⟩
  have universeAvailable : Available start.native.machine.heap (.mu entry body depth ordinary) :=
    initialPhysical.machine.1.cached.nodes key _ (sourceGrowth.nodeRecords key _ stored)
  have universeAtoms : ∀ atom ∈ InternedBoundaryAtoms.atoms (.mu entry body depth ordinary),
      atom = .mu entry.identity := by
    intro atom occurrence
    simpa only [InternedBoundaryAtoms.atoms, List.mem_singleton] using occurrence
  have universeClosed : (Value.mu entry body depth ordinary).free = [] :=
    SourceSynthesisCurrentUniverseStartupAtoms.current_stored_universe_boundary_atoms_closed_after_growth
      lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
      start.native.machine.heap initialPhysical.machine.1 sourceGrowth (.mu entry body depth ordinary) universeAvailable universeAtoms
  have universeProfile : Profile entry.identity (.mu entry body depth ordinary) :=
    ⟨universeClosed, universeAtoms⟩
  obtain ⟨bodyEntry, bodyRows, bodyShape, matched⟩ :=
    SourceSynthesisCurrentUniverseBodyMatchedPairs.current_stored_universe_body_matching_pairs
      lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
      start.native.machine.heap initialPhysical.machine.1 sourceGrowth
  obtain ⟨classifiedEntry, marker, arrow, descriptors, classifiedShape, _bodyAvailable,
      _markerShape, _arrowChildren, _arrowKey, _catalog, _markerClosed, _markerAvailable,
      _markerAtoms, childKinds, _arrowRetained⟩ :=
    SourceSynthesisCurrentUniverseBodyChildClassification.current_stored_universe_body_physical_children_after_growth
      lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
      start.native.machine.heap initialPhysical.machine.1 sourceGrowth
  have sameRows : bodyRows = InternedConstructorTemplates.canonicalEdges (arrow :: descriptors) :=
    (Value.node.inj (bodyShape.symm.trans classifiedShape)).2.1
  have sourceChildren : ∀ row ∈ bodyRows, ∀ child ∈ row.children,
      child = .reference (.interned entry.identity) ∨ Profile entry.identity child := by
    intro row included child member
    rw [sameRows] at included
    rcases (childKinds row included).2.2 child member with reference | closed
    · exact Or.inl reference
    · obtain ⟨_sameMarker, _available, free, atomless⟩ := closed
      right
      refine ⟨free, ?_⟩
      intro atom occurrence
      rw [atomless] at occurrence
      cases occurrence
  let bodyId := bodyEntry.identity
  have bodyIdentity : SourceRecursiveIntersectionControl.identity body = some bodyId := by
    rw [bodyShape]
    rfl
  have initialAdmission : ControlAdmission (width := width) rootRequest start wholeCount
      entry body depth ordinary bodyId (.code (.node rootRequest .pure)) := by
    change NodeAdmission (width := width) rootRequest start wholeCount
      entry body depth ordinary bodyId rootRequest ∧ _
    exact ⟨Or.inl (Or.inl ⟨leftProfile, rightProfile, Or.inl rootDomain⟩), fun _ => True.intro⟩
  have reached := trace_admission rootRequest start initialPhysical wholeCount
    entry body depth ordinary bodyId lib query signed whole accepted rootValue sourceHeap built key stored
    sourceGrowth bodyEntry bodyRows bodyShape bodyIdentity sourceChildren matched universeProfile
    queryUsed 0 (.code (.node rootRequest .pure)) control
    start queryBefore (.refl _ _) queryActual
    (by simpa only [Nat.zero_add] using queryBound) initialAdmission
  exact ⟨bodyId, bodyIdentity, reached⟩

end MicroCFTA.SourceCurrentNativeWarmAdmission

namespace MicroCFTA.SourceSynthesisCurrentUniverseNativeAllocation
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedBinderProtocol (NodeKey)
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceEqualityNativeDemand
open SourceCurrentAllocatedNativeSourceWarmEntry (AuthenticEntryAt)
open SourceCurrentNativeWarmCMDefinitions (Qualified)
open SourceCurrentAllocatedNativePhysicalTraceCompletion (Trace)
open SourceCurrentAllocatedNativePhysicalExecution (InputsThrough)
open SourceEqualityNativeDemandOperations (FieldsThrough)
open SourceSynthesisTypeSyntax (Library Query)
open SourceSynthesisFirstOrderConstruction (Expression)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSynthesisGeneralizeSyntax.Guard
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Profile" => SourceCurrentAllocatedNativeClosedResetProfile.Profile
local notation "ordinarySymbols" => SourceSynthesisUniverseCallerBoundary.ordinarySymbols
set_option autoImplicit false


theorem original_universe_warm_node_query_prefix_full_admission
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
    (lib : Library) (query : Query) (signed : Int) (whole : Expression)
    (accepted : SourceSynthesisCurrentConstruction.firstOrderRaw lib query signed = .ok whole)
    (rootValue : Value Symbol Guard) (sourceHeap : InternedConstructorTemplates.State Symbol Guard)
    (built : InternedFreshOrdinaryConstruction.build (ordinarySymbols whole) [] empty =
      .done rootValue sourceHeap)
    (key : NodeKey) (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (stored : sourceHeap.nodeRecords key = some (.mu entry body depth ordinary))
    (rootRequest : NodeRequest Symbol Guard) (start : Checked width)
    (initialPhysical : SourceCurrentAllocatedNativePhysicalCache.Valid start.native)
    (sourceGrowth : Grows sourceHeap start.native.machine.heap)
    (pastInventory : InternedShallowHeap.NoNewMu sourceHeap start.native.machine.heap)
    (rootDomain : rootRequest.domain = IntersectionEmptyDomain.emptyDomain)
    (leftAvailable : Available start.native.machine.heap rootRequest.left)
    (rightAvailable : Available start.native.machine.heap rootRequest.right)
    (leftClosed : rootRequest.left.free = []) (rightClosed : rootRequest.right.free = [])
    (fuel wholeCount queryUsed : Nat)
    (wholeBound : wholeCount ≤ fuel)
    (inputs : InputsThrough fuel (.code (.node rootRequest .pure)) start)
    (fields : FieldsThrough fuel (.code (.node rootRequest .pure)) start)
    (queried : NodeRequest Symbol Guard)
    (queryNext : Value Symbol Guard → Code Symbol Guard (Value Symbol Guard))
    (queryBefore : Checked width)
    (queryBound : queryUsed ≤ wholeCount)
    (queryActual : Trace queryUsed (.code (.node rootRequest .pure))
      start
      (.code (.node queried queryNext)) queryBefore) :
    ∃ bodyId : Nat, SourceRecursiveIntersectionControl.identity body = some bodyId ∧
      (Qualified (width := width) rootRequest start wholeCount entry body depth ordinary queried ∨
        ∃ (fullPattern : Value Symbol Guard) (patternId : Nat)
          (originalDomain : Interned IntersectionFlatMemoKeyDomain.DomainKey),
          AuthenticEntryAt (width := width) rootRequest start wholeCount
            entry body depth ordinary fullPattern patternId originalDomain ∧
          let universeValue : Value Symbol Guard := .mu entry body depth ordinary
          let referenceValue : Value Symbol Guard := .reference (.interned entry.identity)
          let e := SourceRecursiveIntersectionControl.pair bodyId entry.identity
          let d := SourceRecursiveIntersectionControl.pair entry.identity entry.identity
          let bodyFirst := SourceRecursiveIntersectionDomain.extend originalDomain.key [entry.identity] e
          let diagonalFirst := SourceRecursiveIntersectionDomain.extend originalDomain.key [entry.identity] d
          let bodyTerminal := SourceRecursiveIntersectionDomain.extend bodyFirst [entry.identity] d
          let diagonalTerminal := SourceRecursiveIntersectionDomain.extend diagonalFirst [entry.identity] e
          (queried.domain.key = bodyFirst ∧
            ((queried.left = body ∧ queried.right = body) ∨
             (queried.left = referenceValue ∧ queried.right = referenceValue) ∨
             (queried.left = universeValue ∧ queried.right = referenceValue))) ∨
          (queried.domain.key = bodyTerminal ∧ queried.left = body ∧ queried.right = referenceValue) ∨
          (queried.domain.key = diagonalFirst ∧
            ((queried.left = body ∧ queried.right = referenceValue) ∨
             (queried.left = body ∧ queried.right = universeValue))) ∨
          (queried.domain.key = diagonalTerminal ∧
            ((queried.left = body ∧ queried.right = body) ∨
             (queried.left = referenceValue ∧ queried.right = referenceValue) ∨
             (queried.left = universeValue ∧ queried.right = referenceValue))))
 := by
  obtain ⟨bodyId, bodyIdentity, admitted⟩ :=
    SourceCurrentNativeWarmAdmission.warm_source_control_prefix_full_admission (width := width)
      lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
      rootRequest start initialPhysical sourceGrowth pastInventory rootDomain leftAvailable rightAvailable leftClosed rightClosed
      fuel wholeCount queryUsed wholeBound inputs fields
      (.code (.node queried queryNext)) queryBefore queryBound queryActual
  change SourceCurrentNativeWarmAdmission.NodeAdmission (width := width) rootRequest start wholeCount
    entry body depth ordinary bodyId queried ∧ _ at admitted
  exact ⟨bodyId, bodyIdentity, admitted.1⟩

theorem original_universe_warm_edge_query_prefix_full_admission
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
    (lib : Library) (query : Query) (signed : Int) (whole : Expression)
    (accepted : SourceSynthesisCurrentConstruction.firstOrderRaw lib query signed = .ok whole)
    (rootValue : Value Symbol Guard) (sourceHeap : InternedConstructorTemplates.State Symbol Guard)
    (built : InternedFreshOrdinaryConstruction.build (ordinarySymbols whole) [] empty =
      .done rootValue sourceHeap)
    (key : NodeKey) (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (stored : sourceHeap.nodeRecords key = some (.mu entry body depth ordinary))
    (rootRequest : NodeRequest Symbol Guard) (start : Checked width)
    (initialPhysical : SourceCurrentAllocatedNativePhysicalCache.Valid start.native)
    (sourceGrowth : Grows sourceHeap start.native.machine.heap)
    (pastInventory : InternedShallowHeap.NoNewMu sourceHeap start.native.machine.heap)
    (rootDomain : rootRequest.domain = IntersectionEmptyDomain.emptyDomain)
    (leftAvailable : Available start.native.machine.heap rootRequest.left)
    (rightAvailable : Available start.native.machine.heap rootRequest.right)
    (leftClosed : rootRequest.left.free = []) (rightClosed : rootRequest.right.free = [])
    (fuel wholeCount queryUsed : Nat)
    (wholeBound : wholeCount ≤ fuel)
    (inputs : InputsThrough fuel (.code (.node rootRequest .pure)) start)
    (fields : FieldsThrough fuel (.code (.node rootRequest .pure)) start)
    (queried : EdgeRequest Symbol Guard)
    (queryNext : EdgeValue Symbol Guard → Code Symbol Guard (Value Symbol Guard))
    (queryBefore : Checked width)
    (queryBound : queryUsed ≤ wholeCount)
    (queryActual : Trace queryUsed (.code (.node rootRequest .pure))
      start
      (.code (.edge queried queryNext)) queryBefore) :
    ∃ bodyId : Nat, SourceRecursiveIntersectionControl.identity body = some bodyId ∧
      (queried.left.children.length = queried.right.children.length →
        ∀ children ∈ queried.left.children.zip queried.right.children,
          let request : NodeRequest Symbol Guard := ⟨queried.domain, children.1, children.2⟩
          Qualified (width := width) rootRequest start wholeCount entry body depth ordinary request ∨
            ∃ (fullPattern : Value Symbol Guard) (patternId : Nat)
              (originalDomain : Interned IntersectionFlatMemoKeyDomain.DomainKey),
              AuthenticEntryAt (width := width) rootRequest start wholeCount
                entry body depth ordinary fullPattern patternId originalDomain ∧
              let universeValue : Value Symbol Guard := .mu entry body depth ordinary
              let referenceValue : Value Symbol Guard := .reference (.interned entry.identity)
              let e := SourceRecursiveIntersectionControl.pair bodyId entry.identity
              let d := SourceRecursiveIntersectionControl.pair entry.identity entry.identity
              let bodyFirst := SourceRecursiveIntersectionDomain.extend originalDomain.key [entry.identity] e
              let diagonalFirst := SourceRecursiveIntersectionDomain.extend originalDomain.key [entry.identity] d
              let bodyTerminal := SourceRecursiveIntersectionDomain.extend bodyFirst [entry.identity] d
              let diagonalTerminal := SourceRecursiveIntersectionDomain.extend diagonalFirst [entry.identity] e
              (request.domain.key = bodyFirst ∧
                ((request.left = body ∧ request.right = body) ∨
                 (request.left = referenceValue ∧ request.right = referenceValue) ∨
                 (request.left = universeValue ∧ request.right = referenceValue))) ∨
              (request.domain.key = bodyTerminal ∧ request.left = body ∧ request.right = referenceValue) ∨
              (request.domain.key = diagonalFirst ∧
                ((request.left = body ∧ request.right = referenceValue) ∨
                 (request.left = body ∧ request.right = universeValue))) ∨
              (request.domain.key = diagonalTerminal ∧
                ((request.left = body ∧ request.right = body) ∨
                 (request.left = referenceValue ∧ request.right = referenceValue) ∨
                 (request.left = universeValue ∧ request.right = referenceValue))))
 := by
  obtain ⟨bodyId, bodyIdentity, admitted⟩ :=
    SourceCurrentNativeWarmAdmission.warm_source_control_prefix_full_admission (width := width)
      lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
      rootRequest start initialPhysical sourceGrowth pastInventory rootDomain leftAvailable rightAvailable leftClosed rightClosed
      fuel wholeCount queryUsed wholeBound inputs fields
      (.code (.edge queried queryNext)) queryBefore queryBound queryActual
  change SourceCurrentNativeWarmAdmission.EdgeAdmission (width := width) rootRequest start wholeCount
    entry body depth ordinary bodyId queried ∧ _ at admitted
  exact ⟨bodyId, bodyIdentity, admitted.1⟩

end MicroCFTA.SourceSynthesisCurrentUniverseNativeAllocation
