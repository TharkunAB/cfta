import MicroCFTA.SourceCurrentAllocatedNativeSourceEmptyEnterOperands

namespace MicroCFTA.SourceCurrentAllocatedNativeSourceIssuedDomainEnterOrigin
open Cache InternedConstructorTemplates InternedBinderProtocol IntersectionFlatMemoKeyDomain
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceRecursiveIntersectionControl SourceRecursiveIntersectionDomain
open SourceEqualityNativeDemand
open SourceCurrentAllocatedNativePhysicalTraceCompletion (Trace)
open SourceCurrentAllocatedNativePhysicalExecution (Inputs)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Caller" => SourceCurrentAllocatedPartialState.State
variable {width : Nat} {A B : Type}
set_option autoImplicit false

private def Produced [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (root : Control A) (initial : Checked width) (wholeCount : Nat)
    (final : Control A) (reader : Checked width) (domain : Interned DomainKey) : Prop :=
  domain = IntersectionEmptyDomain.emptyDomain ∨
    ∃ (entryUsed : Nat) (beforeEntry : Checked width) (parent : Interned DomainKey)
      (left right : Value Symbol Guard) (first second : Nat)
      (next : Interned DomainKey → Code Symbol Guard A),
      let entered := SourceRecursiveIntersectionEnvironment.enter beforeEntry.native.machine.domains
        parent.key left right first second
      let started : Checked width :=
        {beforeEntry with native := advance beforeEntry.native {beforeEntry.native.machine with domains := entered.2}}
      entryUsed + 1 ≤ wholeCount ∧
      Trace entryUsed root initial (.code (.enter parent left right first second next)) beforeEntry ∧
      domain = entered.1 ∧
      Trace 1 (.code (.enter parent left right first second next)) beforeEntry
        (.code (next entered.1)) started ∧
      Trace (wholeCount - (entryUsed + 1)) (.code (next entered.1)) started final reader

variable {allowed : Interned DomainKey → Prop}

private def CodeDomains (allowed : Interned DomainKey → Prop) : Code Symbol Guard A → Prop
  | .pure _ | .fail _ => True
  | .work _ next | .read _ next | .optionalBinder _ _ next => ∀ value, CodeDomains allowed (next value)
  | .node request next => allowed request.domain ∧ ∀ value, CodeDomains allowed (next value)
  | .edge request next => allowed request.domain ∧ ∀ value, CodeDomains allowed (next value)
  | .enter domain _ _ _ _ next =>
      allowed domain ∧ ∀ entered, allowed entered → CodeDomains allowed (next entered)
  | .finishNode _ _ next | .finishEdge _ _ next => CodeDomains allowed next

private def ControlDomains (allowed : Interned DomainKey → Prop) : Control A → Prop
  | .code code => CodeDomains allowed code
  | .edgeBody request next => allowed request.domain ∧ ∀ value, CodeDomains allowed (next value)

private theorem origin_bind (code : Code Symbol Guard A) (next : A → Code Symbol Guard B)
    (original : CodeDomains allowed code) (continuation : ∀ value, CodeDomains allowed (next value)) :
    CodeDomains allowed (code.bind next) := by
  induction code with
  | pure value => exact continuation value
  | fail failure => trivial
  | work job resume ih | read name resume ih | optionalBinder key body resume ih =>
      intro value
      exact ih value (original value)
  | node request resume ih | edge request resume ih =>
      refine ⟨original.1, ?_⟩
      intro value
      exact ih value (original.2 value)
  | enter domain left right first second resume ih =>
      refine ⟨original.1, ?_⟩
      intro entered enteredOrigin
      exact ih entered (original.2 entered enteredOrigin)
  | finishNode handle value rest ih | finishEdge handle value rest ih => exact ih original

private theorem origin_walk (call : A → Code Symbol Guard B) (values : List A)
    (calls : ∀ value ∈ values, CodeDomains allowed (call value)) : CodeDomains allowed (walk call values) := by
  induction values with
  | nil => trivial
  | cons first rest ih =>
      apply origin_bind _ _ (calls first List.mem_cons_self)
      intro value
      apply origin_bind _ _ (ih (fun member present => calls member (List.mem_cons_of_mem _ present)))
      intro values
      trivial

private theorem mu_origin (domain : Interned DomainKey) (left right : Value Symbol Guard)
    (domainOrigin : allowed domain) : CodeDomains allowed (compileMu domain left right) := by
  unfold compileMu
  cases leftId : identity left with
  | none => trivial
  | some first =>
      cases rightId : identity right with
      | none => trivial
      | some second =>
          simp only [CodeDomains]
          refine ⟨domainOrigin, ?_⟩
          intro entered enteredOrigin
          exact ⟨enteredOrigin, fun _ _ => trivial⟩

private theorem reference_origin (domain : Interned DomainKey) (name : Nat)
    (other : Value Symbol Guard) (left : Bool) (domainOrigin : allowed domain) :
    CodeDomains allowed (compileReference domain name other left) := by
  by_cases member : name ∈ names domain.key
  · simp only [compileReference, member, ite_true, CodeDomains]
    intro found
    cases found with
    | none => trivial
    | some bound =>
        cases left <;> simp only [Bool.false_eq_true, ite_false, ite_true, requestNode, CodeDomains]
        all_goals exact ⟨domainOrigin, fun _ => trivial⟩
  · simp only [compileReference, member, ite_false, CodeDomains]

private theorem rows_origin [DecidableEq Symbol] (domain : Interned DomainKey)
    (left right : List (EdgeValue Symbol Guard)) (domainOrigin : allowed domain) :
    CodeDomains allowed (compileRows domain left right) := by
  apply origin_bind
  · exact origin_walk _ _ (fun _ _ => ⟨domainOrigin, fun _ => trivial⟩)
  · intro values value
    trivial

private theorem node_origin [DecidableEq Symbol]
    (emptyAllowed : allowed IntersectionEmptyDomain.emptyDomain) (request : NodeRequest Symbol Guard)
    (domainOrigin : allowed request.domain) : CodeDomains allowed (compileNode request) := by
  cases selected : decision request.domain.key request.left request.right with
  | empty | self | repeated key | unsupported =>
      simp only [compileNode, selected, SourceRecursiveIntersectionCode.unsupported, CodeDomains]
  | reset =>
      simp only [compileNode, selected]
      change CodeDomains allowed (requestNode IntersectionEmptyDomain.emptyDomain request.left request.right)
      exact ⟨emptyAllowed, fun _ => trivial⟩
  | swap =>
      simp only [compileNode, selected]
      change CodeDomains allowed (requestNode request.domain request.right request.left)
      exact ⟨domainOrigin, fun _ => trivial⟩
  | bothMu =>
      simpa only [compileNode, selected] using mu_origin request.domain request.left request.right
        domainOrigin
  | leftMu =>
      simpa only [compileNode, selected] using mu_origin request.domain request.left request.right
        domainOrigin
  | rightMu =>
      simpa only [compileNode, selected] using mu_origin request.domain request.left request.right
        domainOrigin
  | leftUnion =>
      simp only [compileNode, selected]
      cases request.left with
      | union entry members depth free =>
          apply origin_bind
          · exact origin_walk _ _ (fun _ _ => ⟨domainOrigin, fun _ => trivial⟩)
          · intro values value
            trivial
      | empty | reference | node | mu => trivial
  | rightUnion =>
      simp only [compileNode, selected]
      cases request.right with
      | union entry members depth free =>
          apply origin_bind
          · exact origin_walk _ _ (fun _ _ => ⟨domainOrigin, fun _ => trivial⟩)
          · intro values value
            trivial
      | empty | reference | node | mu => trivial
  | leftReference =>
      simp only [compileNode, selected]
      cases request.left <;> try trivial
      rename_i name
      cases name <;> first | exact reference_origin _ _ _ _ domainOrigin | trivial
  | rightReference =>
      simp only [compileNode, selected]
      cases request.right <;> try trivial
      rename_i name
      cases name <;> first | exact reference_origin _ _ _ _ domainOrigin | trivial
  | ordinary =>
      simp only [compileNode, selected]
      cases request.left <;> cases request.right <;>
        first | exact rows_origin _ _ _ domainOrigin | trivial

private theorem sentinel_origin (left : EdgeValue Symbol Guard) :
    CodeDomains allowed (SourceEqualityNativeCheckedCode.sentinel left) := by intro value; trivial

private theorem children_origin (request : EdgeRequest Symbol Guard)
    (combined : SourceEqualityConjoinAllocation.Constraint FullSyntax.Formula)
    (domainOrigin : allowed request.domain) :
    CodeDomains allowed (SourceEqualityNativeCheckedCode.children request.domain request.left request.right combined) := by
  apply origin_bind
  · exact origin_walk _ _ (fun _ _ => ⟨domainOrigin, fun _ => trivial⟩)
  · intro values value
    trivial

private theorem body_origin (request : EdgeRequest Symbol Guard)
    (next : EdgeValue Symbol Guard → Code Symbol Guard A) (state after : Checked width)
    (rest : Control A) (one : SourceEqualityNativeDemand.body request next state = .yielded rest after)
    (original : allowed request.domain ∧ ∀ value, CodeDomains allowed (next value)) : ControlDomains allowed rest := by
  unfold SourceEqualityNativeDemand.body at one
  split at one
  · cases one
    exact origin_bind _ _ (sentinel_origin _) original.2
  · split at one
    · cases one
    · cases one
    · split at one
      · cases one
      · cases one
      · dsimp only at one
        split at one
        · cases one
        · cases one
          exact origin_bind _ _ (sentinel_origin _) original.2
        · cases one
          exact origin_bind _ _ (sentinel_origin _) original.2
        · cases one
          exact origin_bind _ _ (children_origin _ _ original.1) original.2

private theorem step_origin [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (control rest : Control A) (before after : Checked width)
    (physical : SourceCurrentAllocatedNativePhysicalCache.Valid before.native)
    (emptyAllowed : allowed IntersectionEmptyDomain.emptyDomain)
    (enterAllowed : ∀ (domain : Interned DomainKey) (left right : Value Symbol Guard)
      (first second : Nat) (next : Interned DomainKey → Code Symbol Guard A),
      control = .code (.enter domain left right first second next) →
      allowed (SourceRecursiveIntersectionEnvironment.enter before.native.machine.domains
        domain.key left right first second).1)
    (inputs : Inputs control before) (one : step control before = .yielded rest after)
    (original : ControlDomains allowed control) : ControlDomains allowed rest := by
  cases control with
  | edgeBody request next => exact body_origin request next before after rest one original
  | code code =>
      change CodeDomains allowed code at original
      cases code with
      | pure value | fail failure =>
          simp only [step, SourceRecursiveIntersectionNative.step, lift] at one
          cases one
      | work job next =>
          simp only [step, SourceRecursiveIntersectionNative.step, lift] at one
          cases one
          exact original _
      | enter domain left right first second next =>
          simp only [step, SourceRecursiveIntersectionNative.step, lift] at one
          cases one
          exact original.2 _ (enterAllowed domain left right first second next rfl)
      | read name next =>
          simp only [step, SourceRecursiveIntersectionNative.step, lift] at one
          cases one
          exact original _
      | optionalBinder key value next =>
          simp only [step, SourceRecursiveIntersectionNative.step] at one
          cases produced : SourceRecursiveIntersectionMaybeMu.maybeMu key value before.native.machine.heap with
          | done result heap =>
              simp only [produced, lift] at one
              cases one
              exact original result
          | pending pending heap => simp only [produced, lift] at one; cases one
      | finishNode handle value next | finishEdge handle value next =>
          simp only [step, SourceRecursiveIntersectionNative.step, lift] at one
          cases one
          exact original
      | node request next =>
          simp only [step, SourceRecursiveIntersectionNative.step] at one
          cases selected : lookupNode width request before.native with
          | mk selection chosen =>
              cases selection with
              | direct actual =>
                  have same := (SourceRecursiveIntersectionNative.lookupNode_direct request actual before.native chosen selected).1
                  subst actual
                  simp only [selected, lift] at one
                  cases one
                  exact origin_bind _ _ (node_origin emptyAllowed request original.1) original.2
              | memoized handle =>
                  obtain ⟨key, requested, _, _⟩ :=
                    SourceRecursiveIntersectionNative.lookupNode_memoized request before.native chosen handle selected
                  cases demanded : demandNode handle chosen with
                  | mk demand running =>
                      cases demand with
                      | absent | busy => simp only [selected, demanded, lift] at one; cases one
                      | ready value =>
                          simp only [selected, demanded, lift] at one
                          cases one
                          exact original.2 value
                      | evaluate actual =>
                          have same := SourceCurrentAllocatedNativePhysicalCache.node_started request actual
                            before.native chosen running handle physical inputs.1 (inputs.2 key requested) selected demanded
                          subst actual
                          simp only [selected, demanded, lift] at one
                          cases one
                          exact origin_bind _ _ (node_origin emptyAllowed request original.1) (fun value => original.2 value)
      | edge request next =>
          simp only [step] at one
          cases selected : lookupEdge width request before.native with
          | mk handle chosen =>
              cases demanded : demandEdge handle chosen with
              | mk demand running =>
                  cases demand with
                  | absent | busy => simp only [selected, demanded] at one; cases one
                  | ready value =>
                      simp only [selected, demanded] at one
                      cases one
                      exact original.2 value
                  | evaluate actual =>
                      have same := SourceCurrentAllocatedNativePhysicalCache.edge_started request actual
                        before.native chosen running handle physical inputs.1 inputs.2 selected demanded
                      subst actual
                      simp only [selected, demanded] at one
                      cases one
                      exact ⟨original.1, fun value => original.2 value⟩

private theorem trace_domains [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (root : Control A) (initial : Checked width) (wholeCount : Nat)
    (final : Control A) (reader : Checked width)
    (count : Nat) (control : Control A) (before : Checked width) (prefixUsed : Nat)
    (prefixActual : Trace prefixUsed root initial control before)
    (actual : Trace count control before final reader)
    (counts : prefixUsed + count = wholeCount)
    (physical : SourceCurrentAllocatedNativePhysicalCache.Valid before.native)
    (original : ControlDomains (Produced root initial wholeCount final reader) control) :
    ControlDomains (Produced root initial wholeCount final reader) final := by
  induction count generalizing control before prefixUsed with
  | zero =>
      cases actual
      exact original
  | succ count ih =>
      cases actual with
      | cons control before middle reached final reader count inputs one tail =>
          have enterAllowed : ∀ (parent : Interned DomainKey) (left right : Value Symbol Guard)
              (first second : Nat) (next : Interned DomainKey → Code Symbol Guard A),
              control = .code (.enter parent left right first second next) →
              Produced root initial wholeCount final reader
                (SourceRecursiveIntersectionEnvironment.enter before.native.machine.domains
                  parent.key left right first second).1 := by
            intro parent left right first second next controlSame
            subst control
            let entered := SourceRecursiveIntersectionEnvironment.enter before.native.machine.domains
              parent.key left right first second
            let started : Checked width :=
              {before with native := advance before.native {before.native.machine with domains := entered.2}}
            have enterStep : step (.code (.enter parent left right first second next)) before =
                .yielded (.code (next entered.1)) started := rfl
            obtain ⟨middleSame, reachedSame⟩ := Outcome.yielded.inj (one.symm.trans enterStep)
            have rawTail : Trace count (.code (next entered.1)) started final reader := by
              simpa only [middleSame, reachedSame] using tail
            apply Or.inr
            refine ⟨prefixUsed, before, parent, left, right, first, second, next, ?_⟩
            dsimp only
            refine ⟨by omega, prefixActual, rfl, ?_, ?_⟩
            · exact Trace.cons _ _ _ _ _ _ 0 inputs enterStep (.refl _ _)
            · have remaining : wholeCount - (prefixUsed + 1) = count := by omega
              simpa only [remaining] using rawTail
          have reachedPhysical : SourceCurrentAllocatedNativePhysicalCache.Valid reached.native := by
            simpa only [one, Outcome.state] using
              SourceCurrentAllocatedNativePhysicalExecution.step_valid control before physical inputs
          have reachedOrigin := step_origin control middle before reached physical
            (Or.inl rfl : Produced root initial wholeCount final reader IntersectionEmptyDomain.emptyDomain)
            enterAllowed inputs one original
          have prefixNext : Trace (prefixUsed + 1) root initial middle reached :=
            prefixActual.trans (Trace.cons _ _ _ _ _ _ 0 inputs one (.refl _ _))
          exact ih middle reached (prefixUsed + 1) prefixNext tail (by omega) reachedPhysical reachedOrigin

theorem stored_dispatch_issued_domain_enter_origin
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (caller : Caller width) (cached : EnumerationExpandableIndex.Cached Symbol Guard)
    (valid : SourcePruningEnumerationNativeBranchCompletion.CacheValid caller cached)
    (source target sourceHandle targetHandle : Nat)
    (sourceScs targetScs : List EnumerationState.Suspended)
    (sourceStored : cached.core.values[source]? =
      some (.unenumerated (some sourceHandle) sourceScs))
    (targetStored : cached.core.values[target]? =
      some (.unenumerated (some targetHandle) targetScs))
    (rootRequest : NodeRequest Symbol Guard)
    (rootEmpty : rootRequest.domain = IntersectionEmptyDomain.emptyDomain)
    (sourceDecoded : SourcePruningEnumerationNodes.lookupNode
      caller.checked.native.machine.heap sourceHandle = some rootRequest.left)
    (targetDecoded : SourcePruningEnumerationNodes.lookupNode
      caller.checked.native.machine.heap targetHandle = some rootRequest.right)
    (physical : SourceCurrentAllocatedNativePhysicalCache.Valid caller.checked.native)
    (queryUsed : Nat) (request : NodeRequest Symbol Guard)
    (resume : Value Symbol Guard → Code Symbol Guard (Value Symbol Guard)) (queryBefore : Checked width)
    (issued : Trace queryUsed (.code (.node rootRequest .pure)) caller.checked
      (.code (.node request resume)) queryBefore)
    (uid patternId : Nat)
    (keyShape : request.domain.key = SourceRecursiveIntersectionDomain.extend
      IntersectionEmptyDomain.emptyKey [uid] (SourceRecursiveIntersectionControl.pair uid patternId)) :
    ∃ (entryUsed : Nat) (beforeEntry : Checked width) (left right : Value Symbol Guard)
      (first second : Nat) (next : Interned DomainKey → Code Symbol Guard (Value Symbol Guard)),
      let entered := SourceRecursiveIntersectionEnvironment.enter beforeEntry.native.machine.domains
        IntersectionEmptyDomain.emptyKey left right first second
      let started : Checked width :=
        {beforeEntry with native := advance beforeEntry.native {beforeEntry.native.machine with domains := entered.2}}
      entryUsed + 1 ≤ queryUsed ∧
      Trace entryUsed (.code (.node rootRequest .pure)) caller.checked
        (.code (.enter IntersectionEmptyDomain.emptyDomain left right first second next)) beforeEntry ∧
      request.domain = entered.1 ∧
      Trace 1 (.code (.enter IntersectionEmptyDomain.emptyDomain left right first second next))
        beforeEntry (.code (next entered.1)) started ∧
      Trace (queryUsed - (entryUsed + 1)) (.code (next entered.1)) started
        (.code (.node request resume)) queryBefore ∧
      left.free = [] ∧ right.free = [] ∧
      SourceRecursiveIntersectionControl.identity left = some first ∧
      SourceRecursiveIntersectionControl.identity right = some second ∧
      SourceRecursiveIntersectionControl.pair first second =
        SourceRecursiveIntersectionControl.pair uid patternId
 := by
  let allowed : Interned DomainKey → Prop := Produced (.code (.node rootRequest .pure))
    caller.checked queryUsed (.code (.node request resume)) queryBefore
  have original : ControlDomains allowed (.code (.node rootRequest .pure)) := by
    refine ⟨?_, fun _ => trivial⟩
    change Produced (.code (.node rootRequest .pure)) caller.checked queryUsed
      (.code (.node request resume)) queryBefore rootRequest.domain
    exact Or.inl rootEmpty
  have reached : ControlDomains allowed (.code (.node request resume)) :=
    trace_domains (.code (.node rootRequest .pure)) caller.checked queryUsed
      (.code (.node request resume)) queryBefore queryUsed
      (.code (.node rootRequest .pure)) caller.checked 0 (.refl _ _) issued (by omega) physical original
  have origin : Produced (.code (.node rootRequest .pure)) caller.checked queryUsed
      (.code (.node request resume)) queryBefore request.domain := reached.1
  have nonempty : request.domain ≠ IntersectionEmptyDomain.emptyDomain := by
    intro empty
    have member : SourceRecursiveIntersectionControl.pair uid patternId ∈ request.domain.key.seen := by
      rw [keyShape]
      exact (SourceRecursiveIntersectionDomain.extend_seen _ _ _ _).mpr (Or.inl rfl)
    rw [empty] at member
    cases member
  rcases origin with empty | origin
  · exact False.elim (nonempty empty)
  · obtain ⟨entryUsed, beforeEntry, parent, left, right, first, second, next,
      bounded, prefixActual, domainSame, entryActual, suffixActual⟩ := origin
    have sameKey : (SourceRecursiveIntersectionEnvironment.enter beforeEntry.native.machine.domains
        parent.key left right first second).1.key = SourceRecursiveIntersectionDomain.extend
          IntersectionEmptyDomain.emptyKey [uid] (SourceRecursiveIntersectionControl.pair uid patternId) :=
      (congrArg (fun domain : Interned DomainKey => domain.key) domainSame).symm.trans keyShape
    have ancestry := SourceCurrentAllocatedNativeEmptyRootDomainAncestry.empty_root_singleton_enter_parent
      rootRequest caller.checked beforeEntry physical rootEmpty entryUsed parent left right first second
      uid patternId next prefixActual sameKey
    have closed := SourceCurrentAllocatedNativeSourceEmptyEnterOperands.stored_dispatch_enter_closed_operands
      caller cached valid source target sourceHandle targetHandle sourceScs targetScs sourceStored targetStored
      rootRequest rootEmpty sourceDecoded targetDecoded physical entryUsed beforeEntry parent left right
      first second uid patternId next prefixActual sameKey
    have identities := SourceCurrentAllocatedNativeSourceEmptyEnterOperands.stored_dispatch_enter_identities
      caller cached valid source target sourceHandle targetHandle sourceScs targetScs sourceStored targetStored
      rootRequest sourceDecoded targetDecoded physical entryUsed beforeEntry parent left right first second
      next prefixActual
    have parentDomain : Domain beforeEntry.native.machine parent := by
      cases entryActual with
      | cons control state middle reached final reader count inputs one tail => exact inputs.1
    have parentIdentity : parent.identity = 0 := by
      simpa only [ancestry.1, ite_true] using parentDomain.represented.2
    have parentEmpty : parent = IntersectionEmptyDomain.emptyDomain := by
      have same : parent = Interned.mk 0 parent.key :=
        congrArg (fun identifier => Interned.mk identifier parent.key) parentIdentity
      rw [ancestry.1] at same
      exact same
    refine ⟨entryUsed, beforeEntry, left, right, first, second, next, ?_⟩
    dsimp only
    refine ⟨bounded, ?_, ?_, ?_, ?_, closed.2.1, closed.2.2.1, identities.1, identities.2, ancestry.2⟩
    · simpa only [parentEmpty] using prefixActual
    · simpa only [parentEmpty, IntersectionEmptyDomain.emptyDomain] using domainSame
    · simpa only [parentEmpty, IntersectionEmptyDomain.emptyDomain] using entryActual
    · simpa only [parentEmpty, IntersectionEmptyDomain.emptyDomain] using suffixActual

end MicroCFTA.SourceCurrentAllocatedNativeSourceIssuedDomainEnterOrigin

namespace MicroCFTA.SourceCurrentAllocatedNativeSourceIssuedDomainEnterOrigin
open Cache InternedConstructorTemplates InternedBinderProtocol IntersectionFlatMemoKeyDomain
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceRecursiveIntersectionControl SourceRecursiveIntersectionDomain
open SourceEqualityNativeDemand
open SourceCurrentAllocatedNativePhysicalTraceCompletion (Trace)
open SourceCurrentAllocatedNativePhysicalExecution (Inputs)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Caller" => SourceCurrentAllocatedPartialState.State
variable {width : Nat} {A B : Type}
set_option autoImplicit false

theorem stored_dispatch_issued_edge_domain_enter_origin
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (caller : Caller width) (cached : EnumerationExpandableIndex.Cached Symbol Guard)
    (valid : SourcePruningEnumerationNativeBranchCompletion.CacheValid caller cached)
    (source target sourceHandle targetHandle : Nat)
    (sourceScs targetScs : List EnumerationState.Suspended)
    (sourceStored : cached.core.values[source]? =
      some (.unenumerated (some sourceHandle) sourceScs))
    (targetStored : cached.core.values[target]? =
      some (.unenumerated (some targetHandle) targetScs))
    (rootRequest : NodeRequest Symbol Guard)
    (rootEmpty : rootRequest.domain = IntersectionEmptyDomain.emptyDomain)
    (sourceDecoded : SourcePruningEnumerationNodes.lookupNode
      caller.checked.native.machine.heap sourceHandle = some rootRequest.left)
    (targetDecoded : SourcePruningEnumerationNodes.lookupNode
      caller.checked.native.machine.heap targetHandle = some rootRequest.right)
    (physical : SourceCurrentAllocatedNativePhysicalCache.Valid caller.checked.native)
    (queryUsed : Nat) (request : EdgeRequest Symbol Guard)
    (resume : EdgeValue Symbol Guard → Code Symbol Guard (Value Symbol Guard)) (queryBefore : Checked width)
    (issued : Trace queryUsed (.code (.node rootRequest .pure)) caller.checked
      (.code (.edge request resume)) queryBefore)
    (uid patternId : Nat)
    (keyShape : request.domain.key = SourceRecursiveIntersectionDomain.extend
      IntersectionEmptyDomain.emptyKey [uid] (SourceRecursiveIntersectionControl.pair uid patternId)) :
    ∃ (entryUsed : Nat) (beforeEntry : Checked width) (left right : Value Symbol Guard)
      (first second : Nat) (next : Interned DomainKey → Code Symbol Guard (Value Symbol Guard)),
      let entered := SourceRecursiveIntersectionEnvironment.enter beforeEntry.native.machine.domains
        IntersectionEmptyDomain.emptyKey left right first second
      let started : Checked width :=
        {beforeEntry with native := advance beforeEntry.native {beforeEntry.native.machine with domains := entered.2}}
      entryUsed + 1 ≤ queryUsed ∧
      Trace entryUsed (.code (.node rootRequest .pure)) caller.checked
        (.code (.enter IntersectionEmptyDomain.emptyDomain left right first second next)) beforeEntry ∧
      request.domain = entered.1 ∧
      Trace 1 (.code (.enter IntersectionEmptyDomain.emptyDomain left right first second next))
        beforeEntry (.code (next entered.1)) started ∧
      Trace (queryUsed - (entryUsed + 1)) (.code (next entered.1)) started
        (.code (.edge request resume)) queryBefore ∧
      left.free = [] ∧ right.free = [] ∧
      SourceRecursiveIntersectionControl.identity left = some first ∧
      SourceRecursiveIntersectionControl.identity right = some second ∧
      SourceRecursiveIntersectionControl.pair first second =
        SourceRecursiveIntersectionControl.pair uid patternId

 := by
  let allowed : Interned DomainKey → Prop := Produced (.code (.node rootRequest .pure))
    caller.checked queryUsed (.code (.edge request resume)) queryBefore
  have original : ControlDomains allowed (.code (.node rootRequest .pure)) := by
    refine ⟨?_, fun _ => trivial⟩
    change Produced (.code (.node rootRequest .pure)) caller.checked queryUsed
      (.code (.edge request resume)) queryBefore rootRequest.domain
    exact Or.inl rootEmpty
  have reached : ControlDomains allowed (.code (.edge request resume)) :=
    trace_domains (.code (.node rootRequest .pure)) caller.checked queryUsed
      (.code (.edge request resume)) queryBefore queryUsed
      (.code (.node rootRequest .pure)) caller.checked 0 (.refl _ _) issued (by omega) physical original
  have origin : Produced (.code (.node rootRequest .pure)) caller.checked queryUsed
      (.code (.edge request resume)) queryBefore request.domain := reached.1
  have nonempty : request.domain ≠ IntersectionEmptyDomain.emptyDomain := by
    intro empty
    have member : SourceRecursiveIntersectionControl.pair uid patternId ∈ request.domain.key.seen := by
      rw [keyShape]
      exact (SourceRecursiveIntersectionDomain.extend_seen _ _ _ _).mpr (Or.inl rfl)
    rw [empty] at member
    cases member
  rcases origin with empty | origin
  · exact False.elim (nonempty empty)
  · obtain ⟨entryUsed, beforeEntry, parent, left, right, first, second, next,
      bounded, prefixActual, domainSame, entryActual, suffixActual⟩ := origin
    have sameKey : (SourceRecursiveIntersectionEnvironment.enter beforeEntry.native.machine.domains
        parent.key left right first second).1.key = SourceRecursiveIntersectionDomain.extend
          IntersectionEmptyDomain.emptyKey [uid] (SourceRecursiveIntersectionControl.pair uid patternId) :=
      (congrArg (fun domain : Interned DomainKey => domain.key) domainSame).symm.trans keyShape
    have ancestry := SourceCurrentAllocatedNativeEmptyRootDomainAncestry.empty_root_singleton_enter_parent
      rootRequest caller.checked beforeEntry physical rootEmpty entryUsed parent left right first second
      uid patternId next prefixActual sameKey
    have closed := SourceCurrentAllocatedNativeSourceEmptyEnterOperands.stored_dispatch_enter_closed_operands
      caller cached valid source target sourceHandle targetHandle sourceScs targetScs sourceStored targetStored
      rootRequest rootEmpty sourceDecoded targetDecoded physical entryUsed beforeEntry parent left right
      first second uid patternId next prefixActual sameKey
    have identities := SourceCurrentAllocatedNativeSourceEmptyEnterOperands.stored_dispatch_enter_identities
      caller cached valid source target sourceHandle targetHandle sourceScs targetScs sourceStored targetStored
      rootRequest sourceDecoded targetDecoded physical entryUsed beforeEntry parent left right first second
      next prefixActual
    have parentDomain : Domain beforeEntry.native.machine parent := by
      cases entryActual with
      | cons control state middle reached final reader count inputs one tail => exact inputs.1
    have parentIdentity : parent.identity = 0 := by
      simpa only [ancestry.1, ite_true] using parentDomain.represented.2
    have parentEmpty : parent = IntersectionEmptyDomain.emptyDomain := by
      have same : parent = Interned.mk 0 parent.key :=
        congrArg (fun identifier => Interned.mk identifier parent.key) parentIdentity
      rw [ancestry.1] at same
      exact same
    refine ⟨entryUsed, beforeEntry, left, right, first, second, next, ?_⟩
    dsimp only
    refine ⟨bounded, ?_, ?_, ?_, ?_, closed.2.1, closed.2.2.1, identities.1, identities.2, ancestry.2⟩
    · simpa only [parentEmpty] using prefixActual
    · simpa only [parentEmpty, IntersectionEmptyDomain.emptyDomain] using domainSame
    · simpa only [parentEmpty, IntersectionEmptyDomain.emptyDomain] using entryActual
    · simpa only [parentEmpty, IntersectionEmptyDomain.emptyDomain] using suffixActual

end MicroCFTA.SourceCurrentAllocatedNativeSourceIssuedDomainEnterOrigin

namespace MicroCFTA.SourceCurrentAllocatedNativeSourceIssuedDomainEnterOrigin
open Cache InternedConstructorTemplates InternedBinderProtocol IntersectionFlatMemoKeyDomain
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceRecursiveIntersectionControl SourceRecursiveIntersectionDomain
open SourceEqualityNativeDemand
open SourceCurrentAllocatedNativePhysicalTraceCompletion (Trace)
open SourceCurrentAllocatedNativePhysicalExecution (Inputs)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Caller" => SourceCurrentAllocatedPartialState.State
variable {width : Nat} {A B : Type}
set_option autoImplicit false

/- Note [Closed-root warm entry]
The actual staged incoming operand need not have a pending-slot lookup.
Its actual source receipt supplies closed root operands. Reuse the original
entry proof at the same Checked start. Keep all counts, controls, domains,
continuations, and readers. This is physical provenance for an authentic entry.
It does not classify an inherited payload or prove a semantic result law.
-/

theorem closed_root_issued_domain_enter_origin
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (before : Checked width) (rootRequest : NodeRequest Symbol Guard)
    (rootEmpty : rootRequest.domain = IntersectionEmptyDomain.emptyDomain)
    (rootClosed : rootRequest.left.free = [] ∧ rootRequest.right.free = [])
    (physical : SourceCurrentAllocatedNativePhysicalCache.Valid before.native)
    (queryUsed : Nat) (request : NodeRequest Symbol Guard)
    (resume : Value Symbol Guard → Code Symbol Guard (Value Symbol Guard)) (queryBefore : Checked width)
    (issued : Trace queryUsed (.code (.node rootRequest .pure)) before
      (.code (.node request resume)) queryBefore)
    (uid patternId : Nat)
    (keyShape : request.domain.key = SourceRecursiveIntersectionDomain.extend
      IntersectionEmptyDomain.emptyKey [uid] (SourceRecursiveIntersectionControl.pair uid patternId)) :
    ∃ (entryUsed : Nat) (beforeEntry : Checked width) (left right : Value Symbol Guard)
      (first second : Nat) (next : Interned DomainKey → Code Symbol Guard (Value Symbol Guard)),
      let entered := SourceRecursiveIntersectionEnvironment.enter beforeEntry.native.machine.domains
        IntersectionEmptyDomain.emptyKey left right first second
      let started : Checked width :=
        {beforeEntry with native := advance beforeEntry.native {beforeEntry.native.machine with domains := entered.2}}
      entryUsed + 1 ≤ queryUsed ∧
      Trace entryUsed (.code (.node rootRequest .pure)) before
        (.code (.enter IntersectionEmptyDomain.emptyDomain left right first second next)) beforeEntry ∧
      request.domain = entered.1 ∧
      Trace 1 (.code (.enter IntersectionEmptyDomain.emptyDomain left right first second next))
        beforeEntry (.code (next entered.1)) started ∧
      Trace (queryUsed - (entryUsed + 1)) (.code (next entered.1)) started
        (.code (.node request resume)) queryBefore ∧
      left.free = [] ∧ right.free = [] ∧
      SourceRecursiveIntersectionControl.identity left = some first ∧
      SourceRecursiveIntersectionControl.identity right = some second ∧
      SourceRecursiveIntersectionControl.pair first second =
        SourceRecursiveIntersectionControl.pair uid patternId := by
  let allowed : Interned DomainKey → Prop := Produced (.code (.node rootRequest .pure))
    before queryUsed (.code (.node request resume)) queryBefore
  have original : ControlDomains allowed (.code (.node rootRequest .pure)) := by
    refine ⟨?_, fun _ => trivial⟩
    change Produced (.code (.node rootRequest .pure)) before queryUsed
      (.code (.node request resume)) queryBefore rootRequest.domain
    exact Or.inl rootEmpty
  have reached : ControlDomains allowed (.code (.node request resume)) :=
    trace_domains (.code (.node rootRequest .pure)) before queryUsed
      (.code (.node request resume)) queryBefore queryUsed
      (.code (.node rootRequest .pure)) before 0 (.refl _ _) issued (by omega) physical original
  have origin : Produced (.code (.node rootRequest .pure)) before queryUsed
      (.code (.node request resume)) queryBefore request.domain := reached.1
  have nonempty : request.domain ≠ IntersectionEmptyDomain.emptyDomain := by
    intro empty
    have member : SourceRecursiveIntersectionControl.pair uid patternId ∈ request.domain.key.seen := by
      rw [keyShape]
      exact (SourceRecursiveIntersectionDomain.extend_seen _ _ _ _).mpr (Or.inl rfl)
    rw [empty] at member
    cases member
  rcases origin with empty | origin
  · exact False.elim (nonempty empty)
  · obtain ⟨entryUsed, beforeEntry, parent, left, right, first, second, next,
      bounded, prefixActual, domainSame, entryActual, suffixActual⟩ := origin
    have sameKey : (SourceRecursiveIntersectionEnvironment.enter beforeEntry.native.machine.domains
        parent.key left right first second).1.key = SourceRecursiveIntersectionDomain.extend
          IntersectionEmptyDomain.emptyKey [uid] (SourceRecursiveIntersectionControl.pair uid patternId) :=
      (congrArg (fun domain : Interned DomainKey => domain.key) domainSame).symm.trans keyShape
    have ancestry := SourceCurrentAllocatedNativeEmptyRootDomainAncestry.empty_root_singleton_enter_parent
      rootRequest before beforeEntry physical rootEmpty entryUsed parent left right first second
      uid patternId next prefixActual sameKey
    have closed := SourceCurrentAllocatedNativeSourceEmptyEnterOperands.query_enter_closed_operands_of_closed_root
      before rootRequest rootEmpty rootClosed physical entryUsed beforeEntry parent left right
      first second uid patternId next prefixActual sameKey
    have identities := SourceCurrentAllocatedNativeSourceEmptyEnterOperands.closed_root_enter_identities
      before rootRequest rootClosed physical entryUsed beforeEntry parent left right first second
      next prefixActual
    have parentDomain : Domain beforeEntry.native.machine parent := by
      cases entryActual with
      | cons control state middle reached final reader count inputs one tail => exact inputs.1
    have parentIdentity : parent.identity = 0 := by
      simpa only [ancestry.1, ite_true] using parentDomain.represented.2
    have parentEmpty : parent = IntersectionEmptyDomain.emptyDomain := by
      have same : parent = Interned.mk 0 parent.key :=
        congrArg (fun identifier => Interned.mk identifier parent.key) parentIdentity
      rw [ancestry.1] at same
      exact same
    refine ⟨entryUsed, beforeEntry, left, right, first, second, next, ?_⟩
    dsimp only
    refine ⟨bounded, ?_, ?_, ?_, ?_, closed.2.1, closed.2.2.1, identities.1, identities.2, ancestry.2⟩
    · simpa only [parentEmpty] using prefixActual
    · simpa only [parentEmpty, IntersectionEmptyDomain.emptyDomain] using domainSame
    · simpa only [parentEmpty, IntersectionEmptyDomain.emptyDomain] using entryActual
    · simpa only [parentEmpty, IntersectionEmptyDomain.emptyDomain] using suffixActual

end MicroCFTA.SourceCurrentAllocatedNativeSourceIssuedDomainEnterOrigin
