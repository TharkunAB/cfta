import MicroCFTA.SourceCurrentCausalSourceComparison
import MicroCFTA.SourceRecursiveIntersectionSemanticHeap

set_option linter.all true
set_option maxRecDepth 30000
set_option maxHeartbeats 5000000
set_option cbv.maxSteps 100000000

namespace MicroCFTA.CausalSourceIntegration
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedConstruction (Syntax Outcome)
open InternedFreshOrdinaryConstruction (build)
open InternedFreshOrdinaryLiveInputs (input)
open InternedBinderProtocol (Reference)
open InternedRootProfile (Profile Equivalent)
open SourceCurrentConstrainedCapSourceHistory (Context)
open SourceCurrentNativeMuPublication (History)
open SourceCurrentStoredRootDeletion (deleted)
open SourceCurrentStoredMuProfileContract (Correct)
open SourceCurrentPublicationHeapInduction (Heap)

private def body (used : Bool) : Syntax Nat Bool :=
  if used then .node [.mk 7 false [.var 0,.binder true (.node [.mk 8 true [.var 0,.var 2]])]]
  else .union [.var 0,.binder true (.var 2)]
private def expression (smart used : Bool) : Syntax Nat Bool := .binder smart (body used)
private def captures (name : Nat) : List (Value Nat Bool) := [.reference (.uninterned name)]
private def result (call : Outcome Nat Bool (Value Nat Bool)) : Value Nat Bool :=
  match call with | .done value _ => value | .pending .. => .empty
private def leftCall (smart used : Bool) := build (expression smart used) (captures 10) empty
private def leftValue (smart used : Bool) := result (leftCall smart used)
private def leftAfter (smart used : Bool) := (leftCall smart used).state
private def rightCall (smart used : Bool) := build (expression smart used) (captures 20) (leftAfter smart used)
private def rightValue (smart used : Bool) := result (rightCall smart used)
private def rightAfter (smart used : Bool) := (rightCall smart used).state
private def firstBefore (smart used warm : Bool) := if warm then rightAfter smart used else empty
private def firstAfter (smart used warm : Bool) := if warm then rightAfter smart used else leftAfter smart used
private def extension : Syntax Nat Bool := .node [.mk 99 false []]
private def extensionCall (smart used : Bool) := build extension [] (rightAfter smart used)
private def common (smart used : Bool) := (extensionCall smart used).state
private def isMu (value : Value Nat Bool) : Bool := match value with | .mu .. => true | _ => false
private def isUsed (value : Value Nat Bool) : Bool :=
  match value with | .mu _ _ depth ordinary => InternedFreshOrdinaryDepthHeap.usesLocal depth ordinary | _ => false

private theorem left_done (smart used warm : Bool) :
    build (expression smart used) (captures 10) (firstBefore smart used warm) =
      .done (leftValue smart used) (firstAfter smart used warm) := by
  cases smart <;> cases used <;> cases warm <;> cbv
private theorem right_done (smart used warm : Bool) :
    build (expression smart used) (captures 20) (firstAfter smart used warm) =
      .done (rightValue smart used) (rightAfter smart used) := by
  cases smart <;> cases used <;> cases warm <;> cbv
private theorem extension_done (smart used : Bool) :
    build extension [] (rightAfter smart used) = .done (result (extensionCall smart used)) (common smart used) := by
  cases smart <;> cases used <;> cbv
private theorem output_shape (smart used : Bool) :
    leftValue smart used ≠ rightValue smart used ∧
    isMu (leftValue smart used) = (used || !smart) ∧
    isMu (rightValue smart used) = (used || !smart) ∧
    isUsed (leftValue smart used) = used ∧ isUsed (rightValue smart used) = used ∧
    (leftValue smart used).free ≠ [] ∧ (rightValue smart used).free ≠ [] ∧
    (smart = true → used = false → leftValue smart used = .reference (.uninterned 10) ∧
      rightValue smart used = .reference (.uninterned 20)) := by
  cases smart <;> cases used <;> cbv <;> simp
private theorem allocation (smart used : Bool) :
    (common smart used).nodes.next = (rightAfter smart used).nodes.next + 1 := by
  cases smart <;> cases used <;> cbv

private theorem captures_available (name : Nat) (state : State Nat Bool) :
    InternedNestedProvenance.Values state (captures name) := by
  intro value member
  have same : value = .reference (.uninterned name) := by simpa only [captures,List.mem_singleton] using member
  cases same
  exact InternedNestedProvenance.ordinary_available state _
private theorem initial_context (name : Nat) : Context empty (captures name) :=
  ⟨SourceRecursiveIntersectionSemanticHeap.context empty SourceRecursiveIntersectionSemanticHeap.empty_heap
    (captures name) (captures_available name empty),InternedFreshOrdinaryDepthHeap.empty_heap⟩
private theorem recapture (name : Nat) {state : State Nat Bool} {environment : List (Value Nat Bool)}
    (context : Context state environment) : Context state (captures name) :=
  ⟨⟨context.base.normal,captures_available name state,context.base.profiles,context.base.freeNames⟩,context.depth⟩
private theorem left_context (smart used : Bool) : Context (leftAfter smart used) (captures 10) :=
  (initial_context 10).build (expression smart used)
private theorem right_context (smart used : Bool) : Context (rightAfter smart used) (captures 20) :=
  (recapture 20 (left_context smart used)).build (expression smart used)
private theorem first_context (smart used warm : Bool) : Context (firstBefore smart used warm) (captures 10) := by
  cases warm with
  | false => exact initial_context 10
  | true => exact recapture 10 (right_context smart used)
private theorem second_context (smart used warm : Bool) : Context (firstAfter smart used warm) (captures 20) := by
  cases warm with
  | false => exact recapture 20 (left_context smart used)
  | true => exact right_context smart used
private theorem left_history (smart used : Bool) : Nonempty (History empty (leftAfter smart used)) :=
  SourceCurrentNativeMuPublication.build_history (expression smart used) (captures 10) empty (initial_context 10)
private theorem right_history (smart used : Bool) : Nonempty (History empty (rightAfter smart used)) := by
  obtain ⟨left⟩ := left_history smart used
  obtain ⟨right⟩ := SourceCurrentNativeMuPublication.build_history (expression smart used) (captures 20)
    (leftAfter smart used) (recapture 20 (left_context smart used))
  exact ⟨.trans left right⟩
private theorem extension_context (smart used : Bool) : Context (rightAfter smart used) [] :=
  ⟨⟨(right_context smart used).base.normal,(by intro value member; cases member),
    (right_context smart used).base.profiles,(right_context smart used).base.freeNames⟩,(right_context smart used).depth⟩
private theorem common_history (smart used : Bool) : Nonempty (History empty (common smart used)) := by
  obtain ⟨earlier⟩ := right_history smart used
  obtain ⟨last⟩ := SourceCurrentNativeMuPublication.build_history extension [] (rightAfter smart used) (extension_context smart used)
  exact ⟨.trans earlier last⟩
private theorem right_heap (smart used : Bool) : Heap Correct (rightAfter smart used) := by
  have left := SourceCurrentCausalSourceComparison.build_heap (expression smart used) (captures 10) empty
    (initial_context 10) (.refl empty) (SourceCurrentPublicationHeapInduction.empty Correct)
  obtain ⟨history⟩ := left_history smart used
  exact SourceCurrentCausalSourceComparison.build_heap (expression smart used) (captures 20) (leftAfter smart used)
    (recapture 20 (left_context smart used)) history left
private theorem common_heap (smart used : Bool) : Heap Correct (common smart used) := by
  obtain ⟨history⟩ := right_history smart used
  exact SourceCurrentCausalSourceComparison.build_heap extension [] (rightAfter smart used)
    (extension_context smart used) history (right_heap smart used)
private theorem right_growth (smart used : Bool) : Grows (leftAfter smart used) (rightAfter smart used) :=
  (InternedFreshOrdinaryFacts.build_verified (expression smart used) (captures 20) (leftAfter smart used)
    (recapture 20 (left_context smart used)).base.normal.facts (captures_available 20 _)).growth
private theorem later (smart used : Bool) : Grows (rightAfter smart used) (common smart used) :=
  (InternedFreshOrdinaryFacts.build_verified extension [] (rightAfter smart used)
    (extension_context smart used).base.normal.facts (by intro value member; cases member)).growth
private theorem first_growth (smart used warm : Bool) : Grows (firstAfter smart used warm) (common smart used) := by
  cases warm with
  | false => exact grows_trans (right_growth smart used) (later smart used)
  | true => exact later smart used

private def symbolic : List (Sum (Value Nat Bool) Unit) := [.inr ()]
private def firstNames : Unit → Reference := fun _ => .uninterned 10
private def secondNames : Unit → Reference := fun _ => .uninterned 20
private theorem support (smart used : Bool) :
    SourceCurrentNativeNormalizationInputs.support (expression smart used) symbolic = [.inr ()] := by
  cases smart <;> cases used <;> cbv
private theorem aliases (smart used : Bool) :
    SourceCurrentUsedBinderAliasTransport.Aliases (expression smart used) symbolic firstNames secondNames := by
  intro first firstMember second secondMember
  simp only [SourceCurrentUsedBinderAliasTransport.Scope,support,List.mem_cons,List.not_mem_nil,or_false] at firstMember secondMember
  rcases firstMember with rfl | rfl <;> rcases secondMember with rfl | rfl <;> cbv
private theorem profile_inputs (smart used : Bool) (first second : Reference → Profile)
    (same : first (.uninterned 10) = second (.uninterned 20)) :
    SourceCurrentScopedProfileInputs.Compatible (expression smart used) symbolic firstNames secondNames first second := by
  constructor
  · intro name present
    simp only [support,List.mem_singleton,reduceCtorEq] at present
  · intro token _
    exact same
private theorem cut_inputs (smart used : Bool) (first second : Reference → Bool)
    (same : first (.uninterned 10) = second (.uninterned 20)) :
    SourceCurrentScopedDeletionInputs.Compatible (expression smart used) symbolic firstNames secondNames first second := by
  constructor
  · intro name present
    simp only [support,List.mem_singleton,reduceCtorEq] at present
  · intro token _
    exact same


private theorem checked (smart used warm : Bool) :
    ∃ (body : Syntax Nat Bool) (expression : Syntax Nat Bool)
      (first second extensionValue : Value Nat Bool)
      (coldLeft coldRight firstBefore firstAfter reader : State Nat Bool),
      body = (if used then .node [.mk 7 false [.var 0,.binder true (.node [.mk 8 true [.var 0,.var 2]])]]
        else .union [.var 0,.binder true (.var 2)]) ∧
      expression = .binder smart body ∧
      build expression [.reference (.uninterned 10)] empty = .done first coldLeft ∧
      build expression [.reference (.uninterned 20)] coldLeft = .done second coldRight ∧
      firstBefore = (if warm then coldRight else empty) ∧
      firstAfter = (if warm then coldRight else coldLeft) ∧
      Context firstBefore [.reference (.uninterned 10)] ∧
      Context firstAfter [.reference (.uninterned 20)] ∧
      build expression [.reference (.uninterned 10)] firstBefore = .done first firstAfter ∧
      build expression [.reference (.uninterned 20)] firstAfter = .done second coldRight ∧
      build (.node [.mk 99 false []]) [] coldRight = .done extensionValue reader ∧
      reader.nodes.next = coldRight.nodes.next + 1 ∧
      Grows firstAfter reader ∧ Grows coldRight reader ∧
      Nonempty (History empty reader) ∧ Heap Correct reader ∧
      first ≠ second ∧
      (match first with | .mu .. => true | _ => false) = (used || !smart) ∧
      (match second with | .mu .. => true | _ => false) = (used || !smart) ∧
      (match first with | .mu _ _ depth ordinary => InternedFreshOrdinaryDepthHeap.usesLocal depth ordinary | _ => false) = used ∧
      (match second with | .mu _ _ depth ordinary => InternedFreshOrdinaryDepthHeap.usesLocal depth ordinary | _ => false) = used ∧
      first.free ≠ [] ∧ second.free ≠ [] ∧
      (smart = true → used = false → first = .reference (.uninterned 10) ∧ second = .reference (.uninterned 20)) ∧
      ∀ (firstAssignment secondAssignment : Reference → Profile) (firstCuts secondCuts : Reference → Bool),
        firstAssignment (.uninterned 10) = secondAssignment (.uninterned 20) →
        firstCuts (.uninterned 10) = secondCuts (.uninterned 20) →
        Equivalent (deleted firstCuts first firstAssignment) (deleted secondCuts second secondAssignment) := by
  obtain ⟨history⟩ := common_history smart used
  have heap := common_heap smart used
  refine ⟨body used,expression smart used,leftValue smart used,rightValue smart used,result (extensionCall smart used),
    leftAfter smart used,rightAfter smart used,firstBefore smart used warm,firstAfter smart used warm,common smart used,
    rfl,rfl,left_done smart used false,right_done smart used false,rfl,rfl,
    first_context smart used warm,second_context smart used warm,left_done smart used warm,right_done smart used warm,
    extension_done smart used,allocation smart used,first_growth smart used warm,later smart used,⟨history⟩,heap,?_⟩
  obtain ⟨distinct,firstMu,secondMu,firstUsed,secondUsed,firstOpen,secondOpen,unused⟩ := output_shape smart used
  refine ⟨distinct,firstMu,secondMu,firstUsed,secondUsed,firstOpen,secondOpen,unused,?_⟩
  intro firstAssignment secondAssignment firstCuts secondCuts profiles cuts
  have firstInputs : symbolic.map (input firstNames) = captures 10 := rfl
  have secondInputs : symbolic.map (input secondNames) = captures 20 := rfl
  exact SourceCurrentCausalSourceComparison.source (expression smart used) (common smart used) symbolic firstNames secondNames
    firstAssignment secondAssignment firstCuts secondCuts
    (firstBefore smart used warm) (firstAfter smart used warm) (firstAfter smart used warm) (rightAfter smart used)
    (leftValue smart used) (rightValue smart used)
    (firstInputs ▸ first_context smart used warm) (secondInputs ▸ second_context smart used warm)
    (aliases smart used) (profile_inputs smart used firstAssignment secondAssignment profiles)
    (cut_inputs smart used firstCuts secondCuts cuts)
    (by simpa only [firstInputs] using left_done smart used warm)
    (by simpa only [secondInputs] using right_done smart used warm)
    (first_growth smart used warm) (later smart used) heap history

/-- Actual nested raw and smart binders compare at a later causal reader for arbitrary compatible root assignments and cuts. -/
theorem actual_nested_pair (smart used warm : Bool) :
    ∃ (body : Syntax Nat Bool) (expression : Syntax Nat Bool)
      (first second extensionValue : Value Nat Bool)
      (coldLeft coldRight firstBefore firstAfter reader : State Nat Bool),
      body = (if used then .node [.mk 7 false [.var 0,.binder true (.node [.mk 8 true [.var 0,.var 2]])]]
        else .union [.var 0,.binder true (.var 2)]) ∧
      expression = .binder smart body ∧
      build expression [.reference (.uninterned 10)] empty = .done first coldLeft ∧
      build expression [.reference (.uninterned 20)] coldLeft = .done second coldRight ∧
      firstBefore = (if warm then coldRight else empty) ∧
      firstAfter = (if warm then coldRight else coldLeft) ∧
      Context firstBefore [.reference (.uninterned 10)] ∧
      Context firstAfter [.reference (.uninterned 20)] ∧
      build expression [.reference (.uninterned 10)] firstBefore = .done first firstAfter ∧
      build expression [.reference (.uninterned 20)] firstAfter = .done second coldRight ∧
      build (.node [.mk 99 false []]) [] coldRight = .done extensionValue reader ∧
      reader.nodes.next = coldRight.nodes.next + 1 ∧
      Grows firstAfter reader ∧ Grows coldRight reader ∧
      Nonempty (History empty reader) ∧ Heap Correct reader ∧
      first ≠ second ∧
      (match first with | .mu .. => true | _ => false) = (used || !smart) ∧
      (match second with | .mu .. => true | _ => false) = (used || !smart) ∧
      (match first with | .mu _ _ depth ordinary => InternedFreshOrdinaryDepthHeap.usesLocal depth ordinary | _ => false) = used ∧
      (match second with | .mu _ _ depth ordinary => InternedFreshOrdinaryDepthHeap.usesLocal depth ordinary | _ => false) = used ∧
      first.free ≠ [] ∧ second.free ≠ [] ∧
      (smart = true → used = false → first = .reference (.uninterned 10) ∧ second = .reference (.uninterned 20)) ∧
      ∀ (firstAssignment secondAssignment : Reference → Profile) (firstCuts secondCuts : Reference → Bool),
        firstAssignment (.uninterned 10) = secondAssignment (.uninterned 20) →
        firstCuts (.uninterned 10) = secondCuts (.uninterned 20) →
        Equivalent (deleted firstCuts first firstAssignment) (deleted secondCuts second secondAssignment) := checked smart used warm

end MicroCFTA.CausalSourceIntegration
