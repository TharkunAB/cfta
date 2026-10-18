import MicroCFTA.SourceCurrentTrackedMarkerChoice
namespace MicroCFTA.TrackedMarkerChoiceKernels
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedConstruction (Syntax Outcome)
open InternedFreshOrdinaryConstruction (build)
open InternedFreshOrdinaryStoredSubstitution (execute)
open InternedStoredSubstitution (Environment Replacements leaves input)
open InternedBinderProtocol (Reference)
open InternedRootProfile (profile Equivalent)
open SourceCurrentStoredMuTrackedProfile (erase)
open SourceEqualityRequiredCache (Ready Keeps)
open SourceCurrentStoredMuLexicalInputs (shadow)
set_option maxRecDepth 30000
set_option maxHeartbeats 5000000
set_option cbv.maxSteps 100000000

private def val (outcome : Outcome Nat Bool (Value Nat Bool)) : Value Nat Bool :=
  match outcome with | .done value _ => value | .pending .. => .empty
private def done (outcome : Outcome Nat Bool (Value Nat Bool)) : Bool :=
  match outcome with | .done .. => true | .pending .. => false
private theorem unpack (outcome : Outcome Nat Bool (Value Nat Bool)) (success : done outcome = true) :
    outcome = .done (val outcome) outcome.state := by
  cases outcome <;> simp_all [done,val,Outcome.state]
private def source : Syntax Nat Bool :=
  .binder false (.binder false (.binder false (.union [.var 1,.var 2])))
private def built := build source [] empty
private def root := val built
private def reader := built.state
private def target := match root with | .mu _ body _ _ => body | _ => .empty
private def outerName : Reference :=
  match root with | .mu entry _ _ _ => .interned entry.identity | _ => .depth
private def entry : Interned InternedBinderProtocol.NodeKey :=
  match target with | .mu entry _ _ _ => entry | _ => ⟨0,.node []⟩
private def body := match target with | .mu _ body _ _ => body | _ => .empty
private def depth := match target with | .mu _ _ depth _ => depth | _ => .empty
private def ordinary := match target with | .mu _ _ _ ordinary => ordinary | _ => .empty
private def environment (level : Nat) : Environment Nat Bool :=
  fun name => if name = outerName then some (.reference (.uninterned level)) else none
private def tracked : List Reference := [.depth,.uninterned 200]
private def marker := SourceCurrentTrackedMarkerChoice.choose tracked
  ((leaves body).map (input (environment 101)) ++ (leaves ordinary).map (input (environment 205)))
private def whole := execute target (environment 101) reader
private def strictBody := execute body
  (shadow (.interned entry.identity) (.reference marker) (environment 101)) reader

private theorem built_done : build source [] empty = .done root reader :=
  unpack built (by cbv)
private theorem ready : Ready reader :=
  SourceEqualityRequiredCache.constructed source root reader built_done
private theorem target_shape : target = .mu entry body depth ordinary := by cbv
private theorem target_available : Available reader target := by
  have available := (InternedFreshOrdinaryFacts.build_verified source [] empty InternedNestedFacts.empty_facts
    (by intro value impossible; cases impossible)).result root reader built_done
  exact available.children target (by cbv; exact List.mem_cons_self)
private theorem bodies_available : Available reader body ∧ Available reader ordinary := by
  have available : Available reader (.mu entry body depth ordinary) := target_shape ▸ target_available
  constructor
  · exact available.children body List.mem_cons_self
  · exact available.children ordinary (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
private theorem replacements (level : Nat) : Replacements reader (environment level) := by
  intro name value found
  dsimp only [environment] at found
  split at found
  · cases found
    exact InternedNestedProvenance.ordinary_available _ level
  · cases found
private theorem fresh :
    Available reader (.reference marker) ∧ marker ∉ tracked ∧
    (∀ leaf ∈ leaves body, marker ∉ (profile (input (environment 101) leaf)).getD []) ∧
    (∀ leaf ∈ leaves ordinary, marker ∉ (profile (input (environment 205) leaf)).getD []) :=
  SourceCurrentTrackedMarkerChoice.bodies tracked body ordinary (environment 101) (environment 205) reader
private theorem marker_exact : marker = .uninterned 206 := by cbv
private theorem whole_done : execute target (environment 101) reader = .done (val whole) whole.state :=
  unpack whole (by cbv)
private theorem body_done : execute body (shadow (.interned entry.identity) (.reference marker) (environment 101)) reader =
    .done (val strictBody) strictBody.state := unpack strictBody (by cbv)
private theorem mixed : profile (val strictBody) = some [marker,.uninterned 101] := by cbv
private theorem result : val whole = .reference (.uninterned 101) := by cbv
private theorem used : (.interned entry.identity) ∈ body.free := by
  cbv
  exact List.mem_cons_of_mem _ List.mem_cons_self
private theorem endpoint :
    Keeps reader strictBody.state ∧ Available strictBody.state (val strictBody) ∧
    Equivalent (profile (val whole)) (erase marker (profile (val strictBody))) := by
  obtain ⟨value,after,actual,kept,available,related⟩ := SourceCurrentStoredMuTrackedProfile.complete
    entry body depth ordinary (environment 101) reader ready (target_shape ▸ target_available)
    (replacements 101) (by cbv) marker fresh.1 fresh.2.2.1 (val whole) whole.state (target_shape ▸ whole_done)
  obtain ⟨rfl,rfl⟩ := Outcome.done.inj (actual.symm.trans body_done)
  exact ⟨kept,available,related⟩

private theorem checked_witness :
    build source [] empty = .done root reader ∧ Ready reader ∧
    target = .mu entry body depth ordinary ∧ Available reader target ∧
    Available reader body ∧ Available reader ordinary ∧
    (.interned entry.identity) ∈ body.free ∧
    Replacements reader (environment 101) ∧ Replacements reader (environment 205) ∧
    marker = .uninterned 206 ∧ Available reader (.reference marker) ∧ marker ∉ tracked ∧
    (∀ leaf ∈ leaves body, marker ∉ (profile (input (environment 101) leaf)).getD []) ∧
    (∀ leaf ∈ leaves ordinary, marker ∉ (profile (input (environment 205) leaf)).getD []) ∧
    execute target (environment 101) reader = .done (val whole) whole.state ∧
    execute body (shadow (.interned entry.identity) (.reference marker) (environment 101)) reader =
      .done (val strictBody) strictBody.state ∧
    Keeps reader strictBody.state ∧ Available strictBody.state (val strictBody) ∧
    Equivalent (profile (val whole)) (erase marker (profile (val strictBody))) ∧
    profile (val strictBody) = some [marker,.uninterned 101] ∧
    val whole = .reference (.uninterned 101) := by
  exact ⟨built_done,ready,target_shape,target_available,bodies_available.1,bodies_available.2,used,
    replacements 101,replacements 205,marker_exact,fresh.1,fresh.2.1,fresh.2.2.1,fresh.2.2.2,
    whole_done,body_done,endpoint.1,endpoint.2.1,endpoint.2.2,mixed,result⟩

theorem actual_nested_mixed_choice :
    build source [] empty = .done root reader ∧ Ready reader ∧
    target = .mu entry body depth ordinary ∧ Available reader target ∧
    Available reader body ∧ Available reader ordinary ∧
    (.interned entry.identity) ∈ body.free ∧
    Replacements reader (environment 101) ∧ Replacements reader (environment 205) ∧
    marker = .uninterned 206 ∧ Available reader (.reference marker) ∧ marker ∉ tracked ∧
    (∀ leaf ∈ leaves body, marker ∉ (profile (input (environment 101) leaf)).getD []) ∧
    (∀ leaf ∈ leaves ordinary, marker ∉ (profile (input (environment 205) leaf)).getD []) ∧
    execute target (environment 101) reader = .done (val whole) whole.state ∧
    execute body (shadow (.interned entry.identity) (.reference marker) (environment 101)) reader =
      .done (val strictBody) strictBody.state ∧
    Keeps reader strictBody.state ∧ Available strictBody.state (val strictBody) ∧
    Equivalent (profile (val whole)) (erase marker (profile (val strictBody))) ∧
    profile (val strictBody) = some [marker,.uninterned 101] ∧
    val whole = .reference (.uninterned 101) := checked_witness

end MicroCFTA.TrackedMarkerChoiceKernels

set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.proofs.threshold 254
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
#check @MicroCFTA.TrackedMarkerChoiceKernels.actual_nested_mixed_choice
#print MicroCFTA.TrackedMarkerChoiceKernels.actual_nested_mixed_choice
#print axioms MicroCFTA.TrackedMarkerChoiceKernels.actual_nested_mixed_choice
