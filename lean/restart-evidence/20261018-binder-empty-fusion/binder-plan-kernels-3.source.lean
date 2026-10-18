import MicroCFTA.SourceCurrentStoredMuEmptyPlan

set_option linter.all true
set_option maxRecDepth 30000
set_option maxHeartbeats 5000000
set_option cbv.maxSteps 100000000

namespace MicroCFTA.StoredMuEmptyPlanKernels
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedConstruction (Syntax Outcome)
open InternedFreshOrdinaryConstruction (build)
open InternedFreshOrdinaryStoredSubstitution (execute)
open InternedStoredSubstitution (Environment Replacements leaves input encode)
open InternedProfileSemantics (evaluate mapNames lower isEmpty)
open InternedRootProfile (profile)
open InternedBinderProtocol (Reference)
open SourceEqualityRequiredCache (Ready)

private def source : Syntax Nat Bool :=
  .binder false (.binder false (.binder false (.union [.var 1,.var 2])))
private def built := build source [] empty
private def root : Value Nat Bool := match built with | .done value _ => value | .pending .. => .empty
private def reader := built.state
private def target : Value Nat Bool := match root with | .mu _ body _ _ => body | _ => .empty
private def outerName : Reference := match root with | .mu entry _ _ _ => .interned entry.identity | _ => .depth
private def entry : Interned InternedBinderProtocol.NodeKey := match target with
  | .mu entry _ _ _ => entry
  | _ => ⟨0,.node []⟩
private def body : Value Nat Bool := match target with | .mu _ body _ _ => body | _ => .empty
private def depth : Value Nat Bool := match target with | .mu _ _ depth _ => depth | _ => .empty
private def ordinary : Value Nat Bool := match target with | .mu _ _ _ ordinary => ordinary | _ => .empty
private def environment : Environment Nat Bool := fun name => if name = outerName then some .empty else none
private def rebuilt := execute target environment reader
private def after := rebuilt.state
private def unlowered := evaluate (encode (leaves body) [] body) ((leaves body).map (fun leaf => match leaf with
  | .reference name => if .interned entry.identity = name then some [Sum.inl ()]
      else mapNames Sum.inr (profile (input environment leaf))
  | _ => mapNames Sum.inr (profile (input environment leaf))))

private theorem built_done : build source [] empty = .done root reader := by cbv
private theorem ready : Ready reader := SourceEqualityRequiredCache.constructed source root reader built_done
private theorem root_available : Available reader root :=
  (InternedFreshOrdinaryFacts.build_verified source [] empty InternedNestedFacts.empty_facts
    (by intro value impossible; cases impossible)).result root reader built_done
private theorem target_shape : target = .mu entry body depth ordinary := by cbv
private theorem target_available : Available reader target := by
  have selected : target ∈ InternedProbeProvenance.children root := by cbv; exact List.mem_cons_self
  exact root_available.children target selected
private theorem replacements : Replacements reader environment := by
  intro name value found
  dsimp only [environment] at found
  split at found
  · cases found; exact InternedProbeProvenance.empty_available reader
  · cases found
private theorem actual : execute target environment reader = .done .empty after := by cbv
private theorem opened : target.free.isEmpty = false := by cbv
private theorem used : .interned entry.identity ∈ body.free := by
  cbv
  exact List.mem_cons_of_mem _ List.mem_cons_self
private theorem symbolic : unlowered = some [Sum.inl ()] := by cbv

private theorem checked :
    build source [] empty = .done root reader ∧ Ready reader ∧ Available reader target ∧
    target = .mu entry body depth ordinary ∧ target.free.isEmpty = false ∧
    .interned entry.identity ∈ body.free ∧
    execute target environment reader = .done .empty after ∧
    evaluate (encode (leaves body) [.interned entry.identity] body)
      (some [Sum.inl ()] :: ((leaves body).map (fun leaf => profile (input environment leaf))).map (mapNames Sum.inr)) =
      unlowered ∧
    unlowered = some [Sum.inl ()] ∧ isEmpty unlowered = false ∧
    isEmpty (lower unlowered) = true ∧
    ((Value.empty : Value Nat Bool).referenceOf == .empty) = isEmpty (lower unlowered) := by
  have bound := SourceCurrentStoredMuEmptyPlan.rebind_profile body (.interned entry.identity) environment reader
    ready.semantic.1.normal.facts.coherent (target_shape ▸ target_available |>.children body
      (by simp [InternedProbeProvenance.children]))
  have current := SourceCurrentStoredMuEmptyPlan.open_execute entry body depth ordinary environment reader ready
    (target_shape ▸ target_available) replacements (target_shape ▸ opened) .empty after
    (target_shape ▸ actual)
  have boundSame : evaluate (encode (leaves body) [.interned entry.identity] body)
      (some [Sum.inl ()] :: ((leaves body).map (fun leaf => profile (input environment leaf))).map (mapNames Sum.inr)) =
      unlowered := by
    convert bound using 1
    congr 1
    apply List.map_congr_left
    intro leaf _
    cases leaf <;> rfl
  have currentSame : ((Value.empty : Value Nat Bool).referenceOf == .empty) = isEmpty (lower unlowered) := by
    convert current using 1
    congr 3
    apply List.map_congr_left
    intro leaf _
    cases leaf <;> rfl
  exact ⟨built_done,ready,target_available,target_shape,opened,used,actual,boundSame,symbolic,
    by rw [symbolic]; rfl,by rw [symbolic]; rfl,currentSame⟩

/-- A source-built used open Mu becomes Empty after external erasure; its unlowered fresh marker remains nonempty. -/
theorem witness :
    build source [] empty = .done root reader ∧ Ready reader ∧ Available reader target ∧
    target = .mu entry body depth ordinary ∧ target.free.isEmpty = false ∧
    .interned entry.identity ∈ body.free ∧
    execute target environment reader = .done .empty after ∧
    evaluate (encode (leaves body) [.interned entry.identity] body)
      (some [Sum.inl ()] :: ((leaves body).map (fun leaf => profile (input environment leaf))).map (mapNames Sum.inr)) =
      unlowered ∧
    unlowered = some [Sum.inl ()] ∧ isEmpty unlowered = false ∧
    isEmpty (lower unlowered) = true ∧
    ((Value.empty : Value Nat Bool).referenceOf == .empty) = isEmpty (lower unlowered) := checked

end MicroCFTA.StoredMuEmptyPlanKernels
