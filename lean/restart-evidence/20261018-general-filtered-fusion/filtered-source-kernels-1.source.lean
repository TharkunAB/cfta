import MicroCFTA.SourceCurrentFilteredSourceFusion

set_option linter.all true
set_option maxRecDepth 30000
set_option maxHeartbeats 5000000
set_option cbv.maxSteps 100000000

namespace MicroCFTA.FilteredSourceKernels
open Cache Language InternedConstructorTemplates InternedProbeProvenance InternedRecordCoherence
open InternedNestedConstruction (Syntax Outcome)
open InternedFreshOrdinaryConstruction (build)
open InternedFreshOrdinaryStoredSubstitution (execute)
open InternedFreshOrdinaryLiveInputs (input)
open InternedStoredSubstitution (Environment Replacements)
open InternedBinderProtocol (Reference)
open SourceCurrentReaderReplacementSlots (Paired Slot)
open SourceCurrentConstrainedCapSourceHistory (Context)
open SourceCurrentUsedBinderAliasTransport (Aliases Scope)
open SourceEqualityRequiredCache (Ready)

private def source : Syntax Nat Bool := .binder false (.node [.mk 7 false [.var 0]])
private def built := build source [] empty
private def captured : Value Nat Bool := match built with | .done value _ => value | .pending .. => .empty
private def reader := built.state
private def q : Reference := .uninterned 1
private def r : Reference := .uninterned 2
private def firstNames : Unit → Reference := fun _ => q
private def secondNames : Unit → Reference := fun _ => r
private def inputs : List (Sum (Value Nat Bool) Unit) := [.inr (),.inl captured]
private def firstMap : Environment Nat Bool := fun name => if name = q then some captured else none
private def secondMap : Environment Nat Bool := fun _ => none
private def used : Value Nat Bool → Prop
  | .mu entry body _ _ => .interned entry.identity ∈ body.free
  | _ => False
private theorem done : build source [] empty = .done captured reader := by cbv
private theorem ready : Ready reader := SourceEqualityRequiredCache.constructed source captured reader done
private theorem available : Available reader captured :=
  (InternedFreshOrdinaryFacts.build_verified source [] empty InternedNestedFacts.empty_facts
    (by intro value impossible; cases impossible)).result captured reader done
private theorem reference_available (name : Reference) (sentinel : ∃ n, name = .uninterned n) : Available reader (.reference name) := by
  obtain ⟨n,rfl⟩ := sentinel
  exact InternedProbeProvenance.reference_available reader _ (InternedFreshProbeKeys.sentinel_references_issued reader n).2
private theorem context (names : Unit → Reference) (argument : Available reader (.reference (names ()))) :
    Context reader (inputs.map (input names)) := by
  refine ⟨SourceRecursiveIntersectionSemanticHeap.context reader ready.semantic _ ?_,ready.semantic.2⟩
  intro value member
  have choices : value = .reference (names ()) ∨ value = captured := by
    simpa only [inputs,List.map_cons,List.map_nil,input,List.mem_cons,List.not_mem_nil,or_false] using member
  rcases choices with rfl | rfl
  · exact argument
  · exact available
private theorem aliases : Aliases (.var 0) inputs firstNames secondNames := by
  intro a ha b hb
  simp only [Scope,SourceCurrentNativeNormalizationInputs.support,InternedFreeNameSemantics.evaluate,
    inputs,List.map_cons,List.map_nil,List.getElem?_cons_zero,Option.getD_some,
    SourceCurrentNativeNormalizationInputs.inputNames,List.mem_cons,List.not_mem_nil,or_false] at ha hb
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> simp [firstNames,secondNames,q,r]
private theorem tests : ∀ label ∈ Scope (.var 0) inputs,
    Sum.elim id firstNames label = q ↔ Sum.elim id secondNames label = r := by
  intro label member
  simp only [Scope,SourceCurrentNativeNormalizationInputs.support,InternedFreeNameSemantics.evaluate,
    inputs,List.map_cons,List.map_nil,List.getElem?_cons_zero,Option.getD_some,
    SourceCurrentNativeNormalizationInputs.inputNames,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl <;> simp [firstNames,secondNames,q,r]
private theorem paired : Paired (fun a b => (a.referenceOf == .empty) = (b.referenceOf == .empty))
    firstMap secondMap (inputs.map (input firstNames)) (inputs.map (input secondNames)) := by
  refine .cons ?_ (.cons ?_ .nil)
  · change (((firstMap q).getD (.reference q)).referenceOf == .empty) =
      (((secondMap r).getD (.reference r)).referenceOf == .empty)
    cbv
  · change captured = captured ∧ ∀ name ∈ captured.free, firstMap name = secondMap name
    refine ⟨rfl,?_⟩
    intro name member
    have closed : captured.free = [] := by cbv
    rw [closed] at member
    cases member
private theorem first_replacements : Replacements reader firstMap := by
  intro name output found
  dsimp only [firstMap] at found
  split at found
  · cases found; exact available
  · cases found
private theorem second_replacements : Replacements reader secondMap := by intro name output impossible; cases impossible
private theorem first_build : build (.var 0) (inputs.map (input firstNames)) reader = .done (.reference q) reader := rfl
private theorem second_build : build (.var 0) (inputs.map (input secondNames)) reader = .done (.reference r) reader := rfl
private theorem first_call : execute (.reference q) firstMap reader = .done captured reader := by cbv
private theorem second_call : execute (.reference r) secondMap reader = .done (.reference r) reader := by cbv
private theorem nonempty : ∀ name, ((firstMap name).getD (.reference name)).referenceOf ≠ .empty := by
  intro name
  dsimp only [firstMap]
  split
  · cbv
    intro impossible
    cases impossible
  · simp [Value.referenceOf]

private theorem checked :
    build source [] empty = .done captured reader ∧ Ready reader ∧ used captured ∧ captured ≠ .reference r ∧
    Aliases (.var 0) inputs firstNames secondNames ∧
    Paired (fun a b => (a.referenceOf == .empty) = (b.referenceOf == .empty))
      firstMap secondMap (inputs.map (input firstNames)) (inputs.map (input secondNames)) ∧
    build (.var 0) (inputs.map (input firstNames)) reader = .done (.reference q) reader ∧
    build (.var 0) (inputs.map (input secondNames)) reader = .done (.reference r) reader ∧
    execute (.reference q) firstMap reader = .done captured reader ∧
    execute (.reference r) secondMap reader = .done (.reference r) reader ∧
    (captured.referenceOf == .empty) = ((Value.reference r : Value Nat Bool).referenceOf == .empty) := by
  have qa := reference_available q ⟨1,rfl⟩
  have ra := reference_available r ⟨2,rfl⟩
  have base := SourceCurrentFilteredSourceFusion.reference (Symbol := Nat) (Guard := Bool) 0 reader ready inputs
    firstNames secondNames q r firstMap secondMap reader reader reader reader
    (.reference q) (.reference r) (.reference q) (.reference r) captured (.reference r)
    (context firstNames qa) (context secondNames ra) aliases tests paired first_replacements second_replacements qa ra
    first_build second_build (grows_refl _) (grows_refl _) rfl rfl first_call second_call
  have adapter := SourceCurrentFilteredSourceFusion.nonempty_maps (.var 0) inputs firstNames secondNames q r
    firstMap secondMap reader reader reader reader reader (.reference q) (.reference r) (.reference q) (.reference r)
    captured (.reference r) (context firstNames qa) (context secondNames ra) first_build second_build ready qa ra
    first_replacements second_replacements rfl rfl first_call second_call (fun name _ => nonempty name)
    (by intro name _; simp [secondMap,Value.referenceOf])
  exact ⟨done,ready,(by cbv; exact List.mem_cons_self),(by cbv; intro impossible; cases impossible),
    aliases,paired,first_build,second_build,first_call,second_call,base.trans (adapter.symm.trans base)⟩

/-- A source-built used Mu and a distinct literal reference satisfy the variable law and nonempty-map adapter. -/
theorem witness :
    build source [] empty = .done captured reader ∧ Ready reader ∧ used captured ∧ captured ≠ .reference r ∧
    Aliases (.var 0) inputs firstNames secondNames ∧
    Paired (fun a b => (a.referenceOf == .empty) = (b.referenceOf == .empty))
      firstMap secondMap (inputs.map (input firstNames)) (inputs.map (input secondNames)) ∧
    build (.var 0) (inputs.map (input firstNames)) reader = .done (.reference q) reader ∧
    build (.var 0) (inputs.map (input secondNames)) reader = .done (.reference r) reader ∧
    execute (.reference q) firstMap reader = .done captured reader ∧
    execute (.reference r) secondMap reader = .done (.reference r) reader ∧
    (captured.referenceOf == .empty) = ((Value.reference r : Value Nat Bool).referenceOf == .empty) := checked

end MicroCFTA.FilteredSourceKernels
