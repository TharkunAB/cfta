import MicroCFTA.SourceCurrentStoredMuProfileReduction
set_option linter.all true
set_option pp.fullNames true
set_option pp.explicit true
set_option maxRecDepth 30000
set_option maxHeartbeats 5000000
set_option cbv.maxSteps 100000000

namespace MicroCFTA.PureMuIntegration
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedConstruction (Syntax Outcome)
open InternedFreshOrdinaryConstruction (build ordinaryLevel)
open InternedStoredSubstitution (leaves encode)
open InternedBinderProtocol (Reference)
open InternedRootProfile (Profile profile Equivalent)
open InternedProfileSemantics (evaluate)
open SourceCurrentStoredProfileFunction (denote)
open SourceCurrentStoredMuProfileContract (Correct shadow)
open SourceCurrentStoredMuTrackedProfile (erase)
open SourceEqualityRequiredCache (Ready)

private def value (outcome : Outcome Nat Bool (Value Nat Bool)) : Value Nat Bool :=
  match outcome with | .done result _ => result | .pending .. => .empty
private def source : Syntax Nat Bool := .binder false (.binder false (.var 1))
private def built := build source [] empty
private def root := value built
private def reader := built.state
private def target := match root with | .mu _ body _ _ => body | _ => .empty
private def outer : Reference := match root with | .mu entry _ _ _ => .interned entry.identity | _ => .depth
private def entry : Interned InternedBinderProtocol.NodeKey :=
  match target with | .mu entry _ _ _ => entry | _ => ⟨0,.node []⟩
private def body := match target with | .mu _ body _ _ => body | _ => .empty
private def depth := match target with | .mu _ _ depth _ => depth | _ => .empty
private def ordinary := match target with | .mu _ _ _ ordinary => ordinary | _ => .empty
private def assignment : Reference → Profile := fun name => if name = outer then some [.uninterned 101,.uninterned 102] else none
private abbrev assigned (leaf : Value Nat Bool) : Profile := match leaf with | .reference name => assignment name | _ => profile leaf
private def context : List (Value Nat Bool) := .empty :: leaves body

private theorem actual : build source [] empty = .done root reader := by cbv
private theorem ready : Ready reader := SourceEqualityRequiredCache.constructed source root reader actual
private theorem root_available : Available reader root :=
  (InternedFreshOrdinaryFacts.build_verified source [] empty InternedNestedFacts.empty_facts
    (by intro val impossible; cases impossible)).result root reader actual
private theorem target_available : Available reader target :=
  root_available.children target (by cbv; exact List.mem_cons_self)
private theorem shape : target = .mu entry body depth ordinary := by cbv
private theorem body_available : Available reader body :=
  (shape ▸ target_available).children body (by simp [InternedProbeProvenance.children])
private theorem body_reference : body = .reference outer := by cbv
private theorem ordinary_body : ordinary = body := by cbv
private theorem own_different : outer ≠ .interned entry.identity := by cbv; intro impossible; cases impossible
private theorem ordinary_different : outer ≠ .uninterned (ordinaryLevel depth) := by cbv; intro impossible; cases impossible
private theorem opened : target.free.isEmpty = false := by cbv
private theorem candidate_correct : Correct entry body depth ordinary := by
  intro rho localProfile
  rw [ordinary_body]
  have same := SourceCurrentStoredProfileFunction.congr body reader ready.semantic.1.normal.facts.coherent
    body_available (shadow (.interned entry.identity) localProfile rho) (shadow (.uninterned (ordinaryLevel depth)) localProfile rho)
    (by
      intro name member
      rw [body_reference,Value.free,List.mem_singleton] at member
      subst name
      simp only [shadow,own_different,ordinary_different,ite_false])
  rw [same]
  exact InternedProfileEquivalence.refl _
private theorem visible : denote target assignment = some [.uninterned 101,.uninterned 102] := by cbv
private theorem closed_shortcut : denote root assignment = profile root :=
  SourceCurrentStoredProfileFunction.closed root assignment (by cbv)
private theorem context_available : InternedNestedProvenance.Values reader context := by
  intro selected member
  rcases List.mem_cons.mp member with rfl | member
  · exact empty_available _
  · exact InternedStoredSubstitution.leaves_available body reader body_available selected member
private theorem recaptured :
    evaluate (encode context [] body) (context.map assigned) = denote body assignment := by
  simpa only [assigned,denote] using SourceCurrentStoredProfilePlan.recapture context body assigned reader ready.semantic.1.normal.facts.coherent
    context_available body_available (fun _ member => List.mem_cons_of_mem _ member)
private theorem rebound (marker : Reference) :
    evaluate (encode context [.interned entry.identity] body) (some [marker] :: context.map assigned) =
      evaluate (encode context [] body) (context.map (fun leaf => match leaf with
        | .reference name => if .interned entry.identity = name then some [marker] else assigned leaf
        | _ => assigned leaf)) := by
  simpa only [assigned] using SourceCurrentStoredProfilePlan.rebind context body (.interned entry.identity) (some [marker]) assigned reader
    ready.semantic.1.normal.facts.coherent context_available (fun _ member => List.mem_cons_of_mem _ member)

private theorem checked :
    build source [] empty = .done root reader ∧ Ready reader ∧ Available reader target ∧
    target = .mu entry body depth ordinary ∧ target.free.isEmpty = false ∧
    Correct entry body depth ordinary ∧
    denote target assignment = some [.uninterned 101,.uninterned 102] ∧
    denote root assignment = profile root ∧
    evaluate (encode context [] body) (context.map assigned) = denote body assignment ∧
    ∃ marker : Reference,
      (∀ leaf ∈ leaves body, marker ∉ (assigned leaf).getD []) ∧
      denote target assignment = erase marker (denote body (shadow (.interned entry.identity) (some [marker]) assignment)) ∧
      Equivalent (denote target assignment)
        (erase marker (denote ordinary (shadow (.uninterned (ordinaryLevel depth)) (some [marker]) assignment))) ∧
      evaluate (encode context [.interned entry.identity] body) (some [marker] :: context.map assigned) =
        evaluate (encode context [] body) (context.map (fun leaf => match leaf with
          | .reference name => if .interned entry.identity = name then some [marker] else assigned leaf
          | _ => assigned leaf)) := by
  obtain ⟨marker,fresh⟩ := SourceCurrentStoredMuProfileReduction.fresh_marker ((leaves body).map assigned)
  have freshLeaves : ∀ leaf ∈ leaves body, marker ∉ (assigned leaf).getD [] :=
    fun leaf member => fresh (assigned leaf) (List.mem_map.mpr ⟨leaf,member,rfl⟩)
  refine ⟨actual,ready,target_available,shape,opened,candidate_correct,visible,closed_shortcut,recaptured,
    marker,freshLeaves,?_,?_,rebound marker⟩
  · exact SourceCurrentStoredMuProfileReduction.open_denote entry body depth ordinary assignment reader
      ready.semantic.1.normal.facts.coherent (shape ▸ target_available) (shape ▸ opened) marker (by simpa only [assigned] using freshLeaves)
  · exact SourceCurrentStoredMuProfileReduction.open_correct entry body depth ordinary assignment reader
      ready.semantic.1.normal.facts.coherent (shape ▸ target_available) candidate_correct (shape ▸ opened) marker (by simpa only [assigned] using freshLeaves)

/-- A source-built open raw Mu reduces under visible outer profiles and a derived payload contract. -/
theorem actual_open :
    build source [] empty = .done root reader ∧ Ready reader ∧ Available reader target ∧
    target = .mu entry body depth ordinary ∧ target.free.isEmpty = false ∧
    Correct entry body depth ordinary ∧
    denote target assignment = some [.uninterned 101,.uninterned 102] ∧
    denote root assignment = profile root ∧
    evaluate (encode context [] body) (context.map assigned) = denote body assignment ∧
    ∃ marker : Reference,
      (∀ leaf ∈ leaves body, marker ∉ (assigned leaf).getD []) ∧
      denote target assignment = erase marker (denote body (shadow (.interned entry.identity) (some [marker]) assignment)) ∧
      Equivalent (denote target assignment)
        (erase marker (denote ordinary (shadow (.uninterned (ordinaryLevel depth)) (some [marker]) assignment))) ∧
      evaluate (encode context [.interned entry.identity] body) (some [marker] :: context.map assigned) =
        evaluate (encode context [] body) (context.map (fun leaf => match leaf with
          | .reference name => if .interned entry.identity = name then some [marker] else assigned leaf
          | _ => assigned leaf)) := checked

end MicroCFTA.PureMuIntegration
