import MicroCFTA.SourceCurrentStoredLiveUnionLineage

set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.proofs.threshold 254
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000

namespace MicroCFTA.LiveUnionKernels
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedConstruction (Syntax Outcome)
open InternedFreshOrdinaryConstruction
open InternedFreshOrdinaryLiveInputs (input)
open InternedStoredSubstitution (Environment Replacements)
open InternedFreshOrdinaryStoredSubstitution (execute)
open SourceEqualityRequiredCache (Ready Keeps)
open SourceCurrentStoredProbeCompatibility (Compatible)
open SourceCurrentStoredMuBinderChildLineage (Paired Slot)
open SourceCurrentOpenObservationSurvival (Related)
open InternedStoredShallowCompletion (BinderFree ManyBinderFree EdgesBinderFree)

private def captureSource : Syntax Nat Bool := .binder true (.union [.node [.mk 3 true []],.node [.mk 4 false [.var 0]]])
private def captureBuilt := build captureSource [] empty
private def value (outcome : Outcome Nat Bool (Value Nat Bool)) := match outcome with | .done result _ => result | .pending .. => .empty
private def capture := value captureBuilt
private def base := captureBuilt.state
private def inner : Syntax Nat Bool := .node [.mk 8 false [.var 0]]
private def discarded : Syntax Nat Bool := .node [.mk 10 true [.empty,.var 1]]
private def source : Syntax Nat Bool := .union [.union [inner,.empty],discarded,.var 2]
private def inputs : List (Sum (Value Nat Bool) Unit) := [.inr (),.inl (.reference (.uninterned 0)),.inl capture]
private def firstNames : Unit → InternedBinderProtocol.Reference := fun _ => .uninterned 0
private def secondNames : Unit → InternedBinderProtocol.Reference := fun _ => .uninterned 9
private def first : Environment Nat Bool := fun name => if name = .uninterned 0 then some capture else none
private def second : Environment Nat Bool := fun name => if name = .uninterned 9 then some capture else none
private def isMu : Value Nat Bool → Bool | .mu .. => true | _ => false

private theorem captureActual : captureBuilt = .done capture base := by cbv
private theorem baseReady : Ready base := SourceEqualityRequiredCache.constructed captureSource capture base captureActual
private theorem captureAvailable : Available base capture :=
  (InternedFreshOrdinaryFacts.build_verified captureSource [] empty InternedNestedFacts.empty_facts
    (by intro output member; cases member)).result capture base captureActual
private theorem available (name : Unit → InternedBinderProtocol.Reference)
    (ordinary : ∃ level, name () = .uninterned level) :
    InternedNestedProvenance.Values base (inputs.map (input name)) := by
  obtain ⟨level,same⟩ := ordinary
  intro output member
  simp only [inputs,List.map_cons,List.map_nil,input,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · rw [same]
    exact InternedNestedProvenance.ordinary_available _ _
  · exact InternedNestedProvenance.ordinary_available _ _
  · exact captureAvailable
private theorem replacements (environment : Environment Nat Bool) (selected : InternedBinderProtocol.Reference)
    (shape : environment = fun name => if name = selected then some capture else none) : Replacements base environment := by
  intro name output found
  rw [shape] at found
  dsimp only at found
  split at found
  · cases found; exact captureAvailable
  · cases found
private theorem supported : SourceCurrentNativeNormalizationInputs.support source inputs = [.inr ()] := by cbv
private theorem compatible : Compatible source inputs firstNames secondNames first second := by
  constructor
  · intro name member
    rw [supported] at member
    have impossible := List.mem_singleton.mp member
    cases impossible
  · intro atom member
    cases atom
    rfl

private theorem initial_receipt :
    ¬ Paired first second (inputs.map (input firstNames)) (inputs.map (input secondNames)) ∧
    SourceCurrentNativeNormalizationInputs.support source inputs = [.inr ()] ∧
    ∃ rawFirst after rawSecond common left middle right reader,
      build source (inputs.map (input firstNames)) base = .done rawFirst after ∧
      build source (inputs.map (input secondNames)) after = .done rawSecond common ∧
      execute rawFirst first common = .done left middle ∧ execute rawSecond second middle = .done right reader ∧
      execute rawFirst first reader = .done left reader ∧ execute rawSecond second reader = .done right reader ∧
      Keeps base after ∧ Keeps after common ∧ Keeps common middle ∧ Keeps middle reader ∧
      Available reader left ∧ Available reader right ∧
      Nonempty (SourceCurrentNativeMuPublication.History common middle) ∧
      Nonempty (SourceCurrentNativeMuPublication.History middle reader) ∧ Related left right := by
  refine ⟨?_,supported,?_⟩
  · intro paired
    cases paired with
    | cons head tail =>
      cases tail with
      | cons bad remaining =>
        change capture = .reference (.uninterned 0) at bad
        have actualMu : isMu capture = true := by cbv
        rw [bad] at actualMu
        cases actualMu
  · exact SourceCurrentStoredLiveUnionLineage.initial source
      (by simp [source,inner,discarded,BinderFree,ManyBinderFree,EdgesBinderFree])
      inputs firstNames secondNames first second compatible base baseReady
      (available firstNames ⟨0,rfl⟩) (available secondNames ⟨9,rfl⟩)
      (replacements first (.uninterned 0) rfl) (replacements second (.uninterned 9) rfl)

/-- Actual initial inputs reconstruct a live union even when the full lexical lists fail Paired. -/
theorem ignored_alias_union_initial :
    ¬ Paired first second (inputs.map (input firstNames)) (inputs.map (input secondNames)) ∧
    SourceCurrentNativeNormalizationInputs.support source inputs = [.inr ()] ∧
    ∃ rawFirst after rawSecond common left middle right reader,
      build source (inputs.map (input firstNames)) base = .done rawFirst after ∧
      build source (inputs.map (input secondNames)) after = .done rawSecond common ∧
      execute rawFirst first common = .done left middle ∧ execute rawSecond second middle = .done right reader ∧
      execute rawFirst first reader = .done left reader ∧ execute rawSecond second reader = .done right reader ∧
      Keeps base after ∧ Keeps after common ∧ Keeps common middle ∧ Keeps middle reader ∧
      Available reader left ∧ Available reader right ∧
      Nonempty (SourceCurrentNativeMuPublication.History common middle) ∧
      Nonempty (SourceCurrentNativeMuPublication.History middle reader) ∧ Related left right := initial_receipt

end MicroCFTA.LiveUnionKernels
