import MicroCFTA.SourceCurrentConstrainedCapGuardBinder

set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000

namespace MicroCFTA.GuardBinderKernels
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedBinderProtocol (Reference)
open SourceCurrentConstrainedCapPairOccurrences (Classified)
variable {Symbol Guard : Type}

/-- A live repeated-pair input constructs its own finite binder, then replays the exact returned cache state. -/
theorem optional_and_replay [DecidableEq (EdgeKey Symbol Guard)] (annotation : Guard → Prop) (pair : Nat × Nat) :
    let old := Reference.intersection pair.1 pair.2
    let body : Value Symbol Guard := .reference old
    let weight : Reference → Nat := fun name => if name = old then 1 else 0
    old ∈ body.free ∧ ∃ value after,
      SourceRecursiveIntersectionMaybeMu.maybeMu pair body empty = .done value after ∧
      SourceRecursiveIntersectionMaybeMu.maybeMu pair body after = .done value after ∧
      SourceCurrentConstrainedCap.Cap annotation 1 value ∧ Classified weight 1 value ∧
      SourceCurrentConstrainedCapGuardHeap.Heap annotation after ∧
      SourceCurrentHereditaryConstruction.MuStored annotation after ∧ Available after value ∧
      SourceEqualityRequiredCache.Keeps (empty : State Symbol Guard) after := by
  dsimp only
  let old := Reference.intersection pair.1 pair.2
  let body : Value Symbol Guard := .reference old
  let weight : Reference → Nat := fun name => if name = old then 1 else 0
  have ready : SourceEqualityRequiredCache.Ready (empty : State Symbol Guard) :=
    SourceEqualityRequiredCache.constructed .empty .empty empty rfl
  have available : Available (empty : State Symbol Guard) body :=
    reference_available empty old (by
      intro identity member
      simp [body, Value.free] at member)
  have classified : Classified weight 1 body := SourceCurrentConstrainedCapPairOccurrences.reference weight 1 old (by simp [weight])
  obtain ⟨value, after, actual, capped, ranked, guards, stored, output, effects⟩ :=
    SourceCurrentConstrainedCapGuardBinder.intersection_complete annotation 1 pair body empty ready available
      (.plain 1 (.reference old)) (SourceCurrentConstrainedCapGuardHeap.empty_heap annotation)
      weight 1 (by decide) (by simp [weight, old]) classified (by
        intro name member
        have same : name = old := List.mem_singleton.mp member
        exact ⟨pair.1, pair.2, same⟩)
  have replay := SourceRecursiveIntersectionMaybeMu.replay pair body empty after after ready.semantic.1.normal.facts
    available value actual (InternedConstructorTemplates.grows_refl _)
  exact ⟨by simp [body, Value.free], value, after, actual, replay, capped, ranked, guards, stored, output, effects⟩

#print axioms optional_and_replay
#check @optional_and_replay
end MicroCFTA.GuardBinderKernels
