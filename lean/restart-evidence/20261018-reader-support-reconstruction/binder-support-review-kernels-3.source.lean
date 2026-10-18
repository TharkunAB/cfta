import MicroCFTA.SourceCurrentReaderFiniteOrdinaryStep
import MicroCFTA.SourceCurrentOpenOriginSteps
import MicroCFTA.SourceCurrentStoredUnionObservations
import MicroCFTA.SourceCurrentFiniteObservationExecution

set_option linter.all true
set_option maxHeartbeats 3000000
set_option maxRecDepth 30000

namespace MicroCFTA.BinderSupportReview
open InternedConstructorTemplates InternedProbeProvenance
open InternedNestedConstruction (Syntax Outcome)
open InternedFreshOrdinaryConstruction (build)
open InternedFreshOrdinaryStoredSubstitution (unfold)

private def value (outcome : Outcome Nat Bool (Value Nat Bool)) :=
  match outcome with | .done result _ => result | .pending .. => .empty
private def inner : Syntax Nat Bool :=
  .binder true (.node [.mk 2 true [],.mk 3 false [.var 0,.var 1]])
private def source : Syntax Nat Bool :=
  .binder true (.node [.mk 0 true [],.mk 1 false [.var 0,inner]])
private def built := build source [] empty
private def original := value built
private def before := built.state
private def unfolded := unfold original before
private def next := value unfolded
private def after := unfolded.state

private def resultEntry : Cache.Interned InternedBinderProtocol.NodeKey :=
  (InternedRecordCoherence.entryOf next).getD ⟨0,.node []⟩
private def originalEntry : Cache.Interned InternedBinderProtocol.NodeKey :=
  (InternedRecordCoherence.entryOf original).getD ⟨0,.node []⟩
private def originalBody : Value Nat Bool :=
  match original with | .mu _ body _ _ => body | _ => .empty
private def originalDepth : Value Nat Bool :=
  match original with | .mu _ _ depth _ => depth | _ => .empty
private def originalOrdinary : Value Nat Bool :=
  match original with | .mu _ _ _ ordinary => ordinary | _ => .empty
private def chosenRow : EdgeValue Nat Bool :=
  ((InternedEdgeResidency.nodeEdges next)[1]?).getD (EdgeValue.mk ⟨0,⟨0,[],false⟩⟩ [])
private def generated : Value Nat Bool := (chosenRow.children[1]?).getD .empty
private def generatedEntry : Cache.Interned InternedBinderProtocol.NodeKey :=
  (InternedRecordCoherence.entryOf generated).getD ⟨0,.node []⟩
private def generatedBody : Value Nat Bool :=
  match generated with | .mu _ body _ _ => body | _ => .empty
private def generatedDepth : Value Nat Bool :=
  match generated with | .mu _ _ depth _ => depth | _ => .empty
private def generatedOrdinary : Value Nat Bool :=
  match generated with | .mu _ _ _ ordinary => ordinary | _ => .empty
private theorem built_done : built = .done original before := by cbv
private theorem unfolded_done : unfolded = .done next after := by cbv
private theorem ready : SourceEqualityRequiredCache.Ready before :=
  SourceEqualityRequiredCache.constructed source original before built_done
private theorem available : Available before original :=
  (InternedFreshOrdinaryFacts.closed_verified source).result original before built_done
private theorem original_shape : original = .mu originalEntry originalBody originalDepth originalOrdinary := by cbv
private theorem result_entry : InternedRecordCoherence.entryOf next = some resultEntry := by cbv
private theorem result_missing : before.nodeRecords resultEntry.key = none := by cbv
private theorem unavailable : ¬ Available before next := by
  intro present
  have resident := present.resident resultEntry result_entry
  rw [result_missing] at resident
  cases resident
private theorem effects : SourceEqualityRequiredCache.Keeps before after ∧ Available after next ∧
    Nonempty (SourceCurrentNativeMuPublication.History before after) := by
  have bodyAvailable : Available before originalBody :=
    available.children originalBody (by rw [original_shape,children]; exact List.mem_cons_self)
  have replacements : InternedStoredSubstitution.Replacements before
      (fun name => if name = .interned originalEntry.identity then some original else none) := by
    intro name result found
    dsimp only at found
    split at found
    · cases found; exact available
    · cases found
  obtain ⟨result,final,called,kept,output,history⟩ := SourceCurrentStoredReconstruction.execute
    originalBody _ before ready bodyAvailable replacements
  have literal : InternedFreshOrdinaryStoredSubstitution.execute originalBody
      (fun name => if name = .interned originalEntry.identity then some original else none) before =
        .done next after := by
    have done : unfold original before = .done next after := unfolded_done
    simpa only [original_shape,unfold] using done
  obtain ⟨rfl,rfl⟩ := Outcome.done.inj (called.symm.trans literal)
  exact ⟨kept,output,history⟩

private theorem generated_available : Available after generated :=
  effects.2.1.children generated (by cbv; exact List.mem_cons_of_mem _ List.mem_cons_self)
private theorem generated_unavailable : ¬ Available before generated := by
  have entry : InternedRecordCoherence.entryOf generated = some generatedEntry := by cbv
  have missing : before.nodeRecords generatedEntry.key = none := by cbv
  intro available
  have resident := available.resident generatedEntry entry
  rw [missing] at resident
  cases resident
private theorem generated_shape : generated = .mu generatedEntry generatedBody generatedDepth generatedOrdinary := by cbv

private theorem witness_proof :
    build source [] empty = .done original before ∧ SourceEqualityRequiredCache.Ready before ∧
    Available before original ∧ original.free = [] ∧
    InternedFreshOrdinaryDepthHeap.usesLocal originalDepth originalOrdinary = true ∧
    unfold original before = .done next after ∧ SourceEqualityRequiredCache.Keeps before after ∧
    Available after next ∧ ¬ Available before next ∧
    Available after generated ∧ ¬ Available before generated ∧
    generated = .mu generatedEntry generatedBody generatedDepth generatedOrdinary ∧
    InternedFreshOrdinaryDepthHeap.usesLocal generatedDepth generatedOrdinary = true ∧
    Nonempty (SourceCurrentNativeMuPublication.History before after) := by
  exact ⟨built_done,ready,available,by cbv,by cbv,unfolded_done,effects.1,effects.2.1,unavailable,
    generated_available,generated_unavailable,generated_shape,by cbv,effects.2.2⟩

/-- Actual nested used-Mu unfolding can return a value absent from its original ready reader. -/
theorem witness :
    build source [] empty = .done original before ∧ SourceEqualityRequiredCache.Ready before ∧
    Available before original ∧ original.free = [] ∧
    InternedFreshOrdinaryDepthHeap.usesLocal originalDepth originalOrdinary = true ∧
    unfold original before = .done next after ∧ SourceEqualityRequiredCache.Keeps before after ∧
    Available after next ∧ ¬ Available before next ∧
    Available after generated ∧ ¬ Available before generated ∧
    generated = .mu generatedEntry generatedBody generatedDepth generatedOrdinary ∧
    InternedFreshOrdinaryDepthHeap.usesLocal generatedDepth generatedOrdinary = true ∧
    Nonempty (SourceCurrentNativeMuPublication.History before after) := witness_proof

end MicroCFTA.BinderSupportReview
