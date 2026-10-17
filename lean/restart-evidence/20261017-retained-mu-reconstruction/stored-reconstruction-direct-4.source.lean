import MicroCFTA.SourceEqualityRequiredCache
import MicroCFTA.SourceCurrentNativeMuPublication

/-!
# Complete stored reconstruction with local publication history

Initial ready caches complete arbitrary repaired stored substitution.
The exact returned heap retains open-depth observations and its local
publication history. A selected Mu supplies both reconstruction payloads
from its actual stored record. The theorem does not compare the two reconstructed results.
-/
namespace MicroCFTA.SourceCurrentStoredReconstruction
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedConstruction (Outcome)
open InternedStoredSubstitution (Environment Replacements leaves input encode inputs_available)
open InternedBinderProtocol (Reference NodeKey)
open SourceEqualityRequiredCache (Ready Keeps)
open SourceCurrentNativeMuPublication (History)

/-- Initial ready data completes repaired substitution and retains its exact local history. -/
theorem execute [DecidableEq (EdgeKey Symbol Guard)] (value : Value Symbol Guard)
    (environment : Environment Symbol Guard) (before : State Symbol Guard) (ready : Ready before)
    (available : Available before value) (replacements : Replacements before environment) :
    ∃ result after, InternedFreshOrdinaryStoredSubstitution.execute value environment before = .done result after ∧
      Keeps before after ∧ Available after result ∧ Nonempty (History before after) := by
  obtain ⟨result, after, done, context, heap, covered, output, growth, issued⟩ :=
    InternedFreshOrdinaryStoredSubstitution.execute_complete_decoded value environment before
      ready.semantic.1 available replacements ready.semantic.2 ready.covered
  have sourceContext : InternedFreshOrdinaryContext.Context before ((leaves value).map (input environment)) :=
    ⟨ready.semantic.1.normal, inputs_available value environment before available replacements,
      ready.semantic.1.profiles, ready.semantic.1.freeNames⟩
  have depth := InternedOpenDepthExecution.build_depth (encode (leaves value) [] value) _ before
    sourceContext ready.semantic.2 ready.depth
  have retained : InternedOpenDepthReadback.Heap after := by
    have same := depth.heap
    change InternedOpenDepthReadback.Heap (InternedFreshOrdinaryStoredSubstitution.execute value environment before).state at same
    simpa only [done, Outcome.state] using same
  have history := SourceCurrentNativeMuPublication.build_history (encode (leaves value) [] value) _ before
    ⟨sourceContext, ready.semantic.2⟩
  change Nonempty (History before (InternedFreshOrdinaryStoredSubstitution.execute value environment before).state) at history
  exact ⟨result, after, done, ⟨⟨⟨context, heap⟩, covered, retained⟩, growth, issued⟩,
    output, by simpa only [done, Outcome.state] using history⟩

/-- An actual stored Mu supplies two complete sequential reconstructions with the same replacement. -/
theorem mu [DecidableEq (EdgeKey Symbol Guard)] (key : NodeKey) (entry : Interned NodeKey)
    (body depth ordinary replacement : Value Symbol Guard) (before : State Symbol Guard)
    (ready : Ready before) (present : before.nodeRecords key = some (.mu entry body depth ordinary))
    (replacementAvailable : Available before replacement) :
    ∃ left middle right after,
      InternedFreshOrdinaryStoredSubstitution.execute body
        (fun name => if name = .interned entry.identity then some replacement else none) before = .done left middle ∧
      InternedFreshOrdinaryStoredSubstitution.execute ordinary
        (fun name => if name = .uninterned (InternedFreshOrdinaryConstruction.ordinaryLevel depth)
          then some replacement else none) middle = .done right after ∧
      Keeps before middle ∧ Keeps middle after ∧
      Available after left ∧ Available after right ∧
      Nonempty (History before middle) ∧ Nonempty (History middle after) ∧
      after.nodeRecords key = some (.mu entry body depth ordinary) := by
  have selected := ready.semantic.1.normal.facts.cached.nodes key _ present
  have bodyAvailable : Available before body := selected.children body (by simp [children])
  have ordinaryAvailable : Available before ordinary := selected.children ordinary (by simp [children])
  obtain ⟨left, middle, bodyDone, first, leftAvailable, firstHistory⟩ :=
    execute body (fun name => if name = .interned entry.identity then some replacement else none)
      before ready bodyAvailable (by
      intro name value found
      dsimp only at found
      split at found
      · cases found
        exact replacementAvailable
      · cases found)
  obtain ⟨right, after, ordinaryDone, second, rightAvailable, secondHistory⟩ :=
    execute ordinary (fun name => if name = .uninterned (InternedFreshOrdinaryConstruction.ordinaryLevel depth)
      then some replacement else none) middle first.ready (first.available ordinary ordinaryAvailable) (by
      intro name value found
      dsimp only at found
      split at found
      · cases found
        exact first.available replacement replacementAvailable
      · cases found)
  exact ⟨left, middle, right, after, bodyDone, ordinaryDone, first, second,
    second.available left leftAvailable, rightAvailable, firstHistory, secondHistory,
    second.growth.nodeRecords key _ (first.growth.nodeRecords key _ present)⟩

end MicroCFTA.SourceCurrentStoredReconstruction
