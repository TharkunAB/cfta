import MicroCFTA.SourceCurrentStoredReconstruction
import MicroCFTA.SourceCurrentStoredSubstitutionOrigins
import MicroCFTA.SourceCurrentOpenObservationConstructors
import MicroCFTA.InternedNormalizationFree

/-!
# Open observations of actual stored union reconstruction

Initial ready data completes the union and each original member call.
The calls retain their source order and exact intermediate heaps. The
union result has the same finite open observations as those member
results in every fixed view. Closed roots retain their exact stored value.
The theorem does not compare reconstruction after an earlier makeUnion.
-/
namespace MicroCFTA.SourceCurrentStoredUnionObservations
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedConstruction (Outcome)
open InternedNestedProvenance (Values)
open InternedStoredSubstitution (Environment Replacements leaves input encode)
open InternedFreshOrdinaryConstruction (build)
open InternedFreshOrdinaryStoredSubstitution (execute)
open InternedBinderProtocol (NodeKey Reference)
open SourceCurrentStoredSubstitutionCalls (Calls)
open SourceEqualityRequiredCache (Ready Keeps)
open SourceCurrentOpenObservations (Same)

/-- Actual repaired substitution retains a closed value and its exact heap. -/
theorem closed [DecidableEq (EdgeKey Symbol Guard)] (value : Value Symbol Guard)
    (environment : Environment Symbol Guard) (before : State Symbol Guard) (noFree : value.free = []) :
    execute value environment before = .done value before := by
  unfold execute
  have captured : leaves value = [value] := by
    rw [leaves.eq_def]
    simp only [noFree, List.isEmpty_nil, ite_true]
  rw [captured]
  have encoded : encode [value] [] value = .var 0 := by
    rw [encode.eq_def]
    simp [noFree, InternedStoredSubstitution.slot]
  rw [encoded]
  simpa only [List.map_cons, List.map_nil, build, List.getElem?_cons_zero, Option.getD_some] using
    congrArg (fun result => (Outcome.done result before : Outcome Symbol Guard (Value Symbol Guard)))
      (InternedStoredSubstitutionScope.input_closed value environment noFree)

/-- Initial ready values construct the ordered member calls and retain their complete cache effects. -/
theorem members [DecidableEq (EdgeKey Symbol Guard)] (originals : List (Value Symbol Guard))
    (environment : Environment Symbol Guard) (before : State Symbol Guard) (ready : Ready before)
    (available : Values before originals) (replacements : Replacements before environment) :
    ∃ values after, Calls environment originals before values after ∧
      Keeps before after ∧ Values after values := by
  induction originals generalizing before with
  | nil => exact ⟨[],before,.nil before,SourceEqualityRequiredCache.pure_keeps before ready,by intro value member; cases member⟩
  | cons original originals ih =>
      obtain ⟨value,middle,actual,first,output,_⟩ :=
        SourceCurrentStoredReconstruction.execute original environment before ready
          (available original List.mem_cons_self) replacements
      obtain ⟨values,after,rest,last,outputs⟩ := ih middle first.ready
        (fun value member => first.available value (available value (List.mem_cons_of_mem _ member)))
        (fun name value found => first.available value (replacements name value found))
      refine ⟨value::values,after,.cons original originals before middle after value values actual rest,first.trans last,?_⟩
      intro selected present
      rcases List.mem_cons.mp present with rfl | member
      · exact last.available selected output
      · exact outputs selected member

private theorem calls_unique [DecidableEq (EdgeKey Symbol Guard)] {environment : Environment Symbol Guard}
    {originals values other : List (Value Symbol Guard)} {before after final : State Symbol Guard}
    (first : Calls environment originals before values after) (second : Calls environment originals before other final) :
    values = other ∧ after = final := by
  induction first generalizing other final with
  | nil => cases second; exact ⟨rfl,rfl⟩
  | cons original originals before middle after value values actual rest ih =>
      cases second with
      | cons _ _ _ next final output outputs done later =>
          obtain ⟨rfl,rfl⟩ := Outcome.done.inj (actual.symm.trans done)
          obtain ⟨rfl,rfl⟩ := ih later
          exact ⟨rfl,rfl⟩

private theorem closed_calls [DecidableEq (EdgeKey Symbol Guard)] (originals : List (Value Symbol Guard))
    (environment : Environment Symbol Guard) (before : State Symbol Guard)
    (noFree : ∀ value ∈ originals, value.free = []) : Calls environment originals before originals before := by
  induction originals with
  | nil => exact .nil before
  | cons original originals ih =>
      exact .cons original originals before before before original originals
        (closed original environment before (noFree original List.mem_cons_self))
        (ih (fun value member => noFree value (List.mem_cons_of_mem _ member)))

/-- Initial ready union data constructs its actual return and all original member calls with the same open observations. -/
theorem complete [DecidableEq (EdgeKey Symbol Guard)] (entry : Interned NodeKey)
    (originals : List (Value Symbol Guard)) (level : Nat) (free : List Reference)
    (environment : Environment Symbol Guard) (before : State Symbol Guard) (ready : Ready before)
    (available : Available before (.union entry originals level free)) (replacements : Replacements before environment) :
    ∃ result after values middle,
      execute (.union entry originals level free) environment before = .done result after ∧
      Calls environment originals before values middle ∧
      Keeps before after ∧ Keeps before middle ∧ Available after result ∧ Values middle values ∧
      Grows middle after ∧ ∀ depth view, Same depth view [result] values := by
  have inputs : Values before originals := fun value member => available.children value member
  by_cases noFree : free = []
  · have fields := InternedNormalizationFree.union_free before ready.semantic.1.normal.facts.coherent
      entry originals level free available.resident
    have closedMembers : ∀ value ∈ originals, value.free = [] := by
      intro value member
      apply List.eq_nil_iff_forall_not_mem.mpr
      intro name named
      have included := (childFree_member originals name).mpr ⟨value,member,named⟩
      rw [←fields,noFree] at included
      cases included
    exact ⟨.union entry originals level free,before,originals,before,
      closed _ environment before noFree,closed_calls originals environment before closedMembers,
      SourceEqualityRequiredCache.pure_keeps before ready,SourceEqualityRequiredCache.pure_keeps before ready,
      available,inputs,grows_refl _,fun depth view => SourceCurrentOpenObservations.union depth view entry originals level free⟩
  · have opened : free.isEmpty = false := by simpa only [List.isEmpty_eq_false_iff] using noFree
    obtain ⟨result,after,actual,kept,output,_⟩ :=
      SourceCurrentStoredReconstruction.execute (.union entry originals level free) environment before ready available replacements
    obtain ⟨values,middle,calls,made,_⟩ := SourceCurrentStoredSubstitutionOrigins.union entry originals level free
      environment before ready.semantic.1.normal available replacements opened result after actual
    obtain ⟨produced,memberAfter,memberCalls,memberKept,memberAvailable⟩ := members originals environment before ready inputs replacements
    obtain ⟨rfl,rfl⟩ := calls_unique calls memberCalls
    have increase : Grows middle after := by
      simpa only [made] using (run_correct (makeUnion values) middle memberKept.ready.semantic.1.normal.facts.coherent.valid).2
    refine ⟨result,after,values,middle,actual,calls,kept,memberKept,output,memberAvailable,increase,?_⟩
    intro depth view
    have observed := SourceCurrentOpenObservationConstructors.makeUnion_normalize depth middle view
      memberKept.ready.semantic.1.normal.facts memberKept.ready.semantic.1.normal.live values memberAvailable
    simpa only [made] using observed

end MicroCFTA.SourceCurrentStoredUnionObservations
