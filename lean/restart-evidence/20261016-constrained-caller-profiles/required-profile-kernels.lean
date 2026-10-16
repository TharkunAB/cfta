import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryRequiredProfile

namespace RequiredProfileChecks
open MicroCFTA Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open SourceEqualityNeeded SourceEqualityRequiredGraph
open SourceEqualityRequiredCache (Keeps)
open SourceEqualityRequiredSemanticCache (SemanticReady)
open SourceCurrentAllocatedFiniteOrdinaryNativeProfile
open InternedNestedProvenance (Values Edges)
variable {Symbol Guard : Type} {rowLimit arityLimit : Nat}
variable [DecidableEq (EdgeKey Symbol Guard)]

/-- Two actual finite entries retain the same profile at the derived intermediate heap. -/
theorem serial_finite (firstPaths lastPaths : List (List Int)) (values : List (Value Symbol Guard))
    (before : State Symbol Guard) (semantic : SemanticReady before) (available : Values before values)
    (profile : ChildrenShape rowLimit arityLimit values) :
    ∃ middleValues middle results after,
      SourceEqualityRequiredWorkerComplete.StableRun
        (fun fuel readFuel => SourceEqualityRequiredExecution.requireAll fuel readFuel firstPaths values before) middleValues middle ∧
      SourceEqualityRequiredWorkerComplete.StableRun
        (fun fuel readFuel => SourceEqualityRequiredExecution.requireAll fuel readFuel lastPaths middleValues middle) results after ∧
      Keeps before after ∧ SemanticReady after ∧ Values after results ∧
      ChildrenShape rowLimit arityLimit results ∧ results.length = values.length := by
  obtain ⟨middleValues, middle, firstKept, middleSemantic, middleAvailable, middleProfile, firstLength, firstStable⟩ :=
    SourceCurrentAllocatedFiniteOrdinaryRequiredProfile.finite firstPaths values before semantic available profile
  obtain ⟨results, after, lastKept, afterSemantic, resultAvailable, resultProfile, lastLength, lastStable⟩ :=
    SourceCurrentAllocatedFiniteOrdinaryRequiredProfile.finite lastPaths middleValues middle middleSemantic middleAvailable middleProfile
  exact ⟨middleValues, middle, results, after, firstStable, lastStable, firstKept.trans lastKept,
    afterSemantic, resultAvailable, resultProfile, lastLength.trans firstLength⟩

/-- The literal empty path list retains the whole forest and heap at zero worker bounds. -/
theorem zero_bounds_empty_paths (values : List (Value Symbol Guard)) (before : State Symbol Guard)
    (semantic : SemanticReady before) (available : Values before values) (profile : ChildrenShape rowLimit arityLimit values) :
    SourceEqualityRequiredExecution.requireAll 0 0 [] values before = .done values before ∧
      Keeps before before ∧ SemanticReady before ∧ Values before values ∧
      ChildrenShape rowLimit arityLimit values ∧ values.length = values.length := by
  have done := SourceEqualityRequiredExecution.requireAll_identity 0 0 values before
  exact ⟨done, SourceCurrentAllocatedFiniteOrdinaryRequiredProfile.requireAll_done 0 0 [] values values before before
    done semantic available profile⟩

/-- A missing required index rejects the row before any child or constructor graph. -/
theorem nullary_rejection (entry : Interned (EdgeKey Symbol Guard)) (before : State Symbol Guard)
    (semantic : SemanticReady before) (resident : EdgeResident before (.mk entry []))
    (profile : EdgeShape rowLimit arityLimit (.mk entry [])) :
    ∃ _actual : RequireRows [(1, .node [])] [.mk entry []] before [] before,
      Keeps before before ∧ SemanticReady before ∧ Edges before [] ∧
      RowsShape rowLimit arityLimit ([] : List (EdgeValue Symbol Guard)) ∧ ([] : List (EdgeValue Symbol Guard)).length ≤ 1 := by
  have actual : RequireRows [(1, .node [])] [.mk entry []] before [] before := .rejected (by change fits (.node [(1, .node [])]) 0 = false; decide) .nil
  have allResident : Edges before [.mk entry []] := by
    intro edge member
    have same := List.mem_singleton.mp member
    subst edge
    exact resident
  exact ⟨actual, SourceCurrentAllocatedFiniteOrdinaryRequiredProfile.rows actual semantic allResident ⟨profile, True.intro⟩⟩

/-- A selected child and retained row use the literal same-cache raw constructor result. -/
theorem unary_rebuild (entry : Interned (EdgeKey Symbol Guard)) (child : Value Symbol Guard)
    (before : State Symbol Guard) (semantic : SemanticReady before) (resident : EdgeResident before (.mk entry [child]))
    (profile : EdgeShape rowLimit arityLimit (.mk entry [child])) :
    let built := run (makeEdge entry.key.symbol entry.key.constraint [child]) before
    ∃ _actual : RequireRows [(0, .node [])] [.mk entry [child]] before [built.1] built.2,
      Keeps before built.2 ∧ SemanticReady built.2 ∧ Edges built.2 [built.1] ∧
      RowsShape rowLimit arityLimit [built.1] ∧ [built.1].length ≤ [EdgeValue.mk entry [child]].length := by
  let built := run (makeEdge entry.key.symbol entry.key.constraint [child]) before
  have selected : RequireChildren [(0, .node [])] 0 [child] before [child] before :=
    .selected 0 rfl .identity .nil
  have actual : RequireRows [(0, .node [])] [.mk entry [child]] before [built.1] built.2 :=
    .kept (by change fits (.node [(0, .node [])]) 1 = true; decide) selected rfl .nil
  have allResident : Edges before [.mk entry [child]] := by
    intro edge member
    have same := List.mem_singleton.mp member
    subst edge
    exact resident
  exact ⟨actual, SourceCurrentAllocatedFiniteOrdinaryRequiredProfile.rows actual semantic allResident ⟨profile, True.intro⟩⟩

#print axioms serial_finite
#check @serial_finite
#print axioms zero_bounds_empty_paths
#check @zero_bounds_empty_paths
#print axioms nullary_rejection
#check @nullary_rejection
#print axioms unary_rebuild
#check @unary_rebuild
end RequiredProfileChecks
