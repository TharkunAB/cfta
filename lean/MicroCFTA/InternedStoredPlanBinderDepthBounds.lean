import MicroCFTA.InternedStoredPlanBinderDepth
import MicroCFTA.InternedFreshOrdinaryDepthComposition

/-!
# Actual cached-depth bounds on stored-plan binder depth

Coherent available records bound their open plan depth by actual cached
depth. Closed captures can make that bound loose. The repaired ordinary
placeholder therefore also bounds the open depth of its actual probe.
These bounds do not assert that cached depth decreases during unfolding.
-/
namespace MicroCFTA.InternedStoredPlanBinderDepth
open InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedFreshOrdinaryDepthComposition (maximumDepth_cons)
open InternedNormalizationDepthExact (maximumDepth_append)

mutual
/-- An available coherent record's actual cached depth bounds its emitted open binder nesting. -/
theorem value_le_cached (value : Value Symbol Guard) (state : State Symbol Guard)
    (coherent : Coherent state) (available : Available state value) : valueDepth value ≤ value.depth := by
  rw [valueDepth.eq_def]
  split
  · exact Nat.zero_le _
  · cases value with
    | empty | reference => exact Nat.zero_le _
    | node entry edges depth free =>
        obtain ⟨actual, present, fields⟩ := coherent.nodes entry.key _ (available.resident entry rfl)
        have depthExact : depth = maximumDepth (edges.flatMap EdgeValue.children) := fields.2.2.1
        rw [Value.depth, depthExact]
        exact edges_le_cached edges state coherent (fun child member => available.children child member)
    | union entry members depth free =>
        obtain ⟨actual, present, fields⟩ := coherent.nodes entry.key _ (available.resident entry rfl)
        have depthExact : depth = maximumDepth members := fields.2.2.1
        rw [Value.depth, depthExact]
        exact many_le_cached members state coherent (fun child member => available.children child member)
    | mu entry body depth ordinary =>
        have bound := value_le_cached body state coherent (available.children body (by simp [children]))
        rw [Value.depth]
        change 1 + valueDepth body ≤ body.depth + 1
        omega
termination_by sizeOf value

/-- The exact maximum cached depth bounds every ordered available member's open binder nesting. -/
theorem many_le_cached (values : List (Value Symbol Guard)) (state : State Symbol Guard)
    (coherent : Coherent state) (available : ∀ value ∈ values, Available state value) :
    manyDepth values ≤ maximumDepth values := by
  cases values with
  | nil => simp [manyDepth, maximumDepth]
  | cons first rest =>
      rw [manyDepth, maximumDepth_cons]
      have head := value_le_cached first state coherent (available first List.mem_cons_self)
      have tail := many_le_cached rest state coherent (fun value member => available value (List.mem_cons_of_mem _ member))
      omega
termination_by sizeOf values

/-- Actual cached edge-child depth bounds the open nesting of the exact stored edge plan. -/
theorem edges_le_cached (edges : List (EdgeValue Symbol Guard)) (state : State Symbol Guard)
    (coherent : Coherent state) (available : ∀ value ∈ edges.flatMap EdgeValue.children, Available state value) :
    edgesDepth edges ≤ maximumDepth (edges.flatMap EdgeValue.children) := by
  cases edges with
  | nil => simp [edgesDepth, maximumDepth]
  | cons first rest =>
      cases first with
      | mk entry values =>
          rw [edgesDepth, List.flatMap_cons, maximumDepth_append]
          simp only [EdgeValue.children]
          have head := many_le_cached values state coherent
            (fun value member => available value (by simp [EdgeValue.children, member]))
          have tail := edges_le_cached rest state coherent
            (fun value member => available value (by simp [EdgeValue.children, member]))
          omega
termination_by sizeOf edges
end

/-- The actual repaired ordinary placeholder retains the open binder-depth bound of its probe. -/
theorem value_le_ordinaryLevel (value : Value Symbol Guard) (state : State Symbol Guard)
    (coherent : Coherent state) (available : Available state value) :
    valueDepth value ≤ InternedFreshOrdinaryConstruction.ordinaryLevel value :=
  Nat.le_trans (value_le_cached value state coherent available)
    (InternedFreshOrdinaryConstruction.ordinary_depth_bound value)

end MicroCFTA.InternedStoredPlanBinderDepth
