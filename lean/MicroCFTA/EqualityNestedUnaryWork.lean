import MicroCFTA.EqualityNestedUnaryCompile

/-!
# Finite constructor work for nested endpoint intersection

The existing path worker consumes finite constructor work. The nested
endpoint schedule consumes a state action. These definitions have the same
source requests and exact returned caches in both interfaces.
-/
namespace MicroCFTA.EqualityNestedUnaryWork
open SourceGuards FullSyntax InternedConstructorTemplates InternedRecordCoherence
open EqualityNestedUnaryCarrier EqualityNestedUnaryChild EqualityNestedUnaryProduct
open EqualityLeafProjectionWorkers (sequence sequence_safe)

noncomputable local instance : DecidableEq ConstraintKey := by classical exact inferInstance

/-- Mapping finite constructor work is exactly its ordered source action. -/
theorem map_work [DecidableEq (EdgeKey Symbol Residual)] (call : Input → Work Symbol Residual Output)
    (inputs : List Input) (state : State Symbol Residual) :
    MergedColdMerge.map (fun input => MergedColdMerge.work (call input)) inputs state =
      MergedColdMerge.work (sequence (inputs.map call)) state := by
  induction inputs generalizing state with
  | nil => rfl
  | cons first rest ih =>
      simp only [MergedColdMerge.map, MergedColdMerge.bind, MergedColdMerge.work,
        MergedSourceComparison.Result.bind, List.map_cons, sequence, run_bind, run,
        MergedColdMerge.pure]
      rw [ih]
      rfl

/-- The finite Cartesian worker retains the actual source hash-join order. -/
noncomputable def product (first second : Value (Fin symbols) ConstraintKey) :
    Work (Fin symbols) ConstraintKey (Value (Fin symbols) ConstraintKey) :=
  (sequence ((pairs first second).map fun pair => edgeMeet pair.1 pair.2)).bind makeNode

/-- The finite whole-node worker uses the same identity and orientation branches. -/
noncomputable def meet (first second : Value (Fin symbols) ConstraintKey) :
    Work (Fin symbols) ConstraintKey (Value (Fin symbols) ConstraintKey) :=
  if first.referenceOf = second.referenceOf then .pure first
  else if EqualityRawLeafProduct.swap first second then product second first else product first second

/-- Finite Cartesian work preserves the full action outcome without assumptions. -/
theorem product_eq (first second : Value (Fin symbols) ConstraintKey) (state : State (Fin symbols) ConstraintKey) :
    MergedColdMerge.work (product first second) state = EqualityNestedUnaryProduct.product first second state := by
  simp only [product, EqualityNestedUnaryProduct.product, MergedColdMerge.bind,
    map_work, MergedColdMerge.work, run_bind, MergedSourceComparison.Result.bind]

/-- Finite nested intersection preserves the full action outcome without assumptions. -/
theorem meet_eq (first second : Value (Fin symbols) ConstraintKey) (state : State (Fin symbols) ConstraintKey) :
    MergedColdMerge.work (meet first second) state = EqualityNestedUnaryMeet.meet first second state := by
  unfold meet EqualityNestedUnaryMeet.meet
  split
  · rfl
  · split <;> exact product_eq _ _ state

/-- Nullary child intersections use only safe source constructors. -/
theorem child_safe (first second : Value (Fin symbols) ConstraintKey) : Safe (childMeet first second) := by
  have productSafe (left right : Value (Fin symbols) ConstraintKey) : Safe (EqualityLeafProjectionProduct.product left right) :=
    safe_bind _ _ (sequence_safe _ (EqualityLeafProjectionNullary.requests_safe _)) makeNode_safe
  unfold childMeet
  split
  · trivial
  · split <;> exact productSafe _ _

/-- A nested Cartesian row uses the actual safe child and edge requests. -/
theorem edge_safe (first second : EdgeValue (Fin symbols) ConstraintKey) : Safe (edgeMeet first second) := by
  unfold edgeMeet
  split
  · apply safe_bind _ _ (sequence_safe _ ?_) (fun children => makeEdge_safe _ _ children)
    intro request member
    obtain ⟨pair, _, rfl⟩ := List.mem_map.mp member
    exact child_safe pair.1 pair.2
  · exact makeEdge_safe _ _ _

/-- Nested product construction meets the ordinary path worker's safety condition. -/
theorem product_safe (first second : Value (Fin symbols) ConstraintKey) : Safe (product first second) := by
  unfold product
  apply safe_bind _ _ (sequence_safe _ ?_) makeNode_safe
  intro request member
  obtain ⟨pair, _, rfl⟩ := List.mem_map.mp member
  exact edge_safe pair.1 pair.2

/-- Every source identity and orientation branch preserves constructor coherence. -/
theorem meet_safe (first second : Value (Fin symbols) ConstraintKey) : Safe (meet first second) := by
  unfold meet
  split
  · trivial
  · split <;> exact product_safe _ _

/-- Empty endpoint occurrences remain empty with no constructor effect. -/
theorem meet_empty_left (value : Value (Fin symbols) ConstraintKey) (state : State (Fin symbols) ConstraintKey) :
    run (meet .empty value) state = (.empty, state) := by
  have same := (meet_eq .empty value state).trans (EqualityNestedUnaryMeet.meet_empty_left value state)
  exact Prod.ext (MergedSourceComparison.Result.done.inj same).1 (MergedSourceComparison.Result.done.inj same).2

end MicroCFTA.EqualityNestedUnaryWork
