import MicroCFTA.InternedUnionCompletion
import MicroCFTA.InternedNestedConstructionExamples

/-!
# Unbounded root-union and consecutive-binder completion

Every level retains its inputs as bare union alternatives. Root self
filtering can remove an alternative and expose a singleton. The actual
first construction still completes at every finite nesting depth.
-/
namespace MicroCFTA.InternedUnionCompletionExamples
open InternedConstructorTemplates InternedNestedConstruction InternedNestedFacts InternedNestedProvenance
open InternedRecordCoherence InternedProbeProvenance InternedNestedCoverage InternedUnionReferences InternedUnionConstruction

/-- Every lexical input occurs as a bare source union alternative. -/
def vars (depth : Nat) : List (Syntax Nat Unit) := (List.range depth).map Syntax.var

/-- All declared alternatives satisfy the recursive source admission rule. -/
theorem vars_retentive (depth count : Nat) : ManyRetentive depth (vars count) := by
  have all : ∀ indices : List Nat, ManyRetentive depth (indices.map (Syntax.var (Symbol := Nat) (Guard := Unit))) := by
    intro indices
    induction indices with
    | nil => simp [ManyRetentive]
    | cons first rest ih => simpa only [List.map_cons, ManyRetentive, Retentive] using And.intro True.intro ih
  exact all _

/-- Each source variable has its exact range membership. -/
theorem var_member (index depth : Nat) (bound : index < depth) : Syntax.var index ∈ vars depth :=
  List.mem_map.mpr ⟨index, List.mem_range.mpr bound, rfl⟩

/-- Sequential source operands preserve recursive admission. -/
theorem retentive_append (depth : Nat) (first second : List (Syntax Nat Unit))
    (left : ManyRetentive depth first) (right : ManyRetentive depth second) : ManyRetentive depth (first ++ second) := by
  induction first with
  | nil => exact right
  | cons head rest ih =>
      simp only [ManyRetentive] at left
      simpa only [List.cons_append, ManyRetentive] using And.intro left.1 (ih left.2)

/-- A source root union retains all visible inputs before constructing the next nested binder. -/
def chain (smart : Bool) (depth : Nat) : Nat → Syntax Nat Unit
  | 0 => .var 0
  | count + 1 => .binder smart (.union (vars (depth + 1) ++ [chain smart (depth + 1) count]))

/-- Each nested depth has source declarations for all enclosing pending names. -/
theorem chain_retentive (smart : Bool) (depth count : Nat) : Retentive depth (chain smart depth count) := by
  induction count generalizing depth with
  | zero => simp [chain, Retentive]
  | succ count ih =>
      simp only [chain, Retentive]
      constructor
      · intro index bound
        exact .union _ (.var (index + 1)) (List.mem_append_left _ (var_member _ _ (by omega))) .var
      · apply retentive_append _ _ _ (vars_retentive _ _)
        simpa only [ManyRetentive] using And.intro (ih (depth + 1)) True.intro

/-- Every range alternative reads an actual source input. -/
theorem vars_scoped (depth : Nat) : ManyScoped depth (vars depth) := by
  have all : ∀ indices : List Nat, (∀ index ∈ indices, index < depth) →
      ManyScoped depth (indices.map (Syntax.var (Symbol := Nat) (Guard := Unit))) := by
    intro indices bounds
    induction indices with
    | nil => simp [ManyScoped]
    | cons first rest ih =>
        simp only [List.map_cons, ManyScoped, Scoped]
        exact ⟨bounds first (by simp), ih (fun index member => bounds index (by simp [member]))⟩
  exact all _ (fun index member => List.mem_range.mp member)

/-- Appended source alternatives retain the same lexical scope. -/
theorem scoped_append (depth : Nat) (first second : List (Syntax Nat Unit))
    (left : ManyScoped depth first) (right : ManyScoped depth second) : ManyScoped depth (first ++ second) := by
  induction first with
  | nil => exact right
  | cons head rest ih =>
      simp only [ManyScoped] at left
      simpa only [List.cons_append, ManyScoped] using And.intro left.1 (ih left.2)

/-- At least one actual binder supplies the innermost variable. -/
theorem chain_scoped (smart : Bool) (depth count : Nat) (positive : 0 < depth + count) : Scoped depth (chain smart depth count) := by
  induction count generalizing depth with
  | zero => simpa [chain, Scoped] using positive
  | succ count ih =>
      simp only [chain, Scoped]
      apply scoped_append _ _ _ (vars_scoped _)
      simpa only [ManyScoped] using And.intro (ih (depth + 1) (by omega)) True.intro

/-- Closed root-union programs include arbitrarily many active nested source binders. -/
def program (smart : Bool) (count : Nat) : Syntax Nat Unit := chain smart 0 (count + 1)

/-- Every member of the unbounded source family is lexically closed. -/
theorem program_scoped (smart : Bool) (count : Nat) : Scoped 0 (program smart count) :=
  chain_scoped smart 0 (count + 1) (by omega)

/-- Actual first execution derives complete records and exact replay for both constructor modes. -/
theorem program_complete (smart : Bool) (count : Nat) :
    ∃ value final, build (program smart count) [] empty = .done value final ∧
      Facts final ∧ Covered [] final ∧ Available final value ∧
      ∀ after, Grows final after → build (program smart count) [] after = .done value after := by
  obtain ⟨value, final, completed⟩ := closed_completes (program smart count) (chain_retentive smart 0 (count + 1))
  have verified := closed_verified (program smart count)
  refine ⟨value, final, completed, ?_, closed_covered _ value final completed,
    verified.result value final completed, fun after growth => empty_replay _ value final after completed growth⟩
  simpa only [completed, Outcome.state] using verified.facts

/-- No finite root-union chain can return a pending canonical request. -/
theorem program_not_pending (smart : Bool) (count : Nat) (key : InternedBinderProtocol.NodeKey) (state : State Nat Unit) :
    build (program smart count) [] empty ≠ .pending key state := by
  obtain ⟨value, final, completed, _⟩ := program_complete smart count
  rw [completed]
  intro impossible
  cases impossible

/-- Consecutive nested binders satisfy the source declaration even before an ordinary node occurs. -/
theorem selfUnion_retentive : Retentive 0 InternedNestedConstructionExamples.selfUnion := by
  simp only [InternedNestedConstructionExamples.selfUnion, Retentive, ManyRetentive]
  refine ⟨?_, ?_, trivial, trivial, trivial⟩
  · intro index impossible; omega
  · intro index bound
    have same : index = 0 := by omega
    subst index
    exact .union _ (.var 1) (by simp) .var

/-- The consecutive-binder fixture now follows from source completion instead of finite kernel evaluation. -/
theorem selfUnion_complete : ∃ value final,
    build InternedNestedConstructionExamples.selfUnion [] empty = .done value final :=
  closed_completes _ selfUnion_retentive

end MicroCFTA.InternedUnionCompletionExamples
