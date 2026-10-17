import MicroCFTA.SourceCurrentConstrainedCapPaths

set_option linter.all true
set_option pp.explicit true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 1000000
set_option pp.fullNames true

namespace ConstrainedCapPathsChecks
open MicroCFTA
open InternedConstructorTemplates SourceEqualityAnnotationLanguage
open SourceCurrentConstrainedCap SourceCurrentConstrainedCapPaths SourceEqualityProjectionGraph
variable {Symbol Guard : Type}

/-- Original cap depths and original path lengths derive all literal other-path masks. -/
theorem original_class_targets (valid : Guard → Prop) (depth : Nat) (values : List (Value Symbol Guard))
    (bounded : ∀ value ∈ values, Cap valid depth value) (paths : EqualityNormalize.Class)
    (long : ∀ path ∈ paths, depth + 1 ≤ path.length) (selected : EqualityNormalize.Path) :
    ∀ path ∈ SourceEqualityClassTarget.operandPaths paths selected, ForestSupported valid path values := by
  apply operand_paths valid paths selected values
  intro path member
  have enough := long path member
  cases path with
  | nil => simp only [List.length_nil] at enough; omega
  | cons index path =>
      exact forest_of_cap valid depth values bounded (Int.ofNat index) (path.map Int.ofNat)
        (by simp only [List.length_map, List.length_cons] at enough ⊢; omega)

/-- Actual selected rows consume the original cap layer before returning endpoints. -/
theorem actual_selected_rows [DecidableEq (EdgeKey Symbol Guard)] (valid : Guard → Prop)
    (entry) (edges : List (EdgeValue Symbol Guard)) (depth free)
    (bounded : Cap valid 1 (.node entry edges depth free)) (index : Int)
    (before after : State Symbol Guard) (results : List (Value Symbol Guard))
    (actual : ProjectRows [] index edges before results after) : ∀ value ∈ results, Annotated valid value := by
  have mask := of_cap bounded [index] (by simp)
  exact project_rows_root valid actual (fun edge member child found => mask.node_selected edge member child found)

/-- Finite cap membership alone does not make a short actual projection hereditary. -/
theorem short_endpoint_counterexample [DecidableEq (EdgeKey Symbol Guard)] (valid : Guard → Prop)
    (entry : Cache.Interned InternedBinderProtocol.NodeKey) (edgeEntry : Cache.Interned (EdgeKey Symbol Guard))
    (invalid : ¬ valid edgeEntry.key.constraint) (state : State Symbol Guard) :
    let value : Value Symbol Guard := .node entry [.mk edgeEntry []] 0 []
    Cap valid 1 value ∧ Project [] value state value state ∧ ¬ Supported valid [] value := by
  dsimp only
  refine ⟨Cap.node 0 entry [.mk edgeEntry []] 0 [] ?_, .root, ?_⟩
  · intro child member
    simp only [List.flatMap_cons, List.flatMap_nil, List.nil_append, EdgeValue.children] at member
    cases member
  · exact root_guard_obstruction valid entry [.mk edgeEntry []] 0 [] (.mk edgeEntry []) List.mem_cons_self invalid

/-- A hereditary Mu boundary accepts paths of unequal length without an ordinary-height claim. -/
theorem recursive_boundary (valid : Guard → Prop) (entry) (body depth ordinary : Value Symbol Guard)
    (bodyPlain : Annotated valid body) (first second : List Int) :
    Supported valid first (.mu entry body depth ordinary) ∧
      Supported valid second (.mu entry body depth ordinary) :=
  ⟨.plain first (.mu entry body depth ordinary bodyPlain), .plain second (.mu entry body depth ordinary bodyPlain)⟩

/-- A negative forest position has an actual Empty return and no endpoint obligation. -/
theorem negative_missing [DecidableEq (EdgeKey Symbol Guard)] (valid : Guard → Prop)
    (values : List (Value Symbol Guard)) (path : List Int) (state : State Symbol Guard) :
    ForestSupported valid (-1 :: path) values ∧ Forest (-1 :: path) values state .empty state := by
  have missing : select values (-1) = none := by simp only [select]; decide
  exact ⟨forest_missing valid values (-1) path missing, .missing missing⟩

/-- Reference annotation cannot conceal the unresolved nonempty projection branch. -/
theorem reference_boundary [DecidableEq (EdgeKey Symbol Guard)] (valid : Guard → Prop) (index : Int)
    (path : List Int) (name) (before after : State Symbol Guard) (result : Value Symbol Guard) :
    Supported valid (index :: path) (.reference name) ∧
      ¬ Project (index :: path) (.reference name) before result after :=
  ⟨SourceCurrentConstrainedCapPaths.reference valid _ name, no_reference_project index path name before after result⟩

end ConstrainedCapPathsChecks

#print axioms ConstrainedCapPathsChecks.original_class_targets
#check @ConstrainedCapPathsChecks.original_class_targets
#print axioms ConstrainedCapPathsChecks.actual_selected_rows
#check @ConstrainedCapPathsChecks.actual_selected_rows
#print axioms ConstrainedCapPathsChecks.short_endpoint_counterexample
#check @ConstrainedCapPathsChecks.short_endpoint_counterexample
#print axioms ConstrainedCapPathsChecks.recursive_boundary
#check @ConstrainedCapPathsChecks.recursive_boundary
#print axioms ConstrainedCapPathsChecks.negative_missing
#check @ConstrainedCapPathsChecks.negative_missing
#print axioms ConstrainedCapPathsChecks.reference_boundary
#check @ConstrainedCapPathsChecks.reference_boundary
