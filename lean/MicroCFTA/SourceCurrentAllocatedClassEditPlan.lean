import MicroCFTA.SourceCurrentEditDomains
import MicroCFTA.SourceEqualitySharedClassEdits

/-!
# Compiler facts for checked single-class edits

The source compiler stores each original natural path as its leaf token.
Coherent nontrivial records derive disjoint proper paths. Selected path
domains derive safety for the literal compiled child map. These facts do
not depend on a native interpreter or a completed edit execution.
-/
namespace MicroCFTA.SourceCurrentAllocatedClassEditPlan
open Language InternedConstructorTemplates
open SourceEqualityEdits SourceEqualityEditLeafPaths SourceCurrentEditDomains
open SourceEqualityProjectionPathDomain

/-- Compile the source class paths in their retained source order. -/
def compiled (record : SourceEqualityClassOrder.Record) : Edits EqualityNormalize.Path :=
  build (SourceEqualityClassEdits.edits record.paths id)

/-- The actual compiler produces a valid signed edit map. -/
theorem compiled_valid (record : SourceEqualityClassOrder.Record) : Valid (compiled record) := build_valid _

/-- Each stored compiled child contains a retained callback. -/
theorem compiled_populated (record : SourceEqualityClassOrder.Record) : Populated (compiled record) := build_populated _

/-- Every compiled callback token is an actual path of the source record. -/
theorem compiled_allowed (record : SourceEqualityClassOrder.Record) :
    SourceEqualitySharedEditEffects.Allowed record (compiled record) :=
  SourceEqualitySharedClassEdits.compiled_allowed record

/-- Coherence derives disjointness of the actual signed input edit pairs. -/
theorem compiled_disjoint (record : SourceEqualityClassOrder.Record) (coherent : SourceEqualityClassOrder.Coherent record) :
    (SourceEqualityClassEdits.edits record.paths id).Pairwise
      (fun first second => SourceEqualityEditCompiledPaths.Disjoint first.1 second.1) :=
  SourceEqualityClassEdits.edits_disjoint record.paths (SourceEqualityClassEdits.coherent_supported record coherent) id

/-- Coherence and nontriviality derive proper original signed edit paths. -/
theorem compiled_nonroot (record : SourceEqualityClassOrder.Record) (coherent : SourceEqualityClassOrder.Coherent record)
    (active : EqualityNormalize.Nontrivial record.paths) :
    ∀ path action, (path, action) ∈ SourceEqualityClassEdits.edits record.paths id → path ≠ [] :=
  SourceEqualityClassEdits.edits_nonroot record.paths
    (SourceEqualityClassEdits.supported_nonroot record.paths (SourceEqualityClassEdits.coherent_supported record coherent) active) id

/-- A coherent nontrivial source record cannot compile to a list-root leaf. -/
theorem compiled_not_leaf (record : SourceEqualityClassOrder.Record) (coherent : SourceEqualityClassOrder.Coherent record)
    (active : EqualityNormalize.Nontrivial record.paths) (token : EqualityNormalize.Path) :
    compiled record ≠ .editAt token :=
  SourceEqualityEditCompiledPaths.build_not_leaf _ (compiled_disjoint record coherent)
    (compiled_nonroot record coherent active) token

/-- The literal class compiler returns a child map at the list root. -/
theorem compiled_children (record : SourceEqualityClassOrder.Record) (coherent : SourceEqualityClassOrder.Coherent record)
    (active : EqualityNormalize.Nontrivial record.paths) :
    ∃ entries, compiled record = .editBelow entries := by
  cases built : compiled record with
  | editAt token => exact False.elim (compiled_not_leaf record coherent active token built)
  | editBelow entries => exact ⟨entries, rfl⟩

/-- Original selected path domains supply safety at each actual compiled child lookup. -/
theorem compiled_safe (record : SourceEqualityClassOrder.Record) (coherent : SourceEqualityClassOrder.Coherent record)
    (values : List (Value Symbol Guard))
    (domains : ∀ path ∈ record.paths, ForestClosed (path.map Int.ofNat) values)
    (entries : List (Int × Edits EqualityNormalize.Path)) (built : compiled record = .editBelow entries) :
    ChildrenSafe entries 0 values := by
  intro query child found value selected path action retained
  have member : (Int.ofNat query :: path, action) ∈ leaves (compiled record) := by
    rw [built]
    exact below_member _ _ _ (SourceEqualityNeededMap.lookup_mem _ _ _ (by simpa using found)) _ _ retained
  have original := (SourceEqualityEditCompiledPaths.build_leaves _ (compiled_disjoint record coherent)).mem_iff.mp member
  obtain ⟨natural, included, same⟩ := List.mem_map.mp original
  have domain := domains natural included
  have samePath := congrArg Prod.fst same
  dsimp at samePath
  rw [samePath] at domain
  apply domain value
  change SourceEqualityProjectionGraph.select values (Int.ofNat query) = some value
  rw [SourceCurrentEditDomains.select_natural]
  exact selected

/-- Compiled leaf tokens have their exact original natural-path lookup condition. -/
theorem compiled_condition (record : SourceEqualityClassOrder.Record) (coherent : SourceEqualityClassOrder.Coherent record)
    (active : EqualityNormalize.Nontrivial record.paths) (symbol : Symbol) (terms : List (Term Symbol)) :
    SourceEqualityEditAPI.ListCondition (fun path part => (Term.node symbol terms).atPath path = some part)
      (compiled record) terms := by
  apply (SourceEqualityEditCompiledPaths.list_condition_exact _ _ (compiled_disjoint record coherent)
    (compiled_nonroot record coherent active) symbol terms).mpr
  exact (SourceEqualityClassEdits.conditions_exact _ record.paths id (.node symbol terms)).mpr
    (fun _ _ _ selected => selected)

end MicroCFTA.SourceCurrentAllocatedClassEditPlan
