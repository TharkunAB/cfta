import MicroCFTA.SourceCurrentHereditaryTypeRouteConstructors
import MicroCFTA.SourceCurrentAllocatedClassEditPlan

/-!
# Type routes for retained edit leaves

The certificates concern the actual retained paths of the edit trie.
Ordinary descent selects only the requested row children. Recursive
inputs require a retained leaf before a route implies their annotation.
Populated subtrees derive that witness at an actual child lookup.
The empty root trie remains permitted and supplies no annotation fact.
These pure laws do not establish worker completion or later role closure.
-/
namespace MicroCFTA.SourceCurrentHereditaryTypeEditPlan
open Cache InternedConstructorTemplates InternedProbeProvenance
open SourceEqualityAnnotationLanguage (Annotated)
open SourceEqualityEdits SourceEqualityEditLeafPaths
open SourceEqualityNeededMap (lookup lookup_mem)
open SourceEqualityProjectionGraph (select select_member)
open SourceCurrentEditDomains (HasLeaf Populated select_natural)
open SourceCurrentHereditaryTypePaths (TypePath ForestPath)
variable {Symbol Guard Action : Type}

/-- Each retained node-edit path has a structural Type route in the input. -/
def NodePaths (valid : Guard → Prop) (edits : Edits Action) (value : Value Symbol Guard) : Prop :=
  ∀ path token, (path, token) ∈ leaves edits → TypePath valid path value

/-- Each retained list-edit path has its structural route in the captured forest. -/
def ForestPaths (valid : Guard → Prop) (edits : Edits Action) (values : List (Value Symbol Guard)) : Prop :=
  ∀ path token, (path, token) ∈ leaves edits → ForestPath valid path values

/-- Child traversal retains its literal offset and exact selected subtree. -/
def ChildrenPaths (valid : Guard → Prop) (entries : List (Int × Edits Action))
    (offset : Nat) (values : List (Value Symbol Guard)) : Prop :=
  ∀ query edits, lookup (Int.ofNat (offset + query)) entries = some edits →
    ∀ value, values[query]? = some value → NodePaths valid edits value

/-- A node leaf route requires the input itself to be annotated. -/
theorem leaf_annotated {valid : Guard → Prop} {token : Action} {value : Value Symbol Guard}
    (routes : NodePaths valid (.editAt token) value) : Annotated valid value :=
  SourceCurrentHereditaryTypeRouteConstructors.route_nil
    (routes [] token (by simp [leaves]))

/-- Every original ordinary row supplies the selected child routes. -/
theorem node_to_children {valid : Guard → Prop} {entries : List (Int × Edits Action)}
    {entry : Interned InternedBinderProtocol.NodeKey} {rows : List (EdgeValue Symbol Guard)}
    {depth : Nat} {free : List InternedBinderProtocol.Reference}
    (routes : NodePaths valid (.editBelow entries) (.node entry rows depth free))
    (row : EdgeValue Symbol Guard) (member : row ∈ rows) : ChildrenPaths valid entries 0 row.children := by
  intro query edits found value selected path token retained
  have retainedParent := below_member entries (Int.ofNat query) edits
    (lookup_mem _ _ _ (by simpa only [Nat.zero_add] using found)) path token retained
  exact SourceCurrentHereditaryTypeRouteConstructors.ordinary_children (routes _ _ retainedParent) row member value
    (by simpa only [select_natural] using selected)

/-- Forest edit routes supply the same actual selected child routes. -/
theorem forest_to_children {valid : Guard → Prop} {entries : List (Int × Edits Action)}
    {values : List (Value Symbol Guard)} (routes : ForestPaths valid (.editBelow entries) values) :
    ChildrenPaths valid entries 0 values := by
  intro query edits found value selected path token retained
  have retainedParent := below_member entries (Int.ofNat query) edits
    (lookup_mem _ _ _ (by simpa only [Nat.zero_add] using found)) path token retained
  exact routes _ _ retainedParent value (by simpa only [select_natural] using selected)

/-- The next original child retains the source offset. -/
theorem children_tail {valid : Guard → Prop} {entries : List (Int × Edits Action)}
    {offset : Nat} {value : Value Symbol Guard} {values : List (Value Symbol Guard)}
    (routes : ChildrenPaths valid entries offset (value :: values)) :
    ChildrenPaths valid entries (offset + 1) values := by
  intro query edits found original selected
  exact routes (query + 1) edits
    (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using found) original selected

/-- The head child's actual lookup selects its complete node-route certificate. -/
theorem children_selected {valid : Guard → Prop} {entries : List (Int × Edits Action)}
    {offset : Nat} {value : Value Symbol Guard} {values : List (Value Symbol Guard)} {edits : Edits Action}
    (routes : ChildrenPaths valid entries offset (value :: values))
    (found : lookup (Int.ofNat offset) entries = some edits) : NodePaths valid edits value :=
  routes 0 edits (by simpa only [Nat.add_zero] using found) value rfl

/-- Populated parent entries derive both nonempty leaves and population for the selected child. -/
theorem selected_populated {entries : List (Int × Edits Action)} {index : Int} {edits : Edits Action}
    (populated : Populated (.editBelow entries)) (found : lookup index entries = some edits) :
    Populated edits ∧ HasLeaf edits := by
  rw [Populated] at populated
  exact populated index edits (lookup_mem _ _ _ found)

/-- A recursive input with one retained route is an annotated Type input. -/
theorem recursive_annotated {valid : Guard → Prop} {edits : Edits Action} {value : Value Symbol Guard}
    (recursive : SourceEqualityRequiredGraph.Recursive value)
    (nonempty : HasLeaf edits) (routes : NodePaths valid edits value) : Annotated valid value := by
  obtain ⟨path, token, retained⟩ := nonempty
  have route := routes path token retained
  cases route with
  | annotated _ _ checked => exact checked
  | ordinary _ => cases recursive

private theorem compiled_leaf_origin (record : SourceEqualityClassOrder.Record)
    (coherent : SourceEqualityClassOrder.Coherent record) (path : List Int) (token : EqualityNormalize.Path)
    (retained : (path, token) ∈ leaves (SourceCurrentAllocatedClassEditPlan.compiled record)) :
    ∃ original ∈ record.paths, path = original.map Int.ofNat ∧ token = original := by
  have original := (SourceEqualityEditCompiledPaths.build_leaves
    (SourceEqualityClassEdits.edits record.paths id)
    (SourceCurrentAllocatedClassEditPlan.compiled_disjoint record coherent)).mem_iff.mp retained
  obtain ⟨source, member, same⟩ := List.mem_map.mp original
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj same
  exact ⟨source, member, rfl, rfl⟩

/-- Coherent source paths supply node routes for the actual compiled trie. -/
theorem compiled_node_paths (valid : Guard → Prop) (record : SourceEqualityClassOrder.Record)
    (coherent : SourceEqualityClassOrder.Coherent record) (value : Value Symbol Guard)
    (routes : ∀ path ∈ record.paths, TypePath valid (path.map Int.ofNat) value) :
    NodePaths valid (SourceCurrentAllocatedClassEditPlan.compiled record) value := by
  intro path token retained
  obtain ⟨original, member, same, _⟩ := compiled_leaf_origin record coherent path token retained
  rw [same]
  exact routes original member

/-- Coherent source paths supply forest routes for the actual compiled trie. -/
theorem compiled_forest_paths (valid : Guard → Prop) (record : SourceEqualityClassOrder.Record)
    (coherent : SourceEqualityClassOrder.Coherent record) (values : List (Value Symbol Guard))
    (routes : ∀ path ∈ record.paths, ForestPath valid (path.map Int.ofNat) values) :
    ForestPaths valid (SourceCurrentAllocatedClassEditPlan.compiled record) values := by
  intro path token retained
  obtain ⟨original, member, same, _⟩ := compiled_leaf_origin record coherent path token retained
  rw [same]
  exact routes original member

end MicroCFTA.SourceCurrentHereditaryTypeEditPlan
