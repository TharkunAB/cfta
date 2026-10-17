import MicroCFTA.SourceCurrentConstrainedCapRequiredSupport
import MicroCFTA.SourceCurrentAllocatedSharedEditEffects
import MicroCFTA.SourceEqualityClassEdits

/-!
# Initial leaf placement and conditional support through actual shared edits

Placement concerns the immutable input of each retained callback. The ordered
output relation retains every supported path, including paths above or below
an edited position. The leaf certificates below are explicit obligations for
the actual reached calls. This module does not produce those certificates
from an arbitrary warm target or native table.
-/
namespace MicroCFTA.SourceCurrentConstrainedCapEditSupport
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values Edges)
open SourceEqualityAnnotationLanguage SourceEqualityEdits SourceEqualityEditLeafPaths
open SourceEqualityProjectionGraph (select)
open SourceCurrentConstrainedCapPaths (Supported ForestSupported)
open SourceCurrentConstrainedCapRequiredSupport (Preserves)
open SourceCurrentHereditaryConstruction (MuStored)
variable {Symbol Guard Action : Type}

/-- Every retained callback starts at a hereditary endpoint in its original input. -/
def AtLeaves (valid : Guard → Prop) (edits : Edits Action) (value : Value Symbol Guard) : Prop :=
  ∀ path action, (path, action) ∈ leaves edits → Supported valid path value

/-- Child placement uses the actual signed lookup and the current scan offset. -/
def ChildrenAtLeaves (valid : Guard → Prop) (entries : List (Int × Edits Action)) (offset : Nat)
    (values : List (Value Symbol Guard)) : Prop :=
  ∀ query edits, SourceEqualityNeededMap.lookup (Int.ofNat (offset + query)) entries = some edits →
    ∀ value, values[query]? = some value → AtLeaves valid edits value

/-- Each original row supplies placement for its own immutable children. -/
def RowsAtLeaves (valid : Guard → Prop) (entries : List (Int × Edits Action))
    (edges : List (EdgeValue Symbol Guard)) : Prop :=
  ∀ edge ∈ edges, ChildrenAtLeaves valid entries 0 edge.children

/-- Forest-root callbacks are ignored by the literal edit list. -/
def ListAtLeaves (valid : Guard → Prop) (edits : Edits Action) (values : List (Value Symbol Guard)) : Prop :=
  match edits with
  | .editAt _ => True
  | .editBelow entries => ChildrenAtLeaves valid entries 0 values

/-- An entered root callback has a hereditary original input. -/
theorem at_root {valid : Guard → Prop} {action : Action} {value : Value Symbol Guard}
    (placed : AtLeaves valid (.editAt action) value) : Annotated valid value :=
  (placed [] action (by simp only [leaves, List.mem_singleton])).root

/-- Hereditary inputs support every retained edit path. -/
theorem of_annotated (valid : Guard → Prop) (edits : Edits Action) (value : Value Symbol Guard)
    (annotated : Annotated valid value) : AtLeaves valid edits value :=
  fun path _ _ => .plain path annotated

/-- Initial node placement passes to the exact original selected child. -/
theorem ordinary_rows {valid : Guard → Prop} {entries : List (Int × Edits Action)} {entry edges depth free}
    (placed : AtLeaves valid (.editBelow entries) (.node entry edges depth free : Value Symbol Guard)) :
    RowsAtLeaves valid entries edges := by
  intro edge member query edits found value selected path action retained
  have original := placed (Int.ofNat query :: path) action
    (below_member entries _ edits (SourceEqualityNeededMap.lookup_mem _ _ _ (by simpa using found)) path action retained)
  exact original.node_selected edge member value
    (by simpa only [SourceCurrentEditDomains.select_natural] using selected)

/-- The suffix uses the next original offset without filtering or reordering. -/
theorem children_tail {valid : Guard → Prop} {entries : List (Int × Edits Action)} {offset : Nat} {value values}
    (placed : ChildrenAtLeaves valid entries offset (value :: values : List (Value Symbol Guard))) :
    ChildrenAtLeaves valid entries (offset + 1) values := by
  intro query edits found original selected
  exact placed (query + 1) edits (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using found) original selected

/-- The first actual lookup receives the first immutable original input. -/
theorem children_head {valid : Guard → Prop} {entries : List (Int × Edits Action)} {offset : Nat}
    {value values : Value Symbol Guard} {tail : List (Value Symbol Guard)} {edits : Edits Action}
    (placed : ChildrenAtLeaves valid entries offset (value :: tail))
    (found : SourceEqualityNeededMap.lookup (offset : Int) entries = some edits) : AtLeaves valid edits value :=
  placed 0 edits (by simpa using found) value rfl

/-- Initial forest masks determine placement in a compiled nonroot edit map. -/
theorem compiled_list (valid : Guard → Prop) (pairs : List (SourceEqualityEdits.Path × Action))
    (disjoint : pairs.Pairwise (fun first second => SourceEqualityEditCompiledPaths.Disjoint first.1 second.1))
    (nonroot : ∀ path action, (path, action) ∈ pairs → path ≠ []) (values : List (Value Symbol Guard))
    (supported : ∀ path action, (path, action) ∈ pairs → ForestSupported valid path values) :
    ListAtLeaves valid (build pairs) values := by
  generalize built : build pairs = edits
  cases edits with
  | editAt action => exact True.intro
  | editBelow entries =>
      intro query edits found value selected path action retained
      have member : (Int.ofNat query :: path, action) ∈ leaves (build pairs) := by
        rw [built]
        exact below_member entries _ edits (SourceEqualityNeededMap.lookup_mem _ _ _ (by simpa using found)) path action retained
      have original := supported _ action ((SourceEqualityEditCompiledPaths.build_leaves pairs disjoint).mem_iff.mp member)
      exact original value (by simpa only [SourceCurrentEditDomains.select_natural] using selected)

/-- Exact original class masks provide placement for the literal source compiler. -/
theorem class_placement (valid : Guard → Prop) (record : SourceEqualityClassOrder.Record)
    (coherent : SourceEqualityClassOrder.Coherent record) (active : EqualityNormalize.Nontrivial record.paths)
    (target : EqualityNormalize.Path → Action) (values : List (Value Symbol Guard))
    (supported : ∀ path ∈ record.paths, ForestSupported valid (path.map Int.ofNat) values) :
    ListAtLeaves valid (build (SourceEqualityClassEdits.edits record.paths target)) values := by
  apply compiled_list valid _
    (SourceEqualityClassEdits.edits_disjoint record.paths (SourceEqualityClassEdits.coherent_supported record coherent) target)
    (SourceEqualityClassEdits.edits_nonroot record.paths
      (SourceEqualityClassEdits.supported_nonroot record.paths (SourceEqualityClassEdits.coherent_supported record coherent) active) target)
  intro path action member
  obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
  exact supported original present

/-- Identity retains every signed support mask. -/
theorem preserves_refl (valid : Guard → Prop) (value : Value Symbol Guard) : Preserves valid value value :=
  fun _ supported => supported

/-- All-path support composes across successive actual replacements. -/
theorem preserves_trans {valid : Guard → Prop} {first middle last : Value Symbol Guard}
    (earlier : Preserves valid first middle) (later : Preserves valid middle last) : Preserves valid first last :=
  fun path supported => later path (earlier path supported)

/-- A hereditary result supports all paths of the replaced input. -/
theorem preserves_of_annotated (valid : Guard → Prop) (original result : Value Symbol Guard)
    (annotated : Annotated valid result) : Preserves valid original result :=
  fun path _ => .plain path annotated

/-- Ordered replacements retain the exact signed position, including missing negative positions. -/
theorem selected {valid : Guard → Prop} {originals results : List (Value Symbol Guard)}
    (related : All₂ (Preserves valid) originals results) (index : Int) (path : List Int)
    (supported : ∀ original, select originals index = some original → Supported valid path original) :
    ∀ result, select results index = some result → Supported valid path result := by
  intro result found
  obtain ⟨original, earlier, retained⟩ := SourceEqualityProjectionLanguage.all₂_signed related index result found
  exact retained path (supported original earlier)

/-- A rebuilt row retains the full raw guard and all child support masks in order. -/
def RowPreserves (valid : Guard → Prop) (original result : EdgeValue Symbol Guard) : Prop :=
  result.entry.key.constraint = original.entry.key.constraint ∧ All₂ (Preserves valid) original.children result.children

/-- Literal edge interning retains the original guard and the supplied child relation. -/
theorem makeEdge [DecidableEq (EdgeKey Symbol Guard)] (valid : Guard → Prop)
    (original : EdgeValue Symbol Guard) (values : List (Value Symbol Guard)) (state : State Symbol Guard)
    (coherent : InternedRecordCoherence.Coherent state) (cached : InternedNestedFacts.Cached state)
    (available : Values state values) (related : All₂ (Preserves valid) original.children values) :
    RowPreserves valid original (run (InternedConstructorTemplates.makeEdge original.entry.key.symbol original.entry.key.constraint values) state).1 := by
  have key := InternedOrdinaryAbsenceReplay.makeEdge_key original.entry.key.symbol original.entry.key.constraint values state coherent
  have children := InternedShallowValues.makeEdge_children original.entry.key.symbol original.entry.key.constraint values state coherent cached available
  exact ⟨congrArg EdgeKey.constraint key, children.symm ▸ related⟩

private theorem rows_masks {valid : Guard → Prop} {originals results : List (EdgeValue Symbol Guard)}
    (related : All₂ (RowPreserves valid) originals results) (index : Int) (path : List Int)
    (supported : ∀ edge ∈ originals, SourceCurrentConstrainedCapPathExposure.Row valid index path edge) :
    ∀ edge ∈ results, SourceCurrentConstrainedCapPathExposure.Row valid index path edge := by
  induction related with
  | nil => intro edge member; cases member
  | cons first rest ih =>
      intro edge member
      rcases List.mem_cons.mp member with rfl | member
      · exact selected first.2 index path (supported _ List.mem_cons_self)
      · exact ih (fun edge member => supported edge (List.mem_cons_of_mem _ member)) edge member

private theorem rows_annotated {valid : Guard → Prop} {originals results : List (EdgeValue Symbol Guard)}
    (related : All₂ (RowPreserves valid) originals results)
    (annotated : ∀ edge ∈ originals, SourceCurrentHereditaryConstructors.Edge valid edge) :
    ∀ edge ∈ results, SourceCurrentHereditaryConstructors.Edge valid edge := by
  induction related with
  | nil => intro edge member; cases member
  | cons first rest ih =>
      intro edge member
      rcases List.mem_cons.mp member with rfl | member
      · refine ⟨first.1.symm ▸ (annotated _ List.mem_cons_self).1, ?_⟩
        have masks := SourceCurrentConstrainedCapRequiredSupport.forest_supported valid first.2 [] (annotated _ List.mem_cons_self).2
        exact masks
      · exact ih (fun edge member => annotated edge (List.mem_cons_of_mem _ member)) edge member

/-- Actual node normalization retains every path of its original ordinary node. -/
theorem makeNode [DecidableEq (EdgeKey Symbol Guard)] (valid : Guard → Prop)
    (entry) (originals results : List (EdgeValue Symbol Guard)) (depth free) (state : State Symbol Guard)
    (coherent : InternedRecordCoherence.Coherent state) (linked : InternedNestedFacts.Linked state)
    (resident : Edges state results) (related : All₂ (RowPreserves valid) originals results) :
    Preserves valid (.node entry originals depth free) (run (InternedConstructorTemplates.makeNode results) state).1 := by
  intro path supported
  cases path with
  | nil =>
      exact .plain [] (SourceCurrentHereditaryConstructors.makeNode valid results state coherent linked resident
        (rows_annotated related (fun edge member => SourceCurrentHereditaryConstructors.node_edge supported.root edge member)))
  | cons index path =>
      exact SourceCurrentConstrainedCapPathExposure.makeNode valid index path results state coherent linked resident
        (rows_masks related index path (fun edge member => supported.node_selected edge member))

/-- Actual recursive head reads retain all path masks from one finite-cap input. -/
theorem head [DecidableEq (EdgeKey Symbol Guard)] (valid : Guard → Prop) (capDepth : Nat)
    {value result : Value Symbol Guard} {before after : State Symbol Guard}
    (actual : SourceEqualityRequiredHead.Head value before result after)
    (ready : SourceEqualityRequiredCache.Ready before) (available : Available before value)
    (closed : value.free = []) (bounded : SourceCurrentConstrainedCap.Cap valid capDepth value)
    (stored : MuStored valid before) : MuStored valid after ∧ Preserves valid value result := by
  refine ⟨(SourceCurrentConstrainedCapExposure.head valid capDepth actual ready available closed bounded stored).1, ?_⟩
  intro path supported
  cases path with
  | nil => exact .plain [] (SourceCurrentHereditaryExposure.head valid actual ready available closed supported.root stored).2
  | cons index path => exact (SourceCurrentConstrainedCapPathExposure.head valid index path actual ready available closed supported stored).2

/-- All-path preservation also transports the retained initial leaf-placement condition. -/
theorem placement_preserved {valid : Guard → Prop} {edits : Edits Action} {original result : Value Symbol Guard}
    (related : Preserves valid original result) (placed : AtLeaves valid edits original) : AtLeaves valid edits result :=
  fun path action member => related path (placed path action member)

end MicroCFTA.SourceCurrentConstrainedCapEditSupport
