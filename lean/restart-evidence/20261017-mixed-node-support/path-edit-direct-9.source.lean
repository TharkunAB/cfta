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
    {value : Value Symbol Guard} {tail : List (Value Symbol Guard)} {edits : Edits Action}
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
  | editAt action => exact False.elim (SourceEqualityEditCompiledPaths.build_not_leaf pairs disjoint nonroot action built)
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
  obtain ⟨original, present, same⟩ := List.mem_map.mp member
  cases same
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
    (coherent : InternedRecordCoherence.Coherent state) (cached : InternedProbeProvenance.Cached state)
    (available : Values state values) (related : All₂ (Preserves valid) original.children values) :
    RowPreserves valid original (run (InternedConstructorTemplates.makeEdge original.entry.key.symbol original.entry.key.constraint values) state).1 := by
  have key := InternedOrdinaryAbsenceReplay.makeEdge_key original.entry.key.symbol original.entry.key.constraint values state coherent
  have children := InternedShallowValues.makeEdge_children original.entry.key.symbol original.entry.key.constraint values state coherent cached available
  exact ⟨by simpa only using congrArg EdgeKey.constraint key, children.symm ▸ related⟩

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
    (coherent : InternedRecordCoherence.Coherent state) (linked : InternedEdgeResidency.Linked state)
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



section Actual
open SourceCurrentAllocatedSharedEditGraph SourceCurrentEditDomains
open SourceEqualitySharedEditEffects (Allowed)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "HeapState" => InternedConstructorTemplates.State Symbol Guard
local notation "Ready" => SourceCurrentAllocatedSharedTargetState.Ready
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Valid" => EndpointMemoGateTrace.Valid
local notation "Cap" => SourceCurrentConstrainedCap.Cap
local notation "EdgeCap" => SourceCurrentConstrainedCap.Edge
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
variable {formulas : SourceGuards.Formulas FullSyntax.Formula}
variable {solver : SourceGuards.Entailment FullSyntax.Formula} {base : HeapState}

/-- One actual reached leaf records its full input and returned shared states. -/
structure LeafEvent (width : Nat) where
  /-- The immutable original value passed to the leaf. -/
  input : Value Symbol Guard
  /-- The actual shared state before the leaf. -/
  before : SharedState width
  /-- The actual returned value. -/
  result : Value Symbol Guard
  /-- The actual complete returned shared state. -/
  after : SharedState width

mutual
  /-- A literal reached leaf inside one supplied node graph. -/
  inductive NodeLeaf {record originals} : (event : LeafEvent width) →
      {edits : Edits EqualityNormalize.Path} → {value : Value Symbol Guard} → {before : SharedState width} →
      {result : Value Symbol Guard} → {after : SharedState width} →
      EditNode record originals edits value before result after → Prop where
    /-- The node itself is the reached leaf. -/
    | leaf {actual : SourceCurrentAllocatedSharedTargetLeaf.Leaf record originals target value before result after} :
        NodeLeaf ⟨value, before, result, after⟩ (.leaf actual)
    /-- A reached row leaf belongs to the same actual ordinary node graph. -/
    | ordinary {actual : EditRows record originals entries edges before rebuilt middle}
        {built : run (InternedConstructorTemplates.makeNode rebuilt) middle.checked.native.machine.heap = (value, heap)}
        (rows : RowsLeaf event actual) :
        NodeLeaf event (.ordinary (entry := entry) (depth := depth) (free := free) actual built)
    /-- Recursive head work precedes the same reached body leaf. -/
    | recursive {recursive : SourceEqualityRequiredGraph.Recursive original}
        {head : SourceEqualityRequiredHead.Head original before.checked.native.machine.heap exposed heap}
        {body : EditNode record originals (.editBelow entries) exposed (advanceHeap before heap) value after}
        (nodes : NodeLeaf event body) : NodeLeaf event (.recursive recursive head body)

  /-- Reached child leaves retain the exact original scan offset and source order. -/
  inductive ChildrenLeaf {record originals} : (event : LeafEvent width) →
      {entries : List (Int × Edits EqualityNormalize.Path)} → {offset : Nat} → {values : List (Value Symbol Guard)} →
      {before : SharedState width} → {results : List (Value Symbol Guard)} → {after : SharedState width} →
      EditChildren record originals entries offset values before results after → Prop where
    /-- An unselected original child contributes only leaves from the suffix. -/
    | unselected {offset : Nat} {absent : SourceEqualityNeededMap.lookup (offset : Int) entries = none}
        {rest : EditChildren record originals entries (offset + 1) values before results after}
        (later : ChildrenLeaf event rest) : ChildrenLeaf event (.unselected (value := value) offset absent rest)
    /-- The selected first child contains this reached leaf. -/
    | selected_first {offset : Nat} {found : SourceEqualityNeededMap.lookup (offset : Int) entries = some edits}
        {first : EditNode record originals edits value before result middle}
        {rest : EditChildren record originals entries (offset + 1) values middle results after}
        (head : NodeLeaf event first) : ChildrenLeaf event (.selected offset found first rest)
    /-- The original suffix contains this leaf after the first child's return. -/
    | selected_rest {offset : Nat} {found : SourceEqualityNeededMap.lookup (offset : Int) entries = some edits}
        {first : EditNode record originals edits value before result middle}
        {rest : EditChildren record originals entries (offset + 1) values middle results after}
        (later : ChildrenLeaf event rest) : ChildrenLeaf event (.selected offset found first rest)

  /-- A reached row leaf belongs to its actual child scan or later row scan. -/
  inductive RowsLeaf {record originals} : (event : LeafEvent width) →
      {entries : List (Int × Edits EqualityNormalize.Path)} → {edges : List (EdgeValue Symbol Guard)} →
      {before : SharedState width} → {results : List (EdgeValue Symbol Guard)} → {after : SharedState width} →
      EditRows record originals entries edges before results after → Prop where
    /-- The original first row contains this reached child leaf. -/
    | first {edge : EdgeValue Symbol Guard} {children : EditChildren record originals entries 0 edge.children before values middle}
        {built : run (InternedConstructorTemplates.makeEdge edge.entry.key.symbol edge.entry.key.constraint values)
          middle.checked.native.machine.heap = (result, heap)}
        {rest : EditRows record originals entries edges (advanceHeap middle heap) results after}
        (head : ChildrenLeaf event children) : RowsLeaf event (.cons children built rest)
    /-- The remaining original rows contain this reached leaf. -/
    | rest {edge : EdgeValue Symbol Guard} {children : EditChildren record originals entries 0 edge.children before values middle}
        {built : run (InternedConstructorTemplates.makeEdge edge.entry.key.symbol edge.entry.key.constraint values)
          middle.checked.native.machine.heap = (result, heap)}
        {rest : EditRows record originals entries edges (advanceHeap middle heap) results after}
        (later : RowsLeaf event rest) : RowsLeaf event (.cons children built rest)
end

/-- This explicit local obligation is not a theorem about arbitrary warm target/native tables. -/
def LeafCertificate (annotation : Guard → Prop) (event : LeafEvent width) : Prop :=
  MuStored annotation event.before.checked.native.machine.heap → Annotated annotation event.input →
    MuStored annotation event.after.checked.native.machine.heap ∧ Annotated annotation event.result

/-- Every literal reached node leaf has the stated local certificate. -/
def NodeLeaves (annotation : Guard → Prop) {record originals edits value before result after}
    (actual : EditNode (width := width) record originals edits value before result after) : Prop :=
  ∀ event, NodeLeaf event actual → LeafCertificate annotation event

/-- Every literal reached child leaf has the stated local certificate. -/
def ChildrenLeaves (annotation : Guard → Prop) {record originals entries offset values before results after}
    (actual : EditChildren (width := width) record originals entries offset values before results after) : Prop :=
  ∀ event, ChildrenLeaf event actual → LeafCertificate annotation event

/-- Every literal reached row leaf has the stated local certificate. -/
def RowsLeaves (annotation : Guard → Prop) {record originals entries edges before results after}
    (actual : EditRows (width := width) record originals entries edges before results after) : Prop :=
  ∀ event, RowsLeaf event actual → LeafCertificate annotation event

private def NodeGoal (annotation : Guard → Prop) {record originals edits input before result after}
    (actual : EditNode (width := width) record originals edits input before result after) (memos : Memos) : Prop :=
  NodeLeaves annotation actual → ∀ inventory depth, Populated edits → HasLeaf edits → Allowed record edits →
    Ready formulas solver inventory record originals base before → Available before.checked.native.machine.heap input →
    Safe edits input → Valid before.checked.native.machine.heap memos →
    MuStored annotation before.checked.native.machine.heap → Cap annotation depth input → AtLeaves annotation edits input →
    MuStored annotation after.checked.native.machine.heap ∧ Preserves annotation input result

private def ChildrenGoal (annotation : Guard → Prop) {record originals entries offset inputs before results after}
    (actual : EditChildren (width := width) record originals entries offset inputs before results after) (memos : Memos) : Prop :=
  ChildrenLeaves annotation actual → ∀ inventory depth, Populated (.editBelow entries) → Allowed record (.editBelow entries) →
    Ready formulas solver inventory record originals base before → Values before.checked.native.machine.heap inputs →
    ChildrenSafe entries offset inputs → Valid before.checked.native.machine.heap memos →
    MuStored annotation before.checked.native.machine.heap → (∀ value ∈ inputs, Cap annotation depth value) →
    ChildrenAtLeaves annotation entries offset inputs →
    MuStored annotation after.checked.native.machine.heap ∧ All₂ (Preserves annotation) inputs results

private def RowsGoal (annotation : Guard → Prop) {record originals entries inputs before results after}
    (actual : EditRows (width := width) record originals entries inputs before results after) (memos : Memos) : Prop :=
  RowsLeaves annotation actual → ∀ inventory depth, Populated (.editBelow entries) → Allowed record (.editBelow entries) →
    Ready formulas solver inventory record originals base before → Edges before.checked.native.machine.heap inputs →
    RowsSafe entries inputs → Valid before.checked.native.machine.heap memos →
    MuStored annotation before.checked.native.machine.heap → (∀ edge ∈ inputs, EdgeCap annotation depth edge) →
    RowsAtLeaves annotation entries inputs →
    MuStored annotation after.checked.native.machine.heap ∧ All₂ (RowPreserves annotation) inputs results

set_option maxHeartbeats 1600000 in
private theorem all_reads (annotation : Guard → Prop) :
    (∀ {record originals edits value before result after} {memos final : Memos}
      {actual : EditNode (width := width) record originals edits value before result after},
      NodeReads formulas solver base actual memos final → NodeGoal (width := width) (formulas := formulas) (solver := solver) (base := base) annotation actual memos) ∧
    (∀ {record originals entries offset values before results after} {memos final : Memos}
      {actual : EditChildren (width := width) record originals entries offset values before results after},
      ChildrenReads formulas solver base actual memos final → ChildrenGoal (width := width) (formulas := formulas) (solver := solver) (base := base) annotation actual memos) ∧
    (∀ {record originals entries edges before results after} {memos final : Memos}
      {actual : EditRows (width := width) record originals entries edges before results after},
      RowsReads formulas solver base actual memos final → RowsGoal (width := width) (formulas := formulas) (solver := solver) (base := base) annotation actual memos) := by
  have leafCase : ∀ {next record originals path value before result after memos saved}
      (receipt : SourceCurrentAllocatedSharedTargetLeaf.Receipt formulas solver next record originals base path value before result after memos saved),
      NodeGoal (width := width) (formulas := formulas) (solver := solver) (base := base) annotation (.leaf receipt.actual) memos := by
    intro next record originals path value before result after memos saved receipt leaves inventory depth _ _ _ _ _ _ _ stored _ placed
    have output := leaves ⟨value, before, result, after⟩ (NodeLeaf.leaf (actual := receipt.actual)) stored (at_root placed)
    exact ⟨output.1, preserves_of_annotated annotation value result output.2⟩
  have emptyCase : ∀ {record originals entries state memos},
      NodeGoal (width := width) (formulas := formulas) (solver := solver) (base := base) annotation
        (.empty (record := record) (originals := originals) (entries := entries) (state := state)) memos := by
    intro record originals entries state memos _ inventory depth _ _ _ _ _ _ _ stored _ _
    exact ⟨stored, preserves_refl annotation .empty⟩
  have ordinaryCase : ∀ {record originals memos saved entries edges before rebuilt middle value heap entry depth free}
      {actual : EditRows record originals entries edges before rebuilt middle}
      {built : run (InternedConstructorTemplates.makeNode rebuilt) middle.checked.native.machine.heap = (value, heap)},
      RowsReads formulas solver base actual memos saved →
      RowsGoal (width := width) (formulas := formulas) (solver := solver) (base := base) annotation actual memos →
      NodeGoal (width := width) (formulas := formulas) (solver := solver) (base := base) annotation
        (.ordinary (entry := entry) (depth := depth) (free := free) actual built) memos := by
    intro record originals memos saved entries edges before rebuilt middle value heap entry depth free actual built reads ih
      leaves inventory capDepth populated _ allowed ready available safe valid stored bounded placed
    have rows : RowsLeaves annotation actual := fun event reached => leaves event (.ordinary reached)
    have facts := ready.checked.semantic.ready.semantic.1.normal.facts
    have resident := InternedEdgeResidency.resident_edges _ facts.linked _ available.resident
    have related := ih rows inventory capDepth populated allowed ready resident (SourceCurrentEditDomains.ordinary_rows safe)
      valid stored (fun edge member => SourceCurrentConstrainedCap.node_edge bounded edge member) (ordinary_rows placed)
    obtain ⟨next, checked⟩ := SourceCurrentAllocatedSharedEditEffects.rows_effects reads populated allowed ready resident
      (SourceCurrentEditDomains.ordinary_rows safe) valid
    have currentFacts := checked.ready.checked.semantic.ready.semantic.1.normal.facts
    have narrowed := makeNode annotation entry edges rebuilt depth free middle.checked.native.machine.heap
      currentFacts.coherent currentFacts.linked checked.available related.2
    exact ⟨by change MuStored annotation heap; simpa only [built] using related.1.makeNode rebuilt, by simpa only [built] using narrowed⟩
  have recursiveCase : ∀ {record originals memos current saved entries original before exposed heap value after}
      {recursive : SourceEqualityRequiredGraph.Recursive original}
      {head : SourceEqualityRequiredHead.Head original before.checked.native.machine.heap exposed heap}
      {body : EditNode record originals (.editBelow entries) exposed (advanceHeap before heap) value after},
      SourceCurrentRequiredQueryMemos.HeadReads head memos current →
      SourceCurrentSubsumesQueryMemos.Effect before.checked.native.machine.heap heap memos current →
      NodeReads formulas solver base body current saved →
      NodeGoal (width := width) (formulas := formulas) (solver := solver) (base := base) annotation body current →
      NodeGoal (width := width) (formulas := formulas) (solver := solver) (base := base) annotation (.recursive recursive head body) memos := by
    intro record originals memos current saved entries original before exposed heap value after recursive actual body
      headReads headGlobal bodyReads ih leaves inventory depth populated nonempty allowed ready available safe _ stored bounded placed
    have bodyLeaves : NodeLeaves annotation body := fun event reached => leaves event (.recursive reached)
    have closed := recursive_closed recursive nonempty safe
    have localHead := head annotation depth actual ready.checked.semantic.ready available closed bounded stored
    have capHead := SourceCurrentConstrainedCapExposure.head annotation depth actual ready.checked.semantic.ready available closed bounded stored
    have physical := SourceCurrentAllocatedSharedEditEffects.head_physical ready actual available
    have headReady : Ready formulas solver inventory record originals base (advanceHeap before heap) := physical.1
    have headSafe : Safe (.editBelow entries) exposed := by
      have checked := actual.verified ready.checked.semantic.ready available closed
      exact closed_safe _ exposed heap headGlobal.semantic checked.2.1 checked.2.2.1
    have later := ih bodyLeaves inventory depth populated nonempty allowed headReady physical.2.2 headSafe
      headGlobal.valid localHead.1 capHead.2 (placement_preserved localHead.2 placed)
    exact ⟨later.1, preserves_trans localHead.2 later.2⟩
  have nilChildren : ∀ {record originals entries offset state memos},
      ChildrenGoal (width := width) (formulas := formulas) (solver := solver) (base := base) annotation
        (.nil (record := record) (originals := originals) (entries := entries) (index := offset) (state := state)) memos := by
    intro record originals entries offset state memos _ inventory depth _ _ _ _ _ _ stored _ _
    exact ⟨stored, .nil⟩
  have unselectedCase : ∀ {record originals memos saved entries values before results after value} {offset : Nat}
      {absent : SourceEqualityNeededMap.lookup (offset : Int) entries = none}
      {rest : EditChildren record originals entries (offset + 1) values before results after},
      ChildrenReads formulas solver base rest memos saved →
      ChildrenGoal (width := width) (formulas := formulas) (solver := solver) (base := base) annotation rest memos →
      ChildrenGoal (width := width) (formulas := formulas) (solver := solver) (base := base) annotation (.unselected (value := value) offset absent rest) memos := by
    intro record originals memos saved entries values before results after value offset absent rest _ ih leaves inventory depth
      populated allowed ready available safe valid stored bounded placed
    have laterLeaves : ChildrenLeaves annotation rest := fun event reached => leaves event (.unselected reached)
    have later := ih laterLeaves inventory depth populated allowed ready
      (fun child member => available child (List.mem_cons_of_mem _ member)) (SourceCurrentEditDomains.children_tail safe) valid stored
      (fun child member => bounded child (List.mem_cons_of_mem _ member)) (children_tail placed)
    exact ⟨later.1, .cons (preserves_refl annotation value) later.2⟩
  have selectedCase : ∀ {record originals memos current saved entries edits value before result middle values results after} {offset : Nat}
      {found : SourceEqualityNeededMap.lookup (offset : Int) entries = some edits}
      {first : EditNode record originals edits value before result middle}
      {rest : EditChildren record originals entries (offset + 1) values middle results after},
      NodeReads formulas solver base first memos current → ChildrenReads formulas solver base rest current saved →
      NodeGoal (width := width) (formulas := formulas) (solver := solver) (base := base) annotation first memos →
      ChildrenGoal (width := width) (formulas := formulas) (solver := solver) (base := base) annotation rest current →
      ChildrenGoal (width := width) (formulas := formulas) (solver := solver) (base := base) annotation (.selected offset found first rest) memos := by
    intro record originals memos current saved entries edits value before result middle values results after offset found first rest
      firstReads _ firstIH restIH leaves inventory depth populated allowed ready available safe valid stored bounded placed
    have firstLeaves : NodeLeaves annotation first := fun event reached => leaves event (.selected_first reached)
    have restLeaves : ChildrenLeaves annotation rest := fun event reached => leaves event (.selected_rest reached)
    have member := SourceEqualityNeededMap.lookup_mem _ _ _ found
    have children := (show ∀ index child, (index, child) ∈ entries → Populated child ∧ HasLeaf child from
      by simpa only [Populated] using populated)
    have childAllowed : Allowed record edits := by
      rw [Allowed, All] at allowed
      exact allowed _ _ member
    have firstSafe := safe 0 _ (by simpa using found) value rfl
    have related := firstIH firstLeaves inventory depth (children _ _ member).1 (children _ _ member).2 childAllowed
      ready (available _ List.mem_cons_self) firstSafe valid stored (bounded _ List.mem_cons_self) (children_head placed found)
    obtain ⟨middleInventory, checked⟩ := SourceCurrentAllocatedSharedEditEffects.node_effects firstReads
      (children _ _ member).1 (children _ _ member).2 childAllowed ready (available _ List.mem_cons_self) firstSafe valid
    have later := restIH restLeaves middleInventory depth populated allowed checked.ready
      (fun original member => checked.effects.keeps.available original (available original (List.mem_cons_of_mem _ member)))
      (SourceCurrentEditDomains.children_tail safe) checked.globals.valid related.1
      (fun original member => bounded original (List.mem_cons_of_mem _ member)) (children_tail placed)
    exact ⟨later.1, .cons related.2 later.2⟩
  have nilRows : ∀ {record originals entries state memos},
      RowsGoal (width := width) (formulas := formulas) (solver := solver) (base := base) annotation
        (.nil (record := record) (originals := originals) (entries := entries) (state := state)) memos := by
    intro record originals entries state memos _ inventory depth _ _ _ _ _ _ stored _ _
    exact ⟨stored, .nil⟩
  have consCase : ∀ {record originals memos current saved entries before values middle result heap edges results after} {edge : EdgeValue Symbol Guard}
      {children : EditChildren record originals entries 0 edge.children before values middle}
      {rebuilt : run (InternedConstructorTemplates.makeEdge edge.entry.key.symbol edge.entry.key.constraint values)
        middle.checked.native.machine.heap = (result, heap)}
      {rest : EditRows record originals entries edges (advanceHeap middle heap) results after},
      ChildrenReads formulas solver base children memos current → RowsReads formulas solver base rest current saved →
      ChildrenGoal (width := width) (formulas := formulas) (solver := solver) (base := base) annotation children memos →
      RowsGoal (width := width) (formulas := formulas) (solver := solver) (base := base) annotation rest current →
      RowsGoal (width := width) (formulas := formulas) (solver := solver) (base := base) annotation (.cons children rebuilt rest) memos := by
    intro record originals memos current saved entries before values middle result heap edges results after edge children rebuilt rest
      firstReads _ firstIH restIH leaves inventory depth populated allowed ready resident safe valid stored bounded placed
    have firstLeaves : ChildrenLeaves annotation children := fun event reached => leaves event (.first reached)
    have restLeaves : RowsLeaves annotation rest := fun event reached => leaves event (.rest reached)
    have facts := ready.checked.semantic.ready.semantic.1.normal.facts
    have available := facts.cached.edges edge.entry.key edge (resident _ List.mem_cons_self)
    have childCaps : ∀ child ∈ edge.children, Cap annotation (depth - 1) child := by
      cases depth with
      | zero => exact fun child member => .plain 0 ((bounded _ List.mem_cons_self).2 child member)
      | succ depth => exact bounded _ List.mem_cons_self
    have related := firstIH firstLeaves inventory (depth - 1) populated allowed ready available (safe _ List.mem_cons_self)
      valid stored childCaps (placed _ List.mem_cons_self)
    obtain ⟨middleInventory, checked⟩ := SourceCurrentAllocatedSharedEditEffects.children_effects firstReads
      populated allowed ready available (safe _ List.mem_cons_self) valid
    have field := (ready.checked.good.fields _ _ (resident _ List.mem_cons_self)).grows checked.effects.grows
    have rebuiltPhysical := SourceCurrentAllocatedSharedEditEffects.edge_physical checked.ready edge.entry.key.symbol
      edge.entry.key.constraint values field checked.available
    have edgeReady : Ready formulas solver middleInventory record originals base (advanceHeap middle heap) := by
      simpa only [rebuilt] using rebuiltPhysical.1
    have edgeKeeps : SourceEqualityRequiredCache.Keeps middle.checked.native.machine.heap heap := by
      have keeps := rebuiltPhysical.2.1.keeps
      change SourceEqualityRequiredCache.Keeps middle.checked.native.machine.heap
        (run (InternedConstructorTemplates.makeEdge edge.entry.key.symbol edge.entry.key.constraint values) middle.checked.native.machine.heap).2 at keeps
      simpa only [rebuilt] using keeps
    have currentFacts := checked.ready.checked.semantic.ready.semantic.1.normal.facts
    have resultMask := makeEdge annotation edge values middle.checked.native.machine.heap
      currentFacts.coherent currentFacts.cached checked.available related.2
    have edgeStore : MuStored annotation heap := by
      simpa only [rebuilt] using related.1.makeEdge edge.entry.key.symbol edge.entry.key.constraint values
    have currentValid := SourceQueryUnfoldMemo.valid_grows _ _ checked.ready.checked.semantic edgeKeeps current checked.globals.valid
    have later := restIH restLeaves middleInventory depth populated allowed edgeReady
      (fun original member => InternedEdgeResidency.edge_grows _ _ (checked.effects.keeps.trans edgeKeeps).growth original
        (resident original (List.mem_cons_of_mem _ member)))
      (fun original member => safe original (List.mem_cons_of_mem _ member)) currentValid edgeStore
      (fun original member => bounded original (List.mem_cons_of_mem _ member))
      (fun original member => placed original (List.mem_cons_of_mem _ member))
    exact ⟨later.1, .cons (by simpa only [rebuilt] using resultMask) later.2⟩
  refine ⟨?_, ?_, ?_⟩
  · intro record originals edits value before result after memos final actual reads
    exact NodeReads.rec
      (motive_1 := fun {record originals edits value before result after} actual memos _ _ =>
        NodeGoal (width := width) (formulas := formulas) (solver := solver) (base := base) annotation actual memos)
      (motive_2 := fun {record originals entries offset values before results after} actual memos _ _ =>
        ChildrenGoal (width := width) (formulas := formulas) (solver := solver) (base := base) annotation actual memos)
      (motive_3 := fun {record originals entries edges before results after} actual memos _ _ =>
        RowsGoal (width := width) (formulas := formulas) (solver := solver) (base := base) annotation actual memos)
      @leafCase @emptyCase @ordinaryCase @recursiveCase @nilChildren @unselectedCase @selectedCase @nilRows @consCase reads
  · intro record originals entries offset values before results after memos final actual reads
    exact ChildrenReads.rec
      (motive_1 := fun {record originals edits value before result after} actual memos _ _ =>
        NodeGoal (width := width) (formulas := formulas) (solver := solver) (base := base) annotation actual memos)
      (motive_2 := fun {record originals entries offset values before results after} actual memos _ _ =>
        ChildrenGoal (width := width) (formulas := formulas) (solver := solver) (base := base) annotation actual memos)
      (motive_3 := fun {record originals entries edges before results after} actual memos _ _ =>
        RowsGoal (width := width) (formulas := formulas) (solver := solver) (base := base) annotation actual memos)
      @leafCase @emptyCase @ordinaryCase @recursiveCase @nilChildren @unselectedCase @selectedCase @nilRows @consCase reads
  · intro record originals entries edges before results after memos final actual reads
    exact RowsReads.rec
      (motive_1 := fun {record originals edits value before result after} actual memos _ _ =>
        NodeGoal (width := width) (formulas := formulas) (solver := solver) (base := base) annotation actual memos)
      (motive_2 := fun {record originals entries offset values before results after} actual memos _ _ =>
        ChildrenGoal (width := width) (formulas := formulas) (solver := solver) (base := base) annotation actual memos)
      (motive_3 := fun {record originals entries edges before results after} actual memos _ _ =>
        RowsGoal (width := width) (formulas := formulas) (solver := solver) (base := base) annotation actual memos)
      @leafCase @emptyCase @ordinaryCase @recursiveCase @nilChildren @unselectedCase @selectedCase @nilRows @consCase reads

/-- Conditional actual node support uses explicit reached-leaf certificates, not a produced target law. -/
theorem node_with_leaf_certificates (annotation : Guard → Prop) {record originals edits value before result after memos final}
    {actual : EditNode (width := width) record originals edits value before result after}
    (reads : NodeReads formulas solver base actual memos final) (leaves : NodeLeaves annotation actual)
    (inventory : Inventory) (depth : Nat) (populated : Populated edits) (nonempty : HasLeaf edits) (allowed : Allowed record edits)
    (ready : Ready formulas solver inventory record originals base before) (available : Available before.checked.native.machine.heap value)
    (safe : Safe edits value) (valid : Valid before.checked.native.machine.heap memos)
    (stored : MuStored annotation before.checked.native.machine.heap) (bounded : Cap annotation depth value)
    (placed : AtLeaves annotation edits value) :
    MuStored annotation after.checked.native.machine.heap ∧ Preserves annotation value result :=
  (all_reads annotation).1 reads leaves inventory depth populated nonempty allowed ready available safe valid stored bounded placed

/-- Conditional actual child support retains all original signed positions in order. -/
theorem children_with_leaf_certificates (annotation : Guard → Prop) {record originals entries offset values before results after memos final}
    {actual : EditChildren (width := width) record originals entries offset values before results after}
    (reads : ChildrenReads formulas solver base actual memos final) (leaves : ChildrenLeaves annotation actual)
    (inventory : Inventory) (depth : Nat) (populated : Populated (.editBelow entries)) (allowed : Allowed record (.editBelow entries))
    (ready : Ready formulas solver inventory record originals base before) (available : Values before.checked.native.machine.heap values)
    (safe : ChildrenSafe entries offset values) (valid : Valid before.checked.native.machine.heap memos)
    (stored : MuStored annotation before.checked.native.machine.heap) (bounded : ∀ value ∈ values, Cap annotation depth value)
    (placed : ChildrenAtLeaves annotation entries offset values) :
    MuStored annotation after.checked.native.machine.heap ∧ All₂ (Preserves annotation) values results :=
  (all_reads annotation).2.1 reads leaves inventory depth populated allowed ready available safe valid stored bounded placed

/-- Conditional actual row support retains each raw guard and its positional child relation. -/
theorem rows_with_leaf_certificates (annotation : Guard → Prop) {record originals entries edges before results after memos final}
    {actual : EditRows (width := width) record originals entries edges before results after}
    (reads : RowsReads formulas solver base actual memos final) (leaves : RowsLeaves annotation actual)
    (inventory : Inventory) (depth : Nat) (populated : Populated (.editBelow entries)) (allowed : Allowed record (.editBelow entries))
    (ready : Ready formulas solver inventory record originals base before) (resident : Edges before.checked.native.machine.heap edges)
    (safe : RowsSafe entries edges) (valid : Valid before.checked.native.machine.heap memos)
    (stored : MuStored annotation before.checked.native.machine.heap) (bounded : ∀ edge ∈ edges, EdgeCap annotation depth edge)
    (placed : RowsAtLeaves annotation entries edges) :
    MuStored annotation after.checked.native.machine.heap ∧ All₂ (RowPreserves annotation) edges results :=
  (all_reads annotation).2.2 reads leaves inventory depth populated allowed ready resident safe valid stored bounded placed

end Actual
end MicroCFTA.SourceCurrentConstrainedCapEditSupport
