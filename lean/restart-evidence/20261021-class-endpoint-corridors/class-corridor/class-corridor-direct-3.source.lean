import MicroCFTA.SourceCurrentRawCorridorSharedTargetCap
import MicroCFTA.SourceCurrentAllocatedClassEdits
import MicroCFTA.SourceCurrentConstrainedCapOpenExposure
import MicroCFTA.SourceCurrentConstrainedCapMixedEditStoreEffects

/-! # All raw endpoint corridors through actual class edits -/
namespace MicroCFTA.SourceCurrentClassEndpointCorridors
open Cache Language InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open InternedNestedProvenance (Values Edges)
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache SourceEqualityProjectionGraph
open SourceEqualityEdits SourceEqualityEditLeafPaths SourceCurrentEditDomains
open SourceEqualitySharedEditEffects (Allowed)
open SourceCurrentAllocatedSharedEditGraph SourceCurrentAllocatedSharedEditEffects
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedClassEditPlan
open SourceCurrentConstrainedCap (Cap)
open SourceCurrentRequiredRawCorridor (RawCorridor)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Row" => EdgeValue Symbol Guard
local notation "Heap" => InternedConstructorTemplates.State Symbol Guard
local notation "Ready" => SourceCurrentAllocatedSharedTargetState.Ready
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Valid" => EndpointMemoGateTrace.Valid
local notation "Stored" => SourceCurrentRequiredSharedTargetCap.Stored
local notation "Plain" => (fun guard : Guard => SourceMemoGate.plain guard = true)
private def Finite (value : Node) := ∃ depth, Cap Plain depth value
private def Preserves (original result : Node) := ∀ path, RawCorridor path original → RawCorridor path result
private def AtLeaves (edits : Edits EqualityNormalize.Path) (value : Node) :=
  ∀ path action, (path,action) ∈ leaves edits → RawCorridor path value
private def ChildrenAtLeaves (entries : List (Int × Edits EqualityNormalize.Path)) (offset : Nat) (values : List Node) :=
  ∀ query edits, SourceEqualityNeededMap.lookup (Int.ofNat (offset+query)) entries = some edits →
    ∀ value, values[query]? = some value → AtLeaves edits value
private def Masks (record : SourceEqualityClassOrder.Record) (values : List Node) :=
  ∀ index path, index::path ∈ record.paths → ∀ value, select values (Int.ofNat index) = some value → RawCorridor (path.map Int.ofNat) value
private theorem root_finite {value : Node} (raw : RawCorridor [] value) : Finite value := by
  cases raw with | full _ _ bounded => exact bounded
private theorem child_finite {value : Node} (bounded : Finite value) (row : Row)
    (member : row ∈ nodeEdges value) (child : Node) (inside : child ∈ row.children) : Finite child := by
  obtain ⟨depth,bounded⟩ := bounded
  have localRow := SourceCurrentConstrainedCap.node_edge bounded row member
  cases depth with
  | zero => exact ⟨0,.plain 0 (localRow.2 child inside)⟩
  | succ depth => exact ⟨depth,localRow child inside⟩
private theorem selected {index path entry rows depth free child} (raw : RawCorridor (index::path) (.node entry rows depth free))
    (row : Row) (member : row ∈ rows) (found : select row.children index = some child) : RawCorridor path child := by
  cases raw with
  | full _ _ bounded => exact .full _ _ (child_finite bounded row member child (select_member found))
  | node _ _ _ _ _ _ children => exact children row member child found
private theorem uniform (values : List Node) (all : ∀ value ∈ values, Finite value) : ∃ depth, ∀ value ∈ values, Cap Plain depth value := by
  induction values with
  | nil => exact ⟨0,by intro value member; cases member⟩
  | cons value values ih =>
    obtain ⟨first,bounded⟩ := all value List.mem_cons_self
    obtain ⟨rest,others⟩ := ih (fun child member => all child (List.mem_cons_of_mem _ member))
    refine ⟨max first rest,?_⟩
    intro child member
    rcases List.mem_cons.mp member with rfl | later
    · exact bounded.mono (Nat.le_max_left _ _)
    · exact (others child later).mono (Nat.le_max_right _ _)
private theorem children_selected {originals results : List Node} (related : All₂ Preserves originals results)
    (index : Int) (path : List Int) (raw : ∀ value, select originals index = some value → RawCorridor path value) :
    ∀ value, select results index = some value → RawCorridor path value := by
  intro value found
  obtain ⟨original,chosen,law⟩ := SourceEqualityProjectionLanguage.all₂_signed related index value found
  exact law path (raw original chosen)
private theorem children_finite {originals results : List Node} (related : All₂ Preserves originals results)
    (bounded : ∀ value ∈ originals, Finite value) : ∀ value ∈ results, Finite value := by
  induction related with
  | nil => intro value member; cases member
  | cons first rest ih =>
    intro value member
    rcases List.mem_cons.mp member with rfl | later
    · exact root_finite (first [] (.full _ _ (bounded _ List.mem_cons_self)))
    · exact ih (fun value member => bounded value (List.mem_cons_of_mem _ member)) value later

private theorem children_tail {entries offset value values}
    (placed : ChildrenAtLeaves entries offset (value::values)) : ChildrenAtLeaves entries (offset+1) values := by
  intro query edits found original chosen
  exact placed (query+1) edits (by simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using found) original chosen
private theorem ordinary_rows {entries entry rows depth free}
    (placed : AtLeaves (.editBelow entries) (.node entry rows depth free)) :
    ∀ row ∈ rows, ChildrenAtLeaves entries 0 row.children := by
  intro row member query edits found value chosen path action retained
  have raw := placed (Int.ofNat query::path) action
    (below_member entries _ edits (SourceEqualityNeededMap.lookup_mem _ _ _ (by simpa using found)) path action retained)
  exact selected raw row member (by simpa only [SourceCurrentEditDomains.select_natural] using chosen)

private theorem placement {record values entries} (coherent : SourceEqualityClassOrder.Coherent record)
    (built : compiled record = .editBelow entries) (masks : Masks record values) : ChildrenAtLeaves entries 0 values := by
  intro query edits found value chosen path action retained
  have member : (Int.ofNat query::path,action) ∈ leaves (compiled record) := by
    rw [built]; exact below_member _ _ _ (SourceEqualityNeededMap.lookup_mem _ _ _ (by simpa using found)) _ _ retained
  have original := (SourceEqualityEditCompiledPaths.build_leaves _ (compiled_disjoint record coherent)).mem_iff.mp member
  obtain ⟨natural,included,same⟩ := List.mem_map.mp original
  have samePath := congrArg Prod.fst same
  dsimp at samePath
  cases natural with
  | nil => cases samePath
  | cons index tail =>
    have parts := List.cons.inj samePath
    have sameIndex : index = query := Int.ofNat.inj parts.1
    subst index
    have raw := masks query tail included value (by simpa only [SourceCurrentEditDomains.select_natural] using chosen)
    exact parts.2 ▸ raw

private def ListAtLeaves (edits : Edits EqualityNormalize.Path) (values : List Node) : Prop :=
  match edits with | .editAt _ => True | .editBelow entries => ChildrenAtLeaves entries 0 values
private theorem forest_refl (values : List Node) : All₂ Preserves values values := by
  induction values with
  | nil => exact .nil
  | cons _ _ ih => exact .cons (fun _ raw => raw) ih
private theorem rows_finite {originals results : List Row}
    (related : All₂ (fun original result => All₂ Preserves original.children result.children) originals results)
    (bounded : ∀ row ∈ originals, ∀ child ∈ row.children, Finite child) :
    ∀ row ∈ results, ∀ child ∈ row.children, Finite child := by
  induction related with
  | nil => intro row member; cases member
  | cons first rest ih =>
    intro row member
    rcases List.mem_cons.mp member with rfl | later
    · exact children_finite first (bounded _ List.mem_cons_self)
    · exact ih (fun row member => bounded row (List.mem_cons_of_mem _ member)) row later
private theorem rows_selected {originals results : List Row}
    (related : All₂ (fun original result => All₂ Preserves original.children result.children) originals results)
    (index : Int) (path : List Int)
    (children : ∀ row ∈ originals, ∀ child, select row.children index = some child → RawCorridor path child) :
    ∀ row ∈ results, ∀ child, select row.children index = some child → RawCorridor path child := by
  induction related with
  | nil => intro row member; cases member
  | cons first rest ih =>
    intro row member
    rcases List.mem_cons.mp member with rfl | later
    · exact children_selected first index path (children _ List.mem_cons_self)
    · exact ih (fun row member => children row (List.mem_cons_of_mem _ member)) row later

section Actual
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
private theorem node_preserves (entry) (originals results : List Row) (depth free) (state : Heap)
    (coherent : InternedRecordCoherence.Coherent state) (linked : Linked state) (resident : Edges state results)
    (related : All₂ (fun original result => All₂ Preserves original.children result.children) originals results) :
    Preserves (.node entry originals depth free) (run (makeNode results) state).1 := by
  intro path raw
  cases raw with
  | full _ _ bounded =>
    have rows := rows_finite related (fun row member child inside => child_finite bounded row member child inside)
    obtain ⟨cap,caps⟩ := uniform (results.flatMap EdgeValue.children) (by
      intro child member; obtain ⟨row,member,inside⟩ := List.mem_flatMap.mp member; exact rows row member child inside)
    exact .full _ _ ⟨cap+1,SourceCurrentConstrainedCap.makeNode Plain (cap+1) results state coherent linked resident
      (fun row member child inside => caps child (List.mem_flatMap.mpr ⟨row,member,inside⟩))⟩
  | node _ _ _ _ index tail children =>
    have masked := rows_selected related index tail children
    have residentCanonical : Edges state (canonicalEdges (surviving results)) :=
      fun row member => resident row (List.mem_filter.mp (canonicalEdges_member _ row member)).1
    unfold InternedConstructorTemplates.makeNode
    dsimp only
    split
    · exact .full _ _ ⟨0,.plain 0 .empty⟩
    · rename_i first rest same
      obtain ⟨key,actual⟩ := InternedEdgeResidency.identifyNode_readback (first::rest) state coherent linked
        (by simpa only [Edges,same] using residentCanonical)
      simp only [run,actual,identifyNode]
      exact .node key _ _ _ index tail (by
        intro row member; exact masked row (List.mem_filter.mp (canonicalEdges_member _ row (same ▸ member))).1)

private theorem advance_stored {formulas solver inventory record originals base} {before : SharedState width}
    (heap : Heap) (stored : Stored before)
    (ready : Ready formulas solver inventory record originals base (advanceHeap before heap))
    (effects : SourceCurrentConjunctionRowsAllocation.Effects (SourceCurrentAllocatedNativeEffects.physical before.checked)
      (SourceCurrentAllocatedNativeEffects.physical (advanceHeap before heap).checked))
    (guards : SourceCurrentConstrainedCapGuardHeap.Heap Plain heap) : Stored (advanceHeap before heap) := by
  exact ⟨SourceCurrentConstrainedCapCurrentNative.advance Plain before.checked _ stored.current ready.checked.good
    ready.checked.semantic.ready.semantic guards
    (SourceCurrentAllocatedQueryMemo.advance_extension before.checked ⟨heap,before.checked.operations⟩ effects) rfl rfl,stored.merge,stored.slots⟩

variable {formulas : SourceGuards.Formulas FullSyntax.Formula} {solver : SourceGuards.Entailment FullSyntax.Formula} {base : Heap}
private def NodeGoal {record originals edits input before result after}
    (_actual : EditNode (width := width) record originals edits input before result after) (memos : Memos) :=
  ∀ inventory, SourceEqualityClassOrder.Coherent record → EqualityNormalize.Nontrivial record.paths →
    Populated edits → HasLeaf edits → Allowed record edits → Ready formulas solver inventory record originals base before →
    Available before.checked.native.machine.heap input → Safe edits input → Valid before.checked.native.machine.heap memos →
    Values base originals → Masks record originals → Stored before → AtLeaves edits input → Stored after ∧ Preserves input result
private def ChildrenGoal {record originals entries offset inputs before results after}
    (_actual : EditChildren (width := width) record originals entries offset inputs before results after) (memos : Memos) :=
  ∀ inventory, SourceEqualityClassOrder.Coherent record → EqualityNormalize.Nontrivial record.paths →
    Populated (.editBelow entries) → Allowed record (.editBelow entries) → Ready formulas solver inventory record originals base before →
    Values before.checked.native.machine.heap inputs → ChildrenSafe entries offset inputs → Valid before.checked.native.machine.heap memos →
    Values base originals → Masks record originals → Stored before → ChildrenAtLeaves entries offset inputs → Stored after ∧ All₂ Preserves inputs results
private def RowsGoal {record originals entries inputs before results after}
    (_actual : EditRows (width := width) record originals entries inputs before results after) (memos : Memos) :=
  ∀ inventory, SourceEqualityClassOrder.Coherent record → EqualityNormalize.Nontrivial record.paths →
    Populated (.editBelow entries) → Allowed record (.editBelow entries) → Ready formulas solver inventory record originals base before →
    Edges before.checked.native.machine.heap inputs → RowsSafe entries inputs → Valid before.checked.native.machine.heap memos →
    Values base originals → Masks record originals → Stored before → (∀ row ∈ inputs, ChildrenAtLeaves entries 0 row.children) →
    Stored after ∧ All₂ (fun original result => All₂ Preserves original.children result.children) inputs results

set_option maxHeartbeats 1600000 in
private theorem children_law {record originals entries offset inputs before results after memos final}
    {actual : EditChildren (width := width) record originals entries offset inputs before results after}
    (reads : ChildrenReads formulas solver base actual memos final) :
    ChildrenGoal (width := width) (formulas := formulas) (solver := solver) (base := base) actual memos := by
  have leafCase : ∀ {next record originals path value before result after memos saved}
      (receipt : SourceCurrentAllocatedSharedTargetLeaf.Receipt formulas solver next record originals base path value before result after memos saved),
      NodeGoal (width := width) (formulas := formulas) (solver := solver) (base := base) (.leaf receipt.actual) memos := by
    intro next record originals path value before result after memos saved receipt inventory coherent active _ _ _ ready available safe _ known masks stored placed
    have inputClosed : value.free = [] := by
      simpa only [SourceEqualityProjectionPathDomain.NodeClosed] using safe [] path (by simp only [leaves,List.mem_singleton])
    obtain ⟨inputDepth,inputCap⟩ := root_finite (placed [] path (by simp only [leaves,List.mem_singleton]))
    cases receipt.reads with
    | apply first query =>
      have forced := SourceCurrentRawCorridorSharedTargetCap.force_receipt known masks coherent active first ready stored
      obtain ⟨targetDepth,targetCap⟩ := forced.2
      have queried := SourceCurrentConstrainedCapCurrentNative.step (max targetDepth inputDepth) formulas solver query.actual
        first.ready.checked.good first.ready.checked.semantic forced.1.current first.available
        (first.effects.keeps.available value available) first.closed inputClosed
        (targetCap.mono (Nat.le_max_left _ _)) (inputCap.mono (Nat.le_max_right _ _))
      exact ⟨⟨queried.1,forced.1.merge,forced.1.slots⟩,fun path _ => .full path _ ⟨_,queried.2.1⟩⟩
  have emptyCase : ∀ {record originals entries state memos},
      NodeGoal (width := width) (formulas := formulas) (solver := solver) (base := base)
        (.empty (record := record) (originals := originals) (entries := entries) (state := state)) memos := by
    intro record originals entries state memos inventory _ _ _ _ _ _ _ _ _ _ _ stored _
    exact ⟨stored,fun _ raw => raw⟩
  have ordinaryCase : ∀ {record originals memos saved entries edges before rebuilt middle value heap entry depth free}
      {actual : EditRows record originals entries edges before rebuilt middle}
      {built : run (InternedConstructorTemplates.makeNode rebuilt) middle.checked.native.machine.heap = (value, heap)},
      RowsReads formulas solver base actual memos saved →
      RowsGoal (width := width) (formulas := formulas) (solver := solver) (base := base) actual memos →
      NodeGoal (width := width) (formulas := formulas) (solver := solver) (base := base)
        (.ordinary (entry := entry) (depth := depth) (free := free) actual built) memos := by
    intro record originals memos saved entries edges before rebuilt middle value heap entry depth free actual built reads ih
      inventory coherent active populated _ allowed ready available safe valid known masks stored placed
    have facts := ready.checked.semantic.ready.semantic.1.normal.facts
    have resident := InternedEdgeResidency.resident_edges _ facts.linked _ available.resident
    have related := ih inventory coherent active populated allowed ready resident (SourceCurrentEditDomains.ordinary_rows safe)
      valid known masks stored (ordinary_rows placed)
    obtain ⟨next,checked⟩ := SourceCurrentAllocatedSharedEditEffects.rows_effects reads populated allowed ready resident
      (SourceCurrentEditDomains.ordinary_rows safe) valid
    have currentFacts := checked.ready.checked.semantic.ready.semantic.1.normal.facts
    have preserved := node_preserves entry edges rebuilt depth free middle.checked.native.machine.heap
      currentFacts.coherent currentFacts.linked checked.available related.2
    have physical := SourceCurrentAllocatedSharedEditEffects.node_physical checked.ready rebuilt checked.available
    have guards := SourceCurrentConstrainedCapGuardHeap.preserve Plain _ _ related.1.current.1.guards
      (InternedShallowHeap.makeNode_noNewMu rebuilt middle.checked.native.machine.heap)
    exact ⟨by simpa only [built] using advance_stored _ related.1 physical.1 physical.2.1 guards,
      by simpa only [built] using preserved⟩
  have recursiveCase : ∀ {record originals memos current saved entries original before exposed heap value after}
      {recursive : SourceEqualityRequiredGraph.Recursive original}
      {head : SourceEqualityRequiredHead.Head original before.checked.native.machine.heap exposed heap}
      {body : EditNode record originals (.editBelow entries) exposed (advanceHeap before heap) value after},
      SourceCurrentRequiredQueryMemos.HeadReads head memos current →
      SourceCurrentSubsumesQueryMemos.Effect before.checked.native.machine.heap heap memos current →
      NodeReads formulas solver base body current saved →
      NodeGoal (width := width) (formulas := formulas) (solver := solver) (base := base) body current →
      NodeGoal (width := width) (formulas := formulas) (solver := solver) (base := base) (.recursive recursive head body) memos := by
    intro record originals memos current saved entries original before exposed heap value after recursive actual body
      headReads headGlobal bodyReads ih inventory coherent active populated nonempty allowed ready available safe _ known masks stored placed
    have hasLeaf := nonempty
    obtain ⟨path,action,member⟩ := nonempty
    have raw := placed path action member
    have bounded : Finite original := by
      cases raw with
      | full _ _ bounded => exact bounded
      | node => cases recursive
    obtain ⟨depth,bounded⟩ := bounded
    have physical := SourceCurrentAllocatedSharedEditEffects.head_physical ready actual available
    have guards := SourceCurrentConstrainedCapProjectionGuard.head Plain actual ready.checked.semantic ready.checked.costs available stored.current.1.guards
    have exposedCap := SourceCurrentConstrainedCapOpenExposure.head Plain depth actual ready.checked.semantic ready.checked.costs available
      bounded (SourceCurrentConstrainedCapGuardNative.stored Plain _ stored.current.1.guards)
    have nextStore := advance_stored heap stored physical.1 physical.2.1 guards
    have headSafe : Safe (.editBelow entries) exposed := by
      have checked := actual.verified ready.checked.semantic.ready available (recursive_closed recursive hasLeaf safe)
      exact closed_safe _ exposed heap headGlobal.semantic checked.2.1 checked.2.2.1
    have later := ih inventory coherent active populated hasLeaf allowed physical.1 physical.2.2 headSafe headGlobal.valid known masks nextStore
      (fun path _ _ => .full path _ ⟨depth,exposedCap.2⟩)
    have output := root_finite (later.2 [] (.full [] _ ⟨depth,exposedCap.2⟩))
    exact ⟨later.1,fun path _ => .full path _ output⟩
  have nilChildren : ∀ {record originals entries offset state memos},
      ChildrenGoal (width := width) (formulas := formulas) (solver := solver) (base := base)
        (.nil (record := record) (originals := originals) (entries := entries) (index := offset) (state := state)) memos := by
    intro record originals entries offset state memos inventory _ _ _ _ _ _ _ _ _ _ stored _
    exact ⟨stored,.nil⟩
  have unselectedCase : ∀ {record originals memos saved entries values before results after value} {offset : Nat}
      {absent : SourceEqualityNeededMap.lookup (offset : Int) entries = none}
      {rest : EditChildren record originals entries (offset + 1) values before results after},
      ChildrenReads formulas solver base rest memos saved →
      ChildrenGoal (width := width) (formulas := formulas) (solver := solver) (base := base) rest memos →
      ChildrenGoal (width := width) (formulas := formulas) (solver := solver) (base := base) (.unselected (value := value) offset absent rest) memos := by
    intro record originals memos saved entries values before results after value offset absent rest _ ih inventory coherent active
      populated allowed ready available safe valid known masks stored placed
    have later := ih inventory coherent active populated allowed ready (fun child member => available child (List.mem_cons_of_mem _ member))
      (SourceCurrentEditDomains.children_tail safe) valid known masks stored (children_tail placed)
    exact ⟨later.1,.cons (fun _ raw => raw) later.2⟩
  have selectedCase : ∀ {record originals memos current saved entries edits value before result middle values results after} {offset : Nat}
      {found : SourceEqualityNeededMap.lookup (offset : Int) entries = some edits}
      {first : EditNode record originals edits value before result middle}
      {rest : EditChildren record originals entries (offset + 1) values middle results after},
      NodeReads formulas solver base first memos current → ChildrenReads formulas solver base rest current saved →
      NodeGoal (width := width) (formulas := formulas) (solver := solver) (base := base) first memos →
      ChildrenGoal (width := width) (formulas := formulas) (solver := solver) (base := base) rest current →
      ChildrenGoal (width := width) (formulas := formulas) (solver := solver) (base := base) (.selected offset found first rest) memos := by
    intro record originals memos current saved entries edits value before result middle values results after offset found first rest
      firstReads _ firstIH restIH inventory coherent active populated allowed ready available safe valid known masks stored placed
    have member := SourceEqualityNeededMap.lookup_mem _ _ _ found
    have children := (show ∀ index child, (index,child) ∈ entries → Populated child ∧ HasLeaf child from by simpa only [Populated] using populated)
    have childAllowed : Allowed record edits := by rw [Allowed,All] at allowed; exact allowed _ _ member
    have firstSafe := safe 0 _ (by simpa using found) value rfl
    have related := firstIH inventory coherent active (children _ _ member).1 (children _ _ member).2 childAllowed ready
      (available _ List.mem_cons_self) firstSafe valid known masks stored (placed 0 edits (by simpa using found) value rfl)
    obtain ⟨middleInventory,checked⟩ := SourceCurrentAllocatedSharedEditEffects.node_effects firstReads
      (children _ _ member).1 (children _ _ member).2 childAllowed ready (available _ List.mem_cons_self) firstSafe valid
    have later := restIH middleInventory coherent active populated allowed checked.ready
      (fun original member => checked.effects.keeps.available original (available original (List.mem_cons_of_mem _ member)))
      (SourceCurrentEditDomains.children_tail safe) checked.globals.valid known masks related.1 (children_tail placed)
    exact ⟨later.1,.cons related.2 later.2⟩
  have nilRows : ∀ {record originals entries state memos},
      RowsGoal (width := width) (formulas := formulas) (solver := solver) (base := base)
        (.nil (record := record) (originals := originals) (entries := entries) (state := state)) memos := by
    intro record originals entries state memos inventory coherent active populated allowed ready resident safe valid known masks stored placed
    exact ⟨stored,.nil⟩
  have consCase : ∀ {record originals memos current saved entries before values middle result heap edges results after} {edge : EdgeValue Symbol Guard}
      {children : EditChildren record originals entries 0 edge.children before values middle}
      {rebuilt : run (InternedConstructorTemplates.makeEdge edge.entry.key.symbol edge.entry.key.constraint values)
        middle.checked.native.machine.heap = (result, heap)}
      {rest : EditRows record originals entries edges (advanceHeap middle heap) results after},
      ChildrenReads formulas solver base children memos current → RowsReads formulas solver base rest current saved →
      ChildrenGoal (width := width) (formulas := formulas) (solver := solver) (base := base) children memos →
      RowsGoal (width := width) (formulas := formulas) (solver := solver) (base := base) rest current →
      RowsGoal (width := width) (formulas := formulas) (solver := solver) (base := base) (.cons children rebuilt rest) memos := by
    intro record originals memos current saved entries before values middle result heap edges results after edge children rebuilt rest
      firstReads _ firstIH restIH inventory coherent active populated allowed ready resident safe valid known masks stored placed
    have facts := ready.checked.semantic.ready.semantic.1.normal.facts
    have available := facts.cached.edges edge.entry.key edge (resident _ List.mem_cons_self)
    have related := firstIH inventory coherent active populated allowed ready available (safe _ List.mem_cons_self)
      valid known masks stored (placed _ List.mem_cons_self)
    obtain ⟨middleInventory,checked⟩ := SourceCurrentAllocatedSharedEditEffects.children_effects firstReads populated allowed ready available (safe _ List.mem_cons_self) valid
    have field := (ready.checked.good.fields _ _ (resident _ List.mem_cons_self)).grows checked.effects.grows
    have physical := SourceCurrentAllocatedSharedEditEffects.edge_physical checked.ready edge.entry.key.symbol edge.entry.key.constraint values field checked.available
    have edgeReady : Ready formulas solver middleInventory record originals base (advanceHeap middle heap) := by simpa only [rebuilt] using physical.1
    have edgeKeeps : SourceEqualityRequiredCache.Keeps middle.checked.native.machine.heap heap := by
      have keeps := physical.2.1.keeps
      change SourceEqualityRequiredCache.Keeps middle.checked.native.machine.heap (run (makeEdge edge.entry.key.symbol edge.entry.key.constraint values) middle.checked.native.machine.heap).2 at keeps
      simpa only [rebuilt] using keeps
    have edgeStore : Stored (advanceHeap middle heap) := by
      have guards : SourceCurrentConstrainedCapGuardHeap.Heap Plain (run (makeEdge edge.entry.key.symbol edge.entry.key.constraint values) middle.checked.native.machine.heap).2 := related.1.current.1.guards
      simpa only [rebuilt] using advance_stored _ related.1 physical.1 physical.2.1 guards
    have currentValid := SourceQueryUnfoldMemo.valid_grows _ _ checked.ready.checked.semantic edgeKeeps current checked.globals.valid
    have later := restIH middleInventory coherent active populated allowed edgeReady
      (fun original member => InternedEdgeResidency.edge_grows _ _ (checked.effects.keeps.trans edgeKeeps).growth original (resident original (List.mem_cons_of_mem _ member)))
      (fun original member => safe original (List.mem_cons_of_mem _ member)) currentValid known masks edgeStore
      (fun original member => placed original (List.mem_cons_of_mem _ member))
    have sameChildren := InternedShallowValues.makeEdge_children edge.entry.key.symbol edge.entry.key.constraint values middle.checked.native.machine.heap
      checked.ready.checked.semantic.ready.semantic.1.normal.facts.coherent checked.ready.checked.semantic.ready.semantic.1.normal.facts.cached checked.available
    have same : result.children = values := by simpa only [rebuilt] using sameChildren
    exact ⟨later.1,.cons (by simpa only [same] using related.2) later.2⟩
  exact ChildrenReads.rec
    (motive_1 := fun {record originals edits value before result after} actual memos _ _ =>
      NodeGoal (width := width) (formulas := formulas) (solver := solver) (base := base) actual memos)
    (motive_2 := fun {record originals entries offset values before results after} actual memos _ _ =>
      ChildrenGoal (width := width) (formulas := formulas) (solver := solver) (base := base) actual memos)
    (motive_3 := fun {record originals entries edges before results after} actual memos _ _ =>
      RowsGoal (width := width) (formulas := formulas) (solver := solver) (base := base) actual memos)
    @leafCase @emptyCase @ordinaryCase @recursiveCase @nilChildren @unselectedCase @selectedCase @nilRows @consCase reads
private theorem list_law {record originals edits values before results after memos final}
    {actual : EditList (width := width) record originals edits values before results after}
    (reads : ListReads formulas solver base actual memos final)
    (inventory : Inventory) (coherent : SourceEqualityClassOrder.Coherent record) (active : EqualityNormalize.Nontrivial record.paths)
    (populated : Populated edits) (allowed : Allowed record edits)
    (ready : Ready formulas solver inventory record originals base before) (available : Values before.checked.native.machine.heap values)
    (safe : SourceCurrentAllocatedSharedEditEffects.ListSafe edits values) (valid : Valid before.checked.native.machine.heap memos)
    (known : Values base originals) (masks : Masks record originals) (stored : Stored before)
    (placed : ListAtLeaves edits values) :
    Stored after ∧ All₂ Preserves values results := by
  cases reads with
  | leaf => exact ⟨stored,forest_refl values⟩
  | children childReads => exact children_law childReads inventory coherent active populated allowed ready available safe valid known masks stored placed
end Actual

/-- Actual class edits preserve every raw endpoint corridor in the same ordered values. -/
theorem class_reads [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (record : SourceEqualityClassOrder.Record)
    (coherent : SourceEqualityClassOrder.Coherent record) (active : EqualityNormalize.Nontrivial record.paths)
    {values results : List Node} {before after : SourceEqualityNativeDemand.State width}
    {memo saved : SourceCurrentMemoMergeGraph.Memo Symbol Guard} {memos final : Memos}
    {actual : SourceCurrentAllocatedClassEdits.Class record values before memo results after saved}
    (reads : SourceCurrentAllocatedClassEdits.ClassReads formulas solver actual memos final)
    (ready : SourceCurrentConjunctionClassScan.Ready before)
    (admitted : SourceCurrentAllocatedNativeInventoryState.At formulas solver inventory before)
    (available : Values before.native.machine.heap values)
    (domains : ∀ path ∈ record.paths, SourceEqualityProjectionPathDomain.ForestClosed (path.map Int.ofNat) values)
    (stored : SourceCurrentMemoMergeEffects.Stored before.native.machine.heap memo)
    (covered : ∀ ambient, SourceCurrentMemoMergeLanguage.CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
    (valid : Valid before.native.machine.heap memos)
    (current : SourceCurrentConstrainedCapCurrentNative.At Plain before)
    (merged : SourceCurrentConstrainedCapMemoMerge.Stored Plain memo)
    (masks : ∀ index path, index::path ∈ record.paths → ∀ value,
      select values (Int.ofNat index) = some value → RawCorridor (path.map Int.ofNat) value) :
    ∃ next, SourceCurrentAllocatedClassEdits.Receipt formulas solver next record values before memo results after saved memos final ∧
      SourceCurrentConstrainedCapCurrentNative.At Plain after ∧ SourceCurrentConstrainedCapMemoMerge.Stored Plain saved ∧
      All₂ (fun original result => ∀ path, RawCorridor path original → RawCorridor path result) values results := by
  obtain ⟨next,receipt⟩ := SourceCurrentAllocatedClassEdits.verified formulas solver inventory record coherent active reads
    ready admitted available domains stored covered valid
  cases reads with
  | edit lower =>
    have initialReady := SourceCurrentAllocatedSharedTargetState.initial_ready formulas solver inventory record values
      before.native.machine.heap before memo ready admitted (SourceEqualityRequiredCache.pure_keeps _ ready.semantic.ready) stored covered
    have initialStore := SourceCurrentRequiredSharedTargetCap.initial_stored before memo current merged
    obtain ⟨entries,built⟩ := compiled_children record coherent active
    have safe : SourceCurrentAllocatedSharedEditEffects.ListSafe (compiled record) values := by
      rw [built]; exact compiled_safe record coherent values domains entries built
    have placed : ListAtLeaves (compiled record) values := by
      rw [built]; exact placement coherent built masks
    have retained := list_law lower inventory coherent active (compiled_populated record) (compiled_allowed record)
      initialReady available safe valid available masks initialStore placed
    exact ⟨next,receipt,retained.1.current,retained.1.merge,retained.2⟩

end MicroCFTA.SourceCurrentClassEndpointCorridors
