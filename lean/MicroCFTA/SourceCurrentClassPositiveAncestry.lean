import MicroCFTA.SourceCurrentRawCorridorSharedTargetPositivePositions
import MicroCFTA.SourceCurrentClassEndpointCorridors
import MicroCFTA.SourceCurrentCappedHeadPositivePosition
import MicroCFTA.SourceCurrentNormalizedChildSeparation

/-!
# Positive positions through one completed captured class

The class captures its literal entry forest. Each target uses that capture.
The actual reads retain positive stores and causal publication history at
each returned state. A copied position uses one record path and one suffix.
-/
namespace MicroCFTA.SourceCurrentClassPositiveAncestry
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
open SourceCurrentRequiredPositivePosition (PositiveAt)
open SourceCurrentNormalizedChildSeparation (Rel)
open SourceCurrentNativeMuPublication (History)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Row" => EdgeValue Symbol Guard
local notation "Heap" => InternedConstructorTemplates.State Symbol Guard
local notation "Ready" => SourceCurrentAllocatedSharedTargetState.Ready
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Valid" => EndpointMemoGateTrace.Valid
local notation "CapStored" => SourceCurrentRequiredSharedTargetCap.Stored
local notation "Plain" => (fun guard : Guard => SourceMemoGate.plain guard = true)
local notation "NativeSupport" => SourceCurrentNativeRequestPositivePositions.Support
local notation "MergeSupport" => SourceCurrentMergePositivePosition.Support
private def Finite (value : Node) := ∃ depth, Cap Plain depth value
private def AtLeaves (edits : Edits EqualityNormalize.Path) (value : Node) :=
  ∀ path action, (path,action) ∈ leaves edits → RawCorridor path value
private def ChildrenAtLeaves (entries : List (Int × Edits EqualityNormalize.Path)) (offset : Nat) (values : List Node) :=
  ∀ query edits, SourceEqualityNeededMap.lookup (Int.ofNat (offset+query)) entries = some edits →
    ∀ value, values[query]? = some value → AtLeaves edits value
private def Masks (record : SourceEqualityClassOrder.Record) (values : List Node) :=
  ∀ index path, index::path ∈ record.paths → ∀ value, select values (Int.ofNat index) = some value → RawCorridor (path.map Int.ofNat) value
private def Placed (address : List Nat) (edits : Edits EqualityNormalize.Path) :=
  ∀ path action, (path,action) ∈ leaves edits →
    ∃ suffix : List Nat, path = suffix.map Int.ofNat ∧ action = address ++ suffix
private def ChildrenPlaced (address : List Nat) (entries : List (Int × Edits EqualityNormalize.Path)) (offset : Nat) :=
  ∀ query edits, SourceEqualityNeededMap.lookup (Int.ofNat (offset+query)) entries = some edits →
    Placed (address ++ [offset+query]) edits
private def Back (record : SourceEqualityClassOrder.Record) (originals : List Node) (address : List Nat) (input result : Node) :=
  ∀ q, PositiveAt result q → PositiveAt input q ∨
    ∃ index path original, originals[index]? = some original ∧ PositiveAt original path ∧
      Rel [record.paths] (address ++ q) (index :: path)
private def ChildrenBack (record : SourceEqualityClassOrder.Record) (originals : List Node) (address : List Nat)
    (offset : Nat) (inputs results : List Node) :=
  ∀ index result, results[index]? = some result → ∃ input, inputs[index]? = some input ∧
    Back record originals (address ++ [offset+index]) input result
private def SlotBack (originals : List Node) (paths : List (List Int)) (value : Node) :=
  ∀ q, PositiveAt value q → ∃ index path original,
    ((index::path).map Int.ofNat) ∈ paths ∧ originals[index]? = some original ∧ PositiveAt original (path++q)
private structure Stores [DecidableEq (EdgeKey Symbol Guard)] (record : SourceEqualityClassOrder.Record) (originals : List Node) (state : SharedState width) : Prop where
  caps : CapStored state
  native : NativeSupport state.checked.native.machine.heap state.checked.native
  causal : Nonempty (History empty state.checked.native.machine.heap)
  merged : MergeSupport state.memo
  slots : ∀ action value, state.targets action = some value →
    SlotBack originals (SourceEqualityClassTarget.operandPaths record.paths action) value

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
    exact parts.2 ▸ masks query tail included value (by simpa only [SourceCurrentEditDomains.select_natural] using chosen)
private theorem compiled_placed {record} (coherent : SourceEqualityClassOrder.Coherent record) : Placed [] (compiled record) := by
  intro path action member
  have original := (SourceEqualityEditCompiledPaths.build_leaves _ (compiled_disjoint record coherent)).mem_iff.mp member
  obtain ⟨natural,_included,same⟩ := List.mem_map.mp original
  have fields := Prod.mk.inj same
  exact ⟨natural,fields.1.symm,by simpa only [List.nil_append,id] using fields.2.symm⟩
private theorem placed_children {address entries} (placed : Placed address (.editBelow entries)) : ChildrenPlaced address entries 0 := by
  intro query edits found path action member
  obtain ⟨suffix,signed,token⟩ := placed (Int.ofNat query::path) action
    (below_member entries _ edits (SourceEqualityNeededMap.lookup_mem _ _ _ (by simpa using found)) path action member)
  cases suffix with
  | nil => cases signed
  | cons index tail =>
    have fields := List.cons.inj signed
    have sameIndex : query = index := Int.ofNat.inj fields.1
    subst index
    exact ⟨tail,fields.2,by simpa only [Nat.zero_add,List.append_assoc,List.singleton_append] using token⟩
private theorem placed_tail {address entries offset} (placed : ChildrenPlaced address entries offset) : ChildrenPlaced address entries (offset+1) := by
  intro query edits found
  simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using
    placed (query+1) edits (by simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using found)
private theorem children_back_refl (record originals address offset) (values : List Node) : ChildrenBack record originals address offset values values := by
  intro index result found
  exact ⟨result,found,fun _ positive => .inl positive⟩

section Actual
variable [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
private theorem node_back (record originals address entry) (inputs outputs : List Row) (depth free) (state : Heap)
    (facts : InternedNestedFacts.Facts state) (resident : Edges state outputs)
    (related : All₂ (fun input output => output.entry.key.constraint = input.entry.key.constraint ∧
      ChildrenBack record originals address 0 input.children output.children) inputs outputs) :
    Back record originals address (.node entry inputs depth free) (run (makeNode outputs) state).1 := by
  have fields := EqualityLeafProjectionPhysical.makeNode_edges outputs state facts.coherent facts.linked resident
  have ordinary := SourceEqualityRequiredCache.node_ordinary outputs state facts resident
  have raw : ∀ row ∈ nodeEdges (run (makeNode outputs) state).1, row ∈ outputs := by
    intro row member
    exact (List.mem_filter.mp (canonicalEdges_member _ row (fields ▸ member))).1
  generalize computed : (run (makeNode outputs) state).1 = result at ordinary raw
  intro path positive
  cases positive with
  | root index row found nonplain =>
    obtain ⟨rawIndex,rawFound⟩ := List.mem_iff_getElem?.mp (raw row (List.mem_of_getElem? found))
    obtain ⟨source,chosen,law⟩ := SourceEqualityProjectionLanguage.all₂_selected related rawIndex row rawFound
    exact .inl (.root rawIndex source chosen (by simpa only [law.1] using nonplain))
  | child index childIndex row child found chosen positive =>
    obtain ⟨rawIndex,rawFound⟩ := List.mem_iff_getElem?.mp (raw row (List.mem_of_getElem? found))
    obtain ⟨source,sourceFound,law⟩ := SourceEqualityProjectionLanguage.all₂_selected related rawIndex row rawFound
    obtain ⟨original,originalFound,back⟩ := law.2 childIndex child chosen
    rcases back _ positive with inherited | captured
    · exact .inl (.child rawIndex childIndex source original sourceFound originalFound inherited)
    · exact .inr (by simpa only [Nat.zero_add,List.append_assoc,List.singleton_append] using captured)
  | member => cases ordinary

variable [DecidableEq Symbol]
private theorem advance_stores {formulas solver inventory record originals base} {before : SharedState width}
    (heap : Heap) (stored : Stores record originals before)
    (ready : Ready formulas solver inventory record originals base (advanceHeap before heap))
    (effects : SourceCurrentConjunctionRowsAllocation.Effects (SourceCurrentAllocatedNativeEffects.physical before.checked)
      (SourceCurrentAllocatedNativeEffects.physical (advanceHeap before heap).checked))
    (guards : SourceCurrentConstrainedCapGuardHeap.Heap Plain heap)
    (interval : History before.checked.native.machine.heap heap) : Stores record originals (advanceHeap before heap) := by
  have extension := SourceCurrentAllocatedQueryMemo.advance_extension before.checked ⟨heap,before.checked.operations⟩ effects
  have current := SourceCurrentConstrainedCapCurrentNative.advance Plain before.checked _ stored.caps.current ready.checked.good
    ready.checked.semantic.ready.semantic guards extension rfl rfl
  have supported := SourceCurrentNativePositiveSupportAdvance.advance before.checked _ stored.caps.current stored.native ready.checked.good extension rfl rfl
  obtain ⟨earlier⟩ := stored.causal
  exact ⟨⟨current,stored.caps.merge,stored.caps.slots⟩,supported,⟨.trans earlier interval⟩,stored.merged,stored.slots⟩

variable {formulas : SourceGuards.Formulas FullSyntax.Formula} {solver : SourceGuards.Entailment FullSyntax.Formula} {base : Heap}
private def NodeGoal {record originals edits input before result after}
    (_actual : EditNode (width := width) record originals edits input before result after) (memos : Memos) :=
  ∀ inventory address, SourceEqualityClassOrder.Coherent record → EqualityNormalize.Nontrivial record.paths →
    Populated edits → HasLeaf edits → Allowed record edits → Ready formulas solver inventory record originals base before →
    Available before.checked.native.machine.heap input → Safe edits input → Valid before.checked.native.machine.heap memos →
    Values base originals → Masks record originals → Stores record originals before → AtLeaves edits input → Placed address edits →
    Stores record originals after ∧ Back record originals address input result
private def ChildrenGoal {record originals entries offset inputs before results after}
    (_actual : EditChildren (width := width) record originals entries offset inputs before results after) (memos : Memos) :=
  ∀ inventory address, SourceEqualityClassOrder.Coherent record → EqualityNormalize.Nontrivial record.paths →
    Populated (.editBelow entries) → Allowed record (.editBelow entries) → Ready formulas solver inventory record originals base before →
    Values before.checked.native.machine.heap inputs → ChildrenSafe entries offset inputs → Valid before.checked.native.machine.heap memos →
    Values base originals → Masks record originals → Stores record originals before → ChildrenAtLeaves entries offset inputs → ChildrenPlaced address entries offset →
    Stores record originals after ∧ ChildrenBack record originals address offset inputs results
private def RowsGoal {record originals entries inputs before results after}
    (_actual : EditRows (width := width) record originals entries inputs before results after) (memos : Memos) :=
  ∀ inventory address, SourceEqualityClassOrder.Coherent record → EqualityNormalize.Nontrivial record.paths →
    Populated (.editBelow entries) → Allowed record (.editBelow entries) → Ready formulas solver inventory record originals base before →
    Edges before.checked.native.machine.heap inputs → RowsSafe entries inputs → Valid before.checked.native.machine.heap memos →
    Values base originals → Masks record originals → Stores record originals before → (∀ row ∈ inputs, ChildrenAtLeaves entries 0 row.children) → ChildrenPlaced address entries 0 →
    Stores record originals after ∧ All₂ (fun input output => output.entry.key.constraint = input.entry.key.constraint ∧
      ChildrenBack record originals address 0 input.children output.children) inputs results

set_option maxHeartbeats 2000000 in
private theorem children_law {record originals entries offset inputs before results after memos final}
    {actual : EditChildren (width := width) record originals entries offset inputs before results after}
    (reads : ChildrenReads formulas solver base actual memos final) :
    ChildrenGoal (width := width) (formulas := formulas) (solver := solver) (base := base) actual memos := by
  have leafCase : ∀ {next record originals path value before result after memos saved}
      (receipt : SourceCurrentAllocatedSharedTargetLeaf.Receipt formulas solver next record originals base path value before result after memos saved),
      NodeGoal (width := width) (formulas := formulas) (solver := solver) (base := base) (.leaf receipt.actual) memos := by
    intro next record originals path value before result after memos saved receipt inventory address coherent active _ _ allowed ready available safe _ known masks stored placed located
    have inputClosed : value.free = [] := by
      simpa only [SourceEqualityProjectionPathDomain.NodeClosed] using safe [] path (by simp only [leaves,List.mem_singleton])
    obtain ⟨inputDepth,inputCap⟩ := root_finite (placed [] path (by simp only [leaves,List.mem_singleton]))
    obtain ⟨suffix,signed,token⟩ := located [] path (by simp only [leaves,List.mem_singleton])
    have empty : suffix = [] := List.map_eq_nil_iff.mp signed.symm
    subst suffix
    have sameToken : path = address := by simpa only [List.append_nil] using token
    have own : path ∈ record.paths := by simpa only [Allowed,All] using allowed
    cases receipt.reads with
    | apply first query =>
      obtain ⟨causal⟩ := stored.causal
      obtain ⟨forcedCaps,forcedNative,forcedCausal,forcedMerge,forcedSlots⟩ :=
        SourceCurrentRawCorridorSharedTargetPositivePositions.force_receipt known masks coherent active first ready stored.caps stored.native causal stored.merged stored.slots
      obtain ⟨targetDepth,targetCap⟩ := forcedCaps.slots path _ first.present
      obtain ⟨currentCausal⟩ := forcedCausal
      obtain ⟨nextCurrent,nextNative,nextCausal,nextCap,back⟩ := SourceCurrentNativeCurrentPositivePositions.step
        (max targetDepth inputDepth) formulas solver query.actual first.ready.checked.good first.ready.checked.semantic
        forcedCaps.current forcedNative currentCausal first.available (first.effects.keeps.available value available)
        first.closed inputClosed (targetCap.mono (Nat.le_max_left _ _)) (inputCap.mono (Nat.le_max_right _ _))
      refine ⟨⟨⟨nextCurrent,forcedCaps.merge,forcedCaps.slots⟩,nextNative,nextCausal,forcedMerge,forcedSlots⟩,?_⟩
      intro q positive
      rcases back q positive with target | inherited
      · obtain ⟨index,tail,original,member,found,positive⟩ := forcedSlots path _ first.present q target
        change ((index::tail).map Int.ofNat) ∈ (EqualityNarrowing.others record.paths path).map (List.map Int.ofNat) at member
        obtain ⟨natural,included,same⟩ := List.mem_map.mp member
        have naturalSame : natural = index::tail := by
          have converted := congrArg (List.map Int.toNat) same
          simpa only [List.map_map,Function.comp_def,Int.ofNat_eq_natCast,Int.toNat_natCast,List.map_id_fun',id] using converted
        have competing : index::tail ∈ record.paths := naturalSame ▸ (List.mem_filter.mp included).1
        refine .inr ⟨index,tail++q,original,found,positive,?_⟩
        simpa only [sameToken,List.cons_append] using
          (Rel.member record.paths (by simp) path (index::tail) own competing q)
      · exact .inl inherited
  have emptyCase : ∀ {record originals entries state memos},
      NodeGoal (width := width) (formulas := formulas) (solver := solver) (base := base)
        (.empty (record := record) (originals := originals) (entries := entries) (state := state)) memos := by
    intro record originals entries state memos inventory address _ _ _ _ _ _ _ _ _ _ _ stored _ _
    exact ⟨stored,fun _ positive => .inl positive⟩
  have ordinaryCase : ∀ {record originals memos saved entries edges before rebuilt middle value heap entry depth free}
      {actual : EditRows record originals entries edges before rebuilt middle}
      {built : run (makeNode rebuilt) middle.checked.native.machine.heap = (value, heap)},
      RowsReads formulas solver base actual memos saved →
      RowsGoal (width := width) (formulas := formulas) (solver := solver) (base := base) actual memos →
      NodeGoal (width := width) (formulas := formulas) (solver := solver) (base := base)
        (.ordinary (entry := entry) (depth := depth) (free := free) actual built) memos := by
    intro record originals memos saved entries edges before rebuilt middle value heap entry depth free actual built reads ih
      inventory address coherent active populated _ allowed ready available safe valid known masks stored placed located
    have facts := ready.checked.semantic.ready.semantic.1.normal.facts
    have resident := resident_edges _ facts.linked _ available.resident
    have related := ih inventory address coherent active populated allowed ready resident (SourceCurrentEditDomains.ordinary_rows safe)
      valid known masks stored (ordinary_rows placed) (placed_children located)
    obtain ⟨next,checked⟩ := SourceCurrentAllocatedSharedEditEffects.rows_effects reads populated allowed ready resident
      (SourceCurrentEditDomains.ordinary_rows safe) valid
    have currentFacts := checked.ready.checked.semantic.ready.semantic.1.normal.facts
    have preserved := node_back record originals address entry edges rebuilt depth free middle.checked.native.machine.heap
      currentFacts checked.available related.2
    have physical := SourceCurrentAllocatedSharedEditEffects.node_physical checked.ready rebuilt checked.available
    have guards := SourceCurrentConstrainedCapGuardHeap.preserve Plain _ _ related.1.caps.current.1.guards
      (InternedShallowHeap.makeNode_noNewMu rebuilt middle.checked.native.machine.heap)
    have interval : History middle.checked.native.machine.heap (run (makeNode rebuilt) middle.checked.native.machine.heap).2 :=
      .retain _ _ (InternedShallowHeap.makeNode_noNewMu rebuilt middle.checked.native.machine.heap)
    exact ⟨by simpa only [built] using advance_stores _ related.1 physical.1 physical.2.1 guards interval,
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
      headReads headGlobal bodyReads ih inventory address coherent active populated nonempty allowed ready available safe _ known masks stored placed located
    have hasLeaf := nonempty
    obtain ⟨path,action,member⟩ := nonempty
    have raw := placed path action member
    have bounded : Finite original := by
      cases raw with
      | full _ _ bounded => exact bounded
      | node => cases recursive
    obtain ⟨depth,bounded⟩ := bounded
    have physical := SourceCurrentAllocatedSharedEditEffects.head_physical ready actual available
    have guards := SourceCurrentConstrainedCapProjectionGuard.head Plain actual ready.checked.semantic ready.checked.costs available stored.caps.current.1.guards
    have exposedCap := SourceCurrentConstrainedCapOpenExposure.head Plain depth actual ready.checked.semantic ready.checked.costs available
      bounded (SourceCurrentConstrainedCapGuardNative.stored Plain _ stored.caps.current.1.guards)
    obtain ⟨interval⟩ := SourceCurrentRequiredPublicationHistory.head actual ready.checked.semantic ready.checked.costs available
    have nextStore := advance_stores heap stored physical.1 physical.2.1 guards interval
    have headSafe : Safe (.editBelow entries) exposed := by
      have checked := actual.verified ready.checked.semantic.ready available (recursive_closed recursive hasLeaf safe)
      exact closed_safe _ exposed heap headGlobal.semantic checked.2.1 checked.2.2.1
    have later := ih inventory address coherent active populated hasLeaf allowed physical.1 physical.2.2 headSafe headGlobal.valid known masks nextStore
      (fun path _ _ => .full path _ ⟨depth,exposedCap.2⟩) located
    refine ⟨later.1,?_⟩
    intro q positive
    rcases later.2 q positive with inherited | captured
    · exact .inl (SourceCurrentCappedHeadPositivePosition.head actual ready.checked.semantic ready.checked.costs available
        stored.caps.current.1.guards depth bounded inherited)
    · exact .inr captured
  have nilChildren : ∀ {record originals entries offset state memos},
      ChildrenGoal (width := width) (formulas := formulas) (solver := solver) (base := base)
        (.nil (record := record) (originals := originals) (entries := entries) (index := offset) (state := state)) memos := by
    intro record originals entries offset state memos inventory address _ _ _ _ _ _ _ _ _ _ stored _ _
    exact ⟨stored,by intro index result found; cases index <;> cases found⟩
  have unselectedCase : ∀ {record originals memos saved entries values before results after value} {offset : Nat}
      {absent : SourceEqualityNeededMap.lookup (offset : Int) entries = none}
      {rest : EditChildren record originals entries (offset+1) values before results after},
      ChildrenReads formulas solver base rest memos saved →
      ChildrenGoal (width := width) (formulas := formulas) (solver := solver) (base := base) rest memos →
      ChildrenGoal (width := width) (formulas := formulas) (solver := solver) (base := base) (.unselected (value := value) offset absent rest) memos := by
    intro record originals memos saved entries values before results after value offset absent rest _ ih inventory address coherent active
      populated allowed ready available safe valid known masks stored placed located
    have later := ih inventory address coherent active populated allowed ready (fun child member => available child (List.mem_cons_of_mem _ member))
      (SourceCurrentEditDomains.children_tail safe) valid known masks stored (children_tail placed) (placed_tail located)
    refine ⟨later.1,?_⟩
    intro index result found
    cases index with
    | zero => exact ⟨value,rfl,by cases Option.some.inj found; intro _ positive; exact .inl positive⟩
    | succ index => simpa only [List.getElem?_cons_succ,Nat.succ_eq_add_one,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using later.2 index result found
  have selectedCase : ∀ {record originals memos current saved entries edits value before result middle values results after} {offset : Nat}
      {found : SourceEqualityNeededMap.lookup (offset : Int) entries = some edits}
      {first : EditNode record originals edits value before result middle}
      {rest : EditChildren record originals entries (offset+1) values middle results after},
      NodeReads formulas solver base first memos current → ChildrenReads formulas solver base rest current saved →
      NodeGoal (width := width) (formulas := formulas) (solver := solver) (base := base) first memos →
      ChildrenGoal (width := width) (formulas := formulas) (solver := solver) (base := base) rest current →
      ChildrenGoal (width := width) (formulas := formulas) (solver := solver) (base := base) (.selected offset found first rest) memos := by
    intro record originals memos current saved entries edits value before result middle values results after offset found first rest
      firstReads _ firstIH restIH inventory address coherent active populated allowed ready available safe valid known masks stored placed located
    have member := SourceEqualityNeededMap.lookup_mem _ _ _ found
    have children := (show ∀ index child, (index,child) ∈ entries → Populated child ∧ HasLeaf child from by simpa only [Populated] using populated)
    have childAllowed : Allowed record edits := by rw [Allowed,All] at allowed; exact allowed _ _ member
    have firstSafe := safe 0 _ (by simpa using found) value rfl
    have related := firstIH inventory (address++[offset]) coherent active (children _ _ member).1 (children _ _ member).2 childAllowed ready
      (available _ List.mem_cons_self) firstSafe valid known masks stored (placed 0 edits (by simpa using found) value rfl)
      (by simpa only [Nat.add_zero] using located 0 edits (by simpa using found))
    obtain ⟨middleInventory,checked⟩ := SourceCurrentAllocatedSharedEditEffects.node_effects firstReads
      (children _ _ member).1 (children _ _ member).2 childAllowed ready (available _ List.mem_cons_self) firstSafe valid
    have later := restIH middleInventory address coherent active populated allowed checked.ready
      (fun original member => checked.effects.keeps.available original (available original (List.mem_cons_of_mem _ member)))
      (SourceCurrentEditDomains.children_tail safe) checked.globals.valid known masks related.1 (children_tail placed) (placed_tail located)
    refine ⟨later.1,?_⟩
    intro index output chosen
    cases index with
    | zero =>
      have same : result = output := Option.some.inj chosen
      subst output
      exact ⟨value,rfl,by simpa only [Nat.add_zero] using related.2⟩
    | succ index => simpa only [List.getElem?_cons_succ,Nat.succ_eq_add_one,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using later.2 index output chosen
  have nilRows : ∀ {record originals entries state memos},
      RowsGoal (width := width) (formulas := formulas) (solver := solver) (base := base)
        (.nil (record := record) (originals := originals) (entries := entries) (state := state)) memos := by
    intro record originals entries state memos inventory address _ _ _ _ _ _ _ _ _ _ stored _ _
    exact ⟨stored,.nil⟩
  have consCase : ∀ {record originals memos current saved entries before values middle result heap edges results after} {edge : Row}
      {children : EditChildren record originals entries 0 edge.children before values middle}
      {rebuilt : run (makeEdge edge.entry.key.symbol edge.entry.key.constraint values) middle.checked.native.machine.heap = (result,heap)}
      {rest : EditRows record originals entries edges (advanceHeap middle heap) results after},
      ChildrenReads formulas solver base children memos current → RowsReads formulas solver base rest current saved →
      ChildrenGoal (width := width) (formulas := formulas) (solver := solver) (base := base) children memos →
      RowsGoal (width := width) (formulas := formulas) (solver := solver) (base := base) rest current →
      RowsGoal (width := width) (formulas := formulas) (solver := solver) (base := base) (.cons children rebuilt rest) memos := by
    intro record originals memos current saved entries before values middle result heap edges results after edge children rebuilt rest
      firstReads _ firstIH restIH inventory address coherent active populated allowed ready resident safe valid known masks stored placed located
    have facts := ready.checked.semantic.ready.semantic.1.normal.facts
    have available := facts.cached.edges edge.entry.key edge (resident _ List.mem_cons_self)
    have related := firstIH inventory address coherent active populated allowed ready available (safe _ List.mem_cons_self)
      valid known masks stored (placed _ List.mem_cons_self) located
    obtain ⟨middleInventory,checked⟩ := SourceCurrentAllocatedSharedEditEffects.children_effects firstReads populated allowed ready available (safe _ List.mem_cons_self) valid
    have field := (ready.checked.good.fields _ _ (resident _ List.mem_cons_self)).grows checked.effects.grows
    have physical := SourceCurrentAllocatedSharedEditEffects.edge_physical checked.ready edge.entry.key.symbol edge.entry.key.constraint values field checked.available
    have edgeReady : Ready formulas solver middleInventory record originals base (advanceHeap middle heap) := by simpa only [rebuilt] using physical.1
    have edgeKeeps : Keeps middle.checked.native.machine.heap heap := by
      have keeps := physical.2.1.keeps
      change Keeps middle.checked.native.machine.heap (run (makeEdge edge.entry.key.symbol edge.entry.key.constraint values) middle.checked.native.machine.heap).2 at keeps
      simpa only [rebuilt] using keeps
    have interval : History middle.checked.native.machine.heap heap := by
      have same : heap.nodeRecords = middle.checked.native.machine.heap.nodeRecords := by
        have actual := congrArg Prod.snd rebuilt
        exact (congrArg State.nodeRecords actual).symm
      exact .retain _ _ (fun _ _ _ _ _ present => same ▸ present)
    have edgeStore : Stores record originals (advanceHeap middle heap) := by
      have guards : SourceCurrentConstrainedCapGuardHeap.Heap Plain (run (makeEdge edge.entry.key.symbol edge.entry.key.constraint values) middle.checked.native.machine.heap).2 := related.1.caps.current.1.guards
      simpa only [rebuilt] using advance_stores _ related.1 physical.1 physical.2.1 guards (by simpa only [rebuilt] using interval)
    have currentValid := SourceQueryUnfoldMemo.valid_grows _ _ checked.ready.checked.semantic edgeKeeps current checked.globals.valid
    have later := restIH middleInventory address coherent active populated allowed edgeReady
      (fun original member => InternedEdgeResidency.edge_grows _ _ (checked.effects.keeps.trans edgeKeeps).growth original (resident original (List.mem_cons_of_mem _ member)))
      (fun original member => safe original (List.mem_cons_of_mem _ member)) currentValid known masks edgeStore
      (fun original member => placed original (List.mem_cons_of_mem _ member)) located
    have sameFields := MergedPhysicalGroupEdges.makeEdge_fields middle.checked.native.machine.heap
      checked.ready.checked.semantic.ready.semantic.1.normal.facts edge.entry.key.symbol edge.entry.key.constraint values checked.available
    rw [rebuilt] at sameFields
    exact ⟨later.1,.cons ⟨sameFields.2.1,by simpa only [sameFields.2.2] using related.2⟩ later.2⟩
  exact ChildrenReads.rec
    (motive_1 := fun {record originals edits value before result after} actual memos _ _ =>
      NodeGoal (width := width) (formulas := formulas) (solver := solver) (base := base) actual memos)
    (motive_2 := fun {record originals entries offset values before results after} actual memos _ _ =>
      ChildrenGoal (width := width) (formulas := formulas) (solver := solver) (base := base) actual memos)
    (motive_3 := fun {record originals entries edges before results after} actual memos _ _ =>
      RowsGoal (width := width) (formulas := formulas) (solver := solver) (base := base) actual memos)
    @leafCase @emptyCase @ordinaryCase @recursiveCase @nilChildren @unselectedCase @selectedCase @nilRows @consCase reads
private def ListAtLeaves (edits : Edits EqualityNormalize.Path) (values : List Node) : Prop :=
  match edits with | .editAt _ => True | .editBelow entries => ChildrenAtLeaves entries 0 values
private theorem list_law {record originals edits inputs before results after memos final}
    {actual : EditList (width := width) record originals edits inputs before results after}
    (reads : ListReads formulas solver base actual memos final)
    (inventory : Inventory) (coherent : SourceEqualityClassOrder.Coherent record) (active : EqualityNormalize.Nontrivial record.paths)
    (populated : Populated edits) (allowed : Allowed record edits)
    (ready : Ready formulas solver inventory record originals base before) (available : Values before.checked.native.machine.heap inputs)
    (safe : SourceCurrentAllocatedSharedEditEffects.ListSafe edits inputs) (valid : Valid before.checked.native.machine.heap memos)
    (known : Values base originals) (masks : Masks record originals) (stored : Stores record originals before)
    (placed : ListAtLeaves edits inputs) (located : Placed [] edits) :
    Stores record originals after ∧ ChildrenBack record originals [] 0 inputs results := by
  cases reads with
  | leaf => exact ⟨stored,children_back_refl _ _ _ _ _⟩
  | children childReads =>
    exact children_law childReads inventory [] coherent active populated allowed ready available safe valid known masks stored placed (placed_children located)
end Actual

/-- One completed class retains current stores and traces each positive output to its literal capture. -/
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
      select values (Int.ofNat index) = some value → RawCorridor (path.map Int.ofNat) value)
    (supported : NativeSupport before.native.machine.heap before.native)
    (causal : History empty before.native.machine.heap) (positiveMemo : MergeSupport memo) :
    ∃ next, SourceCurrentAllocatedClassEdits.Receipt formulas solver next record values before memo results after saved memos final ∧
      SourceCurrentConstrainedCapCurrentNative.At Plain after ∧ SourceCurrentConstrainedCapMemoMerge.Stored Plain saved ∧
      All₂ (fun original result => ∀ path, RawCorridor path original → RawCorridor path result) values results ∧
      NativeSupport after.native.machine.heap after.native ∧ Nonempty (History empty after.native.machine.heap) ∧ MergeSupport saved ∧
      ∀ outputIndex result, results[outputIndex]? = some result → ∀ residual, PositiveAt result residual →
        ∃ inputIndex originalPath original, values[inputIndex]? = some original ∧ PositiveAt original originalPath ∧
          Rel [record.paths] (outputIndex::residual) (inputIndex::originalPath) := by
  obtain ⟨next,receipt,currentAfter,mergedAfter,corridors⟩ := SourceCurrentClassEndpointCorridors.class_reads
    formulas solver inventory record coherent active reads ready admitted available domains stored covered valid current merged masks
  refine ⟨next,receipt,currentAfter,mergedAfter,corridors,?_⟩
  cases reads with
  | edit lower =>
    have initialReady := SourceCurrentAllocatedSharedTargetState.initial_ready formulas solver inventory record values
      before.native.machine.heap before memo ready admitted (pure_keeps _ ready.semantic.ready) stored covered
    have initialStore : Stores record values (SourceCurrentAllocatedSharedTargetState.initial before memo) :=
      ⟨SourceCurrentRequiredSharedTargetCap.initial_stored before memo current merged,supported,⟨causal⟩,positiveMemo,
        by intro action value absent; cases absent⟩
    obtain ⟨entries,built⟩ := compiled_children record coherent active
    have safe : SourceCurrentAllocatedSharedEditEffects.ListSafe (compiled record) values := by
      rw [built]; exact compiled_safe record coherent values domains entries built
    have placed : ListAtLeaves (compiled record) values := by
      rw [built]; exact placement coherent built masks
    have retained := list_law lower inventory coherent active (compiled_populated record) (compiled_allowed record)
      initialReady available safe valid available masks initialStore placed (compiled_placed coherent)
    refine ⟨retained.1.native,retained.1.causal,retained.1.merged,?_⟩
    intro outputIndex result found residual positive
    obtain ⟨original,chosen,back⟩ := retained.2 outputIndex result found
    rcases back residual positive with inherited | captured
    · exact ⟨outputIndex,residual,original,chosen,inherited,.refl _⟩
    · exact (by simpa only [List.nil_append,Nat.zero_add,List.singleton_append] using captured)

end MicroCFTA.SourceCurrentClassPositiveAncestry
