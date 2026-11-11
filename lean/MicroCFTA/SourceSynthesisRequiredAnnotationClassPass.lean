import MicroCFTA.SourceSynthesisRequiredAnnotationEditRetention
import MicroCFTA.SourceSynthesisNativeTypeClassPass

/-!
# Required annotation heads through the actual class pass

A protected path has an ordinary value at each visited position, including
its endpoint. Empty values satisfy the property. Compiled placement and
source endpoint exclusion prevent a leaf edit at any protected ancestor.
Actual row reconstruction and the tail-first class fold preserve the path.
The source application law derives exclusion from the same precheck and
selected Scan reads. Membership in a retained required path remains separate.
-/
namespace MicroCFTA.SourceSynthesisRequiredAnnotationClassPass
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values Edges)
open MergedColdReaderClosedInputs (ClosedValues ClosedEdges)
open SourceEqualityRequiredCache (Ordinary)
open SourceEqualityEdits SourceEqualityEditLeafPaths
open SourceCurrentAllocatedSharedEditGraph
open SourceCurrentHereditaryTypePaths (ForestPath)
open SourceCurrentHereditaryTypeEditPlan
open SourceCurrentHereditaryTypeRouteConstructors (ForestRoutes)
open SourceCurrentEditDomains (Populated)
open SourceSynthesisRequiredAnnotationEditRetention (Placed child_placed compiled_placed)
open SourceSynthesisTypeSyntax (Library)
open SourceSynthesisGeneralizeSyntax (Guard)
open SourceSynthesisNativeTypeTrace (Origin)
open SourceCurrentAllocatedClassEdits (Class)
open SourceCurrentAllocatedClassPass (Fold Pass)
open SourceCurrentAllocatedSharedTargetState (initial)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Ready" => SourceSynthesisNativeTypeSharedState.Ready
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Memo" => SourceCurrentMemoMergeGraph.Memo Symbol Guard

/-- Every visited value, including the endpoint, is empty or ordinary. -/
def OrdinaryAt : List Nat → Node → Prop
  | [], value => Ordinary value
  | _ :: _, .empty => True
  | index :: path, .node _ rows _ _ =>
      ∀ row ∈ rows, ∀ child, row.children[index]? = some child → OrdinaryAt path child
  | _ :: _, _ => False

/-- A selected physical forest position has the protected ordinary path. -/
def ForestOrdinaryAt (index : Nat) (path : List Nat) (values : List Node) : Prop :=
  ∀ value, values[index]? = some value → OrdinaryAt path value

/-- Child zero of each ordinary row has an ordinary head. -/
abbrev FirstOrdinary (value : Node) : Prop := OrdinaryAt [0] value

/-- The literal function operand is forest position two. -/
abbrev AtFunction (values : List Node) : Prop := ForestOrdinaryAt 2 [0] values

/-- No endpoint of the class replaces the protected value or an ancestor. -/
def Excluded (record : SourceEqualityClassOrder.Record) (path : EqualityNormalize.Path) : Prop :=
  ∀ endpoint ∈ record.paths, ¬ endpoint.IsPrefix path

/-- An empty protected path still checks the value's head. -/
theorem OrdinaryAt.nil_iff (value : Node) : OrdinaryAt [] value ↔ Ordinary value := Iff.rfl

/-- Every protected path starts with an ordinary head. -/
theorem OrdinaryAt.ordinary {path : List Nat} {value : Node} (shape : OrdinaryAt path value) :
    Ordinary value := by
  cases path with
  | nil => exact shape
  | cons index path =>
      cases value with
      | empty | node => trivial
      | reference | union | mu => cases shape

/-- An actual selected row child has the remaining protected path. -/
theorem OrdinaryAt.child {index : Nat} {path : List Nat}
    {entry : Interned InternedBinderProtocol.NodeKey} {rows : List (EdgeValue Symbol Guard)}
    {depth : Nat} {free : List InternedBinderProtocol.Reference}
    (shape : OrdinaryAt (index :: path) (.node entry rows depth free))
    {row : EdgeValue Symbol Guard} (member : row ∈ rows) {value : Node}
    (found : row.children[index]? = some value) : OrdinaryAt path value :=
  shape row member value found

private theorem empty_at (path : List Nat) : OrdinaryAt path (.empty : Node) := by
  cases path <;> trivial

private def NodeLaw (lib : Library) (record : SourceEqualityClassOrder.Record)
    (originals : List Node) (edits : Edits EqualityNormalize.Path) (input : Node)
    (before : SharedState width) (output : Node) (_after : SharedState width) : Prop :=
  Ready lib before → Values before.checked.native.machine.heap originals → ClosedValues originals →
  (∀ own ∈ record.paths, ForestPath (Origin lib) (own.map Int.ofNat) originals) →
  Populated edits → Available before.checked.native.machine.heap input → input.free = [] →
  NodePaths (Origin lib) edits input →
  ∀ address path, Placed record address edits → Excluded record (address ++ path) →
    OrdinaryAt path input → OrdinaryAt path output

private def ChildrenLaw (lib : Library) (record : SourceEqualityClassOrder.Record)
    (originals : List Node) (entries : List (Int × Edits EqualityNormalize.Path)) (offset : Nat)
    (inputs : List Node) (before : SharedState width) (outputs : List Node) (_after : SharedState width) : Prop :=
  Ready lib before → Values before.checked.native.machine.heap originals → ClosedValues originals →
  (∀ own ∈ record.paths, ForestPath (Origin lib) (own.map Int.ofNat) originals) →
  Populated (.editBelow entries) → Values before.checked.native.machine.heap inputs → ClosedValues inputs →
  ChildrenPaths (Origin lib) entries offset inputs →
  ∀ address index path, Placed record address (.editBelow entries) →
    Excluded record (address ++ [offset + index] ++ path) → ForestOrdinaryAt index path inputs →
    ForestOrdinaryAt index path outputs

private def RowsLaw (lib : Library) (record : SourceEqualityClassOrder.Record)
    (originals : List Node) (entries : List (Int × Edits EqualityNormalize.Path))
    (inputs : List (EdgeValue Symbol Guard)) (before : SharedState width)
    (outputs : List (EdgeValue Symbol Guard)) (_after : SharedState width) : Prop :=
  Ready lib before → Values before.checked.native.machine.heap originals → ClosedValues originals →
  (∀ own ∈ record.paths, ForestPath (Origin lib) (own.map Int.ofNat) originals) →
  Populated (.editBelow entries) → Edges before.checked.native.machine.heap inputs → ClosedEdges inputs →
  (∀ row ∈ inputs, ChildrenPaths (Origin lib) entries 0 row.children) →
  ∀ address index path, Placed record address (.editBelow entries) →
    Excluded record (address ++ [index] ++ path) →
    (∀ row ∈ inputs, ForestOrdinaryAt index path row.children) →
    ∀ row ∈ outputs, ForestOrdinaryAt index path row.children

variable {width : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

omit [DecidableEq Symbol] in
private theorem makeNode_at (index : Nat) (path : List Nat) (rows : List (EdgeValue Symbol Guard))
    (before : InternedConstructorTemplates.State Symbol Guard) (facts : InternedNestedFacts.Facts before)
    (resident : Edges before rows) (shape : ∀ row ∈ rows, ForestOrdinaryAt index path row.children) :
    OrdinaryAt (index :: path) (run (makeNode rows) before).1 := by
  have selected : Edges before (canonicalEdges (surviving rows)) :=
    fun row member => resident row (List.mem_filter.mp (canonicalEdges_member _ row member)).1
  have selectedShape : ∀ row ∈ canonicalEdges (surviving rows), ForestOrdinaryAt index path row.children :=
    fun row member => shape row (List.mem_filter.mp (canonicalEdges_member _ row member)).1
  unfold makeNode
  dsimp only
  split
  · exact empty_at _
  · rename_i first rest same
    obtain ⟨entry, readback⟩ := InternedEdgeResidency.identifyNode_readback (first :: rest) before
      facts.coherent facts.linked (by simpa [InternedNestedProvenance.Edges, same] using selected)
    simp only [run, readback, identifyNode, OrdinaryAt]
    intro row member child found
    exact selectedShape row (by simpa only [same] using member) child found

private theorem preserved (lib : Library) :
    (∀ {record originals edits input before output after},
      EditNode (width := width) record originals edits input before output after →
      NodeLaw lib record originals edits input before output after) ∧
    (∀ {record originals entries offset inputs before outputs after},
      EditChildren (width := width) record originals entries offset inputs before outputs after →
      ChildrenLaw lib record originals entries offset inputs before outputs after) ∧
    (∀ {record originals entries inputs before outputs after},
      EditRows (width := width) record originals entries inputs before outputs after →
      RowsLaw lib record originals entries inputs before outputs after) := by
  have leafCase : ∀ {record originals target input before output after},
      SourceCurrentAllocatedSharedTargetLeaf.Leaf record originals target input before output after →
      NodeLaw (width := width) lib record originals (.editAt target) input before output after := by
    intro record originals target input before output after _ _ _ _ _ _ _ _ _ address path placed excluded _
    obtain ⟨member, suffix, signed, original⟩ := placed [] target (by simp [leaves])
    have emptySuffix : suffix = [] := List.map_eq_nil_iff.mp signed.symm
    subst suffix
    simp only [List.append_nil] at original
    subst target
    exact False.elim (excluded address member ⟨path, rfl⟩)
  have emptyCase : ∀ {record originals entries state},
      NodeLaw (width := width) lib record originals (.editBelow entries) (.empty : Node) state .empty state := by
    intro record originals entries state _ _ _ _ _ _ _ _ _ path _ _ _
    exact empty_at path
  have ordinaryCase : ∀ {record originals entries edges before rebuilt middle value heap entry depth free}
      (actual : EditRows record originals entries edges before rebuilt middle),
      run (makeNode rebuilt) middle.checked.native.machine.heap = (value, heap) →
      RowsLaw (width := width) lib record originals entries edges before rebuilt middle →
      NodeLaw (width := width) lib record originals (.editBelow entries) (.node entry edges depth free)
        before value (advanceHeap middle heap) := by
    intro record originals entries edges before rebuilt middle value heap entry depth free actual built ih
      ready originalAvailable originalClosed originalRoutes populated available closed paths address path placed excluded shape
    cases path with
    | nil =>
        exact SourceSynthesisTypeRouteProgramFields.below_ordinary lib (.ordinary actual built) ready
          originalAvailable originalClosed originalRoutes populated available closed paths shape
    | cons index path =>
        have facts := ready.checked.semantic.ready.semantic.1.normal.facts
        have resident := InternedEdgeResidency.resident_edges _ facts.linked _ available.resident
        have rowClosed := MergedColdReaderClosed.node_children_closed _ facts entry edges depth free available closed
        have returned := SourceSynthesisNativeTypeSharedEdit.rows lib actual ready originalAvailable originalClosed
          originalRoutes populated resident rowClosed (fun row member => node_to_children paths row member)
        have protectedRows := ih ready originalAvailable originalClosed originalRoutes populated resident rowClosed
          (fun row member => node_to_children paths row member) address index path placed
          (by simpa only [List.append_assoc, List.singleton_append] using excluded) shape
        have retained := makeNode_at index path rebuilt middle.checked.native.machine.heap
          returned.1.checked.semantic.ready.semantic.1.normal.facts returned.2.2.1 protectedRows
        simpa only [built] using retained
  have recursiveCase : ∀ {record originals entries input} {before : SharedState width} {exposed heap output after},
      SourceEqualityRequiredGraph.Recursive input →
      SourceEqualityRequiredHead.Head input before.checked.native.machine.heap exposed heap →
      EditNode record originals (.editBelow entries) exposed (advanceHeap before heap) output after →
      NodeLaw (width := width) lib record originals (.editBelow entries) exposed (advanceHeap before heap) output after →
      NodeLaw (width := width) lib record originals (.editBelow entries) input before output after := by
    intro record originals entries input before exposed heap output after recursive _ _ _
      _ _ _ _ _ _ _ _ _ _ _ _ shape
    have ordinary := shape.ordinary
    cases input <;> cases recursive <;> cases ordinary
  have nilChildren : ∀ {record originals entries offset state},
      ChildrenLaw (width := width) lib record originals entries offset ([] : List Node) state [] state := by
    intro record originals entries offset state _ _ _ _ _ _ _ _ _ _ _ _ _ _ value found
    cases found
  have unselectedCase : ∀ {record originals entries inputs before outputs after input} (offset : Nat),
      SourceEqualityNeededMap.lookup (offset : Int) entries = none →
      EditChildren record originals entries (offset + 1) inputs before outputs after →
      ChildrenLaw (width := width) lib record originals entries (offset + 1) inputs before outputs after →
      ChildrenLaw (width := width) lib record originals entries offset (input :: inputs) before (input :: outputs) after := by
    intro record originals entries inputs before outputs after input offset _ _ ih
      ready originalAvailable originalClosed originalRoutes populated available closed paths address index path placed excluded shape
    cases index with
    | zero => intro value found; cases found; exact shape input rfl
    | succ index =>
        exact ih ready originalAvailable originalClosed originalRoutes populated
          (fun value member => available value (List.mem_cons_of_mem _ member))
          (fun value member => closed value (List.mem_cons_of_mem _ member)) (children_tail paths)
          address index path placed
          (by simpa only [Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using excluded) shape
  have selectedCase : ∀ {record originals entries edits input before result middle inputs outputs after} (offset : Nat),
      SourceEqualityNeededMap.lookup (offset : Int) entries = some edits →
      (first : EditNode record originals edits input before result middle) →
      EditChildren record originals entries (offset + 1) inputs middle outputs after →
      NodeLaw (width := width) lib record originals edits input before result middle →
      ChildrenLaw (width := width) lib record originals entries (offset + 1) inputs middle outputs after →
      ChildrenLaw (width := width) lib record originals entries offset (input :: inputs) before (result :: outputs) after := by
    intro record originals entries edits input before result middle inputs outputs after offset found first _ firstIH restIH
      ready originalAvailable originalClosed originalRoutes populated available closed paths address index path placed excluded shape
    have populatedChild := selected_populated populated found
    obtain ⟨current, extension, _returned, _resultClosed, _retained⟩ :=
      SourceSynthesisNativeTypeSharedEdit.node lib first ready originalAvailable originalClosed originalRoutes
        populatedChild.1 populatedChild.2 (available input List.mem_cons_self) (closed input List.mem_cons_self)
        (children_selected paths found)
    cases index with
    | zero =>
        intro value stored
        cases stored
        exact firstIH ready originalAvailable originalClosed originalRoutes populatedChild.1
          (available input List.mem_cons_self) (closed input List.mem_cons_self) (children_selected paths found)
          (address ++ [offset]) path (child_placed offset placed found)
          (by simpa only [Nat.add_zero] using excluded) (shape input rfl)
    | succ index =>
        exact restIH current
          (fun original member => extension.available original (originalAvailable original member))
          originalClosed originalRoutes populated
          (fun value member => extension.available value (available value (List.mem_cons_of_mem _ member)))
          (fun value member => closed value (List.mem_cons_of_mem _ member)) (children_tail paths)
          address index path placed
          (by simpa only [Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using excluded) shape
  have nilRows : ∀ {record originals entries state},
      RowsLaw (width := width) lib record originals entries ([] : List (EdgeValue Symbol Guard)) state [] state := by
    intro record originals entries state _ _ _ _ _ _ _ _ _ _ _ _ _ _ row member
    cases member
  have consRows : ∀ {record originals entries before values middle result heap edges results after edge},
      (children : EditChildren record originals entries 0 edge.children before values middle) →
      run (makeEdge edge.entry.key.symbol edge.entry.key.constraint values) middle.checked.native.machine.heap = (result, heap) →
      EditRows record originals entries edges (advanceHeap middle heap) results after →
      ChildrenLaw (width := width) lib record originals entries 0 edge.children before values middle →
      RowsLaw (width := width) lib record originals entries edges (advanceHeap middle heap) results after →
      RowsLaw (width := width) lib record originals entries (edge :: edges) before (result :: results) after := by
    intro record originals entries before values middle result heap edges results after edge children built _ firstIH restIH
      ready originalAvailable originalClosed originalRoutes populated resident closed paths address index path placed excluded shape
    have facts := ready.checked.semantic.ready.semantic.1.normal.facts
    obtain ⟨current, extension, valuesAvailable, _valuesClosed, _retained⟩ :=
      SourceSynthesisNativeTypeSharedEdit.children lib children ready originalAvailable originalClosed originalRoutes
        populated (facts.cached.edges _ _ (resident edge List.mem_cons_self))
        (closed edge List.mem_cons_self) (paths edge List.mem_cons_self)
    have ownShape := firstIH ready originalAvailable originalClosed originalRoutes populated
      (facts.cached.edges _ _ (resident edge List.mem_cons_self)) (closed edge List.mem_cons_self)
      (paths edge List.mem_cons_self) address index path placed
      (by simpa only [Nat.zero_add] using excluded) (shape edge List.mem_cons_self)
    have oldRow := InternedEdgeResidency.edge_grows _ _ extension.heap edge (resident edge List.mem_cons_self)
    obtain ⟨constructed, edgeExtension, _resident, exactChildren, _guard⟩ :=
      SourceSynthesisNativeTypeSharedHeap.edge lib edge values built current oldRow valuesAvailable
    have preceding := extension.trans edgeExtension
    have tailShape := restIH constructed
      (fun original member => preceding.available original (originalAvailable original member)) originalClosed originalRoutes
      populated (fun row member => InternedEdgeResidency.edge_grows _ _ preceding.heap row
        (resident row (List.mem_cons_of_mem _ member)))
      (fun row member => closed row (List.mem_cons_of_mem _ member))
      (fun row member => paths row (List.mem_cons_of_mem _ member)) address index path placed excluded
      (fun row member => shape row (List.mem_cons_of_mem _ member))
    intro row member
    rcases List.mem_cons.mp member with rfl | member
    · simpa only [exactChildren] using ownShape
    · exact tailShape row member
  refine ⟨?_, ?_, ?_⟩
  · intro record originals edits input before output after actual
    exact EditNode.rec
      (motive_1 := fun edits input before output after _ => NodeLaw lib record originals edits input before output after)
      (motive_2 := fun entries offset inputs before outputs after _ => ChildrenLaw lib record originals entries offset inputs before outputs after)
      (motive_3 := fun entries inputs before outputs after _ => RowsLaw lib record originals entries inputs before outputs after)
      (fun {_ _ _ _ _} actual => leafCase actual)
      (fun {_ _} => emptyCase)
      (fun {_ _ _ _ _ _ _ _ _ _} actual built ih => ordinaryCase actual built ih)
      (fun {_ _ _ _ _ _ _} recursive head body ih => recursiveCase recursive head body ih)
      (fun {_ _ _} => nilChildren)
      (fun {_ _ _ _ _ _} offset absent rest ih => unselectedCase offset absent rest ih)
      (fun {_ _ _ _ _ _ _ _ _} offset found first rest firstIH restIH => selectedCase offset found first rest firstIH restIH)
      (fun {_ _} => nilRows)
      (fun {_ _ _ _ _ _ _ _ _ _} children built rest firstIH restIH => consRows children built rest firstIH restIH) actual
  · intro record originals entries offset inputs before outputs after actual
    exact EditChildren.rec
      (motive_1 := fun edits input before output after _ => NodeLaw lib record originals edits input before output after)
      (motive_2 := fun entries offset inputs before outputs after _ => ChildrenLaw lib record originals entries offset inputs before outputs after)
      (motive_3 := fun entries inputs before outputs after _ => RowsLaw lib record originals entries inputs before outputs after)
      (fun {_ _ _ _ _} actual => leafCase actual)
      (fun {_ _} => emptyCase)
      (fun {_ _ _ _ _ _ _ _ _ _} actual built ih => ordinaryCase actual built ih)
      (fun {_ _ _ _ _ _ _} recursive head body ih => recursiveCase recursive head body ih)
      (fun {_ _ _} => nilChildren)
      (fun {_ _ _ _ _ _} offset absent rest ih => unselectedCase offset absent rest ih)
      (fun {_ _ _ _ _ _ _ _ _} offset found first rest firstIH restIH => selectedCase offset found first rest firstIH restIH)
      (fun {_ _} => nilRows)
      (fun {_ _ _ _ _ _ _ _ _ _} children built rest firstIH restIH => consRows children built rest firstIH restIH) actual
  · intro record originals entries inputs before outputs after actual
    exact EditRows.rec
      (motive_1 := fun edits input before output after _ => NodeLaw lib record originals edits input before output after)
      (motive_2 := fun entries offset inputs before outputs after _ => ChildrenLaw lib record originals entries offset inputs before outputs after)
      (motive_3 := fun entries inputs before outputs after _ => RowsLaw lib record originals entries inputs before outputs after)
      (fun {_ _ _ _ _} actual => leafCase actual)
      (fun {_ _} => emptyCase)
      (fun {_ _ _ _ _ _ _ _ _ _} actual built ih => ordinaryCase actual built ih)
      (fun {_ _ _ _ _ _ _} recursive head body ih => recursiveCase recursive head body ih)
      (fun {_ _ _} => nilChildren)
      (fun {_ _ _ _ _ _} offset absent rest ih => unselectedCase offset absent rest ih)
      (fun {_ _ _ _ _ _ _ _ _} offset found first rest firstIH restIH => selectedCase offset found first rest firstIH restIH)
      (fun {_ _} => nilRows)
      (fun {_ _ _ _ _ _ _ _ _ _} children built rest firstIH restIH => consRows children built rest firstIH restIH) actual

/-- An actual placed node edit preserves an ordinary path excluded from its endpoints. -/
theorem edit_node (lib : Library) {record originals edits input before output after}
    (actual : EditNode (width := width) record originals edits input before output after)
    (ready : Ready lib before) (originalAvailable : Values before.checked.native.machine.heap originals)
    (originalClosed : ClosedValues originals)
    (originalRoutes : ∀ own ∈ record.paths, ForestPath (Origin lib) (own.map Int.ofNat) originals)
    (populated : Populated edits) (available : Available before.checked.native.machine.heap input)
    (closed : input.free = []) (paths : NodePaths (Origin lib) edits input)
    (address path : EqualityNormalize.Path) (placed : Placed record address edits)
    (excluded : Excluded record (address ++ path)) (shape : OrdinaryAt path input) : OrdinaryAt path output :=
  (preserved lib).1 actual ready originalAvailable originalClosed originalRoutes populated available closed paths
    address path placed excluded shape

/-- The literal ordered child edit retains the selected physical forest position. -/
theorem edit_children (lib : Library) {record originals entries offset inputs before outputs after}
    (actual : EditChildren (width := width) record originals entries offset inputs before outputs after)
    (ready : Ready lib before) (originalAvailable : Values before.checked.native.machine.heap originals)
    (originalClosed : ClosedValues originals)
    (originalRoutes : ∀ own ∈ record.paths, ForestPath (Origin lib) (own.map Int.ofNat) originals)
    (populated : Populated (.editBelow entries)) (available : Values before.checked.native.machine.heap inputs)
    (closed : ClosedValues inputs) (paths : ChildrenPaths (Origin lib) entries offset inputs)
    (address : EqualityNormalize.Path) (index : Nat) (path : EqualityNormalize.Path)
    (placed : Placed record address (.editBelow entries))
    (excluded : Excluded record (address ++ [offset + index] ++ path))
    (shape : ForestOrdinaryAt index path inputs) : ForestOrdinaryAt index path outputs :=
  (preserved lib).2.1 actual ready originalAvailable originalClosed originalRoutes populated available closed paths
    address index path placed excluded shape

/-- Every actual reconstructed row retains its selected child path. -/
theorem edit_rows (lib : Library) {record originals entries inputs before outputs after}
    (actual : EditRows (width := width) record originals entries inputs before outputs after)
    (ready : Ready lib before) (originalAvailable : Values before.checked.native.machine.heap originals)
    (originalClosed : ClosedValues originals)
    (originalRoutes : ∀ own ∈ record.paths, ForestPath (Origin lib) (own.map Int.ofNat) originals)
    (populated : Populated (.editBelow entries)) (resident : Edges before.checked.native.machine.heap inputs)
    (closed : ClosedEdges inputs) (paths : ∀ row ∈ inputs, ChildrenPaths (Origin lib) entries 0 row.children)
    (address : EqualityNormalize.Path) (index : Nat) (path : EqualityNormalize.Path)
    (placed : Placed record address (.editBelow entries)) (excluded : Excluded record (address ++ [index] ++ path))
    (shape : ∀ row ∈ inputs, ForestOrdinaryAt index path row.children) :
    ∀ row ∈ outputs, ForestOrdinaryAt index path row.children :=
  (preserved lib).2.2 actual ready originalAvailable originalClosed originalRoutes populated resident closed paths
    address index path placed excluded shape

/-- A coherent class preserves the required function annotation through its actual edit list. -/
theorem class_edit (lib : Library) {record values results} {before after : Checked width} {memo saved : Memo}
    (actual : Class record values before memo results after saved)
    (ready : Ready lib (initial before memo)) (available : Values before.native.machine.heap values)
    (closed : ClosedValues values) (coherent : SourceEqualityClassOrder.Coherent record)
    (routes : ∀ path ∈ record.paths, ForestPath (Origin lib) (path.map Int.ofNat) values)
    (excluded : Excluded record [2, 0]) (shape : AtFunction values) : AtFunction results := by
  cases actual with
  | edit lower =>
      have placed := compiled_placed record coherent
      have populated := SourceCurrentAllocatedClassEditPlan.compiled_populated record
      have paths := compiled_forest_paths (Origin lib) record coherent values routes
      generalize compiled : SourceCurrentAllocatedClassEditPlan.compiled record = edits at lower
      rw [compiled] at placed populated paths
      cases lower with
      | leaf => exact shape
      | children trace =>
          exact edit_children lib trace ready available closed routes populated available closed
            (forest_to_children paths) [] 2 [0] placed excluded shape

/-- A head class receives the same tail return and the derived ordinary annotation path. -/
theorem fold (lib : Library) {records values results} {before after : Checked width} {memo saved : Memo}
    (actual : Fold records values before memo results after saved)
    (ready : Ready lib (initial before memo)) (available : Values before.native.machine.heap values)
    (closed : ClosedValues values) (coherent : ∀ record ∈ records, SourceEqualityClassOrder.Coherent record)
    (routes : ∀ record ∈ records, ∀ path ∈ record.paths, ForestPath (Origin lib) (path.map Int.ofNat) values)
    (excluded : ∀ record ∈ records, Excluded record [2, 0]) (shape : AtFunction values) : AtFunction results := by
  revert ready available closed coherent routes excluded shape
  induction actual with
  | nil => intro _ _ _ _ _ _ shape; exact shape
  | cons tail head ih =>
      intro ready available closed coherent routes excluded shape
      have tailShape := ih ready available closed
        (fun record member => coherent record (List.mem_cons_of_mem _ member))
        (fun record member => routes record (List.mem_cons_of_mem _ member))
        (fun record member => excluded record (List.mem_cons_of_mem _ member)) shape
      obtain ⟨middleReady, _extension, middleAvailable, middleClosed, tailRoutes⟩ :=
        SourceSynthesisNativeTypeClassPass.fold lib tail ready available closed
          (fun record member => coherent record (List.mem_cons_of_mem _ member))
          (fun record member => routes record (List.mem_cons_of_mem _ member))
      exact class_edit lib head middleReady middleAvailable middleClosed (coherent _ List.mem_cons_self)
        (fun path member => tailRoutes (path.map Int.ofNat) (routes _ List.mem_cons_self path member))
        (excluded _ List.mem_cons_self) tailShape

/-- Final empty propagation preserves the required path at the same forest position. -/
theorem pass (lib : Library) {records values results} {before after : Checked width} {memo saved : Memo}
    (actual : Pass records values before memo results after saved)
    (ready : Ready lib (initial before memo)) (available : Values before.native.machine.heap values)
    (closed : ClosedValues values) (coherent : ∀ record ∈ records, SourceEqualityClassOrder.Coherent record)
    (routes : ∀ record ∈ records, ∀ path ∈ record.paths, ForestPath (Origin lib) (path.map Int.ofNat) values)
    (excluded : ∀ record ∈ records, Excluded record [2, 0]) (shape : AtFunction values) : AtFunction results := by
  cases actual with
  | done actual =>
      have retained := fold lib actual ready available closed coherent routes excluded shape
      unfold EqualityLeafProjectionRuntimeEmpty.propagate
      split
      · intro value found
        have member := List.mem_of_getElem? found
        obtain ⟨original, _included, same⟩ := List.mem_map.mp member
        cases same
        exact empty_at _
      · exact retained

section Selected
open SourceSynthesisFirstOrderConstruction (Expression application)
variable [DecidableEq Node]
variable {formulas : SourceGuards.Formulas FullSyntax.Formula}
variable {solver : SourceGuards.Entailment FullSyntax.Formula}
variable {inventory : SourceCurrentAllocatedNativeInventoryState.Inventory}
variable {guard : Guard} {loaded : SourceEqualityConjoinAllocation.Constraint FullSyntax.Formula}
variable {inherited own : SourceEqualityConstraintAllocation.Value}
variable {start scanned : SourceEqualityNativeDemand.State width}
variable {records kept : List SourceEqualityClassOrder.Record} {budget : Nat} {values : List Node}
variable {fourth savedFourth : SourceCurrentEmptinessMemo.Memo}
variable {outcome : Option EqualityNormalize.Class} {memos final : EndpointMemoGateTrace.Memos}

/-- The same source occurrence, precheck, and selected Scan derive every class endpoint exclusion. -/
theorem application_pass (lib : Library) (types function argument : Expression)
    (sourceName : String) (sourceChildren : List Expression)
    (occurrence : application types function argument = .node [.mk sourceName guard sourceChildren])
    (receipt : SourceCurrentAllocatedPrecheck.Receipt formulas solver inventory guard loaded
      inherited start own (.classes records))
    (scan : SourceCurrentSharedScanCallerNumeric.ScanReads budget values records
      (SourceCurrentAllocatedPrecheck.state start loaded inherited) fourth outcome kept scanned savedFourth memos final)
    {inputs results : List Node} {before after : Checked width} {memo saved : Memo}
    (actual : Pass kept inputs before memo results after saved)
    (ready : Ready lib (initial before memo)) (available : Values before.native.machine.heap inputs)
    (closed : ClosedValues inputs)
    (routes : ∀ record ∈ kept, ∀ path ∈ record.paths, ForestPath (Origin lib) (path.map Int.ofNat) inputs)
    (shape : AtFunction inputs) : AtFunction results := by
  have excluded := SourceSynthesisRequiredAnnotationEditRetention.selected_application_avoids_function_annotation
    types function argument sourceName sourceChildren occurrence receipt scan
  exact pass lib actual ready available closed (fun record member => (excluded record member).1)
    routes (fun record member => (excluded record member).2) shape

end Selected
end MicroCFTA.SourceSynthesisRequiredAnnotationClassPass
