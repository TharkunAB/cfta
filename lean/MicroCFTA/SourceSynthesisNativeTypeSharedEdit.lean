import MicroCFTA.SourceSynthesisNativeTypeSharedLeaf
import MicroCFTA.SourceSynthesisNativeTypeSharedHeap
import MicroCFTA.SourceCurrentAllocatedSharedEditGraph
import MicroCFTA.SourceCurrentHereditaryTypeEditPlan
import MicroCFTA.SourceCurrentHereditaryTypeRouteConstructors

/-!
# Type routes through actual shared edits

Every retained edit leaf has an input structural Type route. At a leaf,
the empty relative route proves the input annotation. Ordered child and row
calls retain all routes for later classes. Constructor work retains the
original guards. Program guards need no Type annotation.

These laws concern completed current edit graphs and genuine initial
readiness and route certificates. They do not establish traversal completion,
all reached source roles, finite-word bounds, or native lazy demand order.
-/
namespace MicroCFTA.SourceSynthesisNativeTypeSharedEdit
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values Edges)
open InternedEdgeResidency (EdgeResident)
open MergedColdReaderClosedInputs (ClosedValues ClosedEdges)
open SourceSynthesisTypeSyntax (Library)
open SourceSynthesisGeneralizeSyntax (Guard)
open SourceSynthesisNativeTypeTrace (Origin)
open SourceEqualityAnnotationLanguage (Annotated)
open SourceEqualityProjectionGraph (select)
open SourceEqualityEdits (Edits)
open SourceCurrentHereditaryTypePaths (TypePath ForestPath)
open SourceCurrentHereditaryTypeEditPlan
open SourceCurrentHereditaryTypeRouteConstructors (ForestRoutes RowRoutes route_nil)
open SourceCurrentEditDomains (Populated HasLeaf)
open SourceCurrentAllocatedSharedEditGraph
open SourceRecursiveIntersectionKernel (Extension)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Ready" => SourceSynthesisNativeTypeSharedState.Ready
variable {width : Nat}

private def NodeRoutes (valid : Guard → Prop) (input output : Value Symbol Guard) : Prop :=
  ∀ path, TypePath valid path input → TypePath valid path output

private theorem aligned_get {valid : Guard → Prop} {inputs outputs : List (Value Symbol Guard)}
    (aligned : All₂ (NodeRoutes valid) inputs outputs) (index : Nat) (path : List Int)
    (routes : ∀ value, inputs[index]? = some value → TypePath valid path value) :
    ∀ value, outputs[index]? = some value → TypePath valid path value := by
  induction aligned generalizing index with
  | nil => intro value found; cases found
  | cons first rest ih =>
      cases index with
      | zero => intro value found; cases found; exact first path (routes _ rfl)
      | succ index => exact ih index routes

private theorem aligned_forest {valid : Guard → Prop} {inputs outputs : List (Value Symbol Guard)}
    (aligned : All₂ (NodeRoutes valid) inputs outputs) : ForestRoutes valid inputs outputs := by
  intro path routes
  cases path with
  | nil =>
      induction aligned with
      | nil => intro value member; cases member
      | cons first rest ih =>
          intro value member
          rcases List.mem_cons.mp member with rfl | member
          · exact route_nil (first [] (.annotated [] _ (routes _ List.mem_cons_self)))
          · exact ih (fun original included => routes original (List.mem_cons_of_mem _ included)) value member
  | cons index path =>
      by_cases negative : index < 0
      · intro value selected
        simp only [select, negative, ite_true] at selected
        cases selected
      · intro value selected
        have found : outputs[index.toNat]? = some value := by
          simpa only [select, negative, ite_false] using selected
        exact aligned_get aligned index.toNat path
          (fun original found => routes original (by simpa only [select, negative, ite_false] using found)) value found

private def NodeLaw (lib : Library) (record : SourceEqualityClassOrder.Record)
    (originals : List (Value Symbol Guard)) (edits : Edits EqualityNormalize.Path)
    (input : Value Symbol Guard) (before : SharedState width) (output : Value Symbol Guard)
    (after : SharedState width) : Prop :=
  Ready lib before → Values before.checked.native.machine.heap originals → ClosedValues originals →
  (∀ own ∈ record.paths, ForestPath (Origin lib) (own.map Int.ofNat) originals) →
  Populated edits → HasLeaf edits → Available before.checked.native.machine.heap input → input.free = [] →
  NodePaths (Origin lib) edits input →
  Ready lib after ∧ Extension before.checked.native.machine after.checked.native.machine ∧
    Available after.checked.native.machine.heap output ∧ output.free = [] ∧ NodeRoutes (Origin lib) input output

private def ChildrenLaw (lib : Library) (record : SourceEqualityClassOrder.Record)
    (originals : List (Value Symbol Guard)) (entries : List (Int × Edits EqualityNormalize.Path))
    (offset : Nat) (inputs : List (Value Symbol Guard)) (before : SharedState width)
    (outputs : List (Value Symbol Guard)) (after : SharedState width) : Prop :=
  Ready lib before → Values before.checked.native.machine.heap originals → ClosedValues originals →
  (∀ own ∈ record.paths, ForestPath (Origin lib) (own.map Int.ofNat) originals) →
  Populated (.editBelow entries) → Values before.checked.native.machine.heap inputs → ClosedValues inputs →
  ChildrenPaths (Origin lib) entries offset inputs →
  Ready lib after ∧ Extension before.checked.native.machine after.checked.native.machine ∧
    Values after.checked.native.machine.heap outputs ∧ ClosedValues outputs ∧
      All₂ (NodeRoutes (Origin lib)) inputs outputs

private def RowsLaw (lib : Library) (record : SourceEqualityClassOrder.Record)
    (originals : List (Value Symbol Guard)) (entries : List (Int × Edits EqualityNormalize.Path))
    (inputs : List (EdgeValue Symbol Guard)) (before : SharedState width)
    (outputs : List (EdgeValue Symbol Guard)) (after : SharedState width) : Prop :=
  Ready lib before → Values before.checked.native.machine.heap originals → ClosedValues originals →
  (∀ own ∈ record.paths, ForestPath (Origin lib) (own.map Int.ofNat) originals) →
  Populated (.editBelow entries) → Edges before.checked.native.machine.heap inputs → ClosedEdges inputs →
  (∀ edge ∈ inputs, ChildrenPaths (Origin lib) entries 0 edge.children) →
  Ready lib after ∧ Extension before.checked.native.machine after.checked.native.machine ∧
    Edges after.checked.native.machine.heap outputs ∧ ClosedEdges outputs ∧ RowRoutes (Origin lib) inputs outputs

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

private theorem preserved (lib : Library) :
    (∀ {record originals edits input before output after},
      EditNode (width := width) record originals edits input before output after →
      NodeLaw (width := width) lib record originals edits input before output after) ∧
    (∀ {record originals entries offset inputs before outputs after},
      EditChildren (width := width) record originals entries offset inputs before outputs after →
      ChildrenLaw (width := width) lib record originals entries offset inputs before outputs after) ∧
    (∀ {record originals entries inputs before outputs after},
      EditRows (width := width) record originals entries inputs before outputs after →
      RowsLaw (width := width) lib record originals entries inputs before outputs after) := by
  have leafCase : ∀ {record originals target input before output after},
      SourceCurrentAllocatedSharedTargetLeaf.Leaf record originals target input before output after →
      NodeLaw (width := width) lib record originals (.editAt target) input before output after := by
    intro record originals target input before output after actual ready originalAvailable originalClosed originalRoutes
      _ _ available closed paths
    obtain ⟨next, extension, returned, resultClosed, annotated⟩ :=
      SourceSynthesisNativeTypeSharedLeaf.leaf lib actual ready originalAvailable originalClosed originalRoutes
        available closed (leaf_annotated paths)
    exact ⟨next, extension, returned, resultClosed, fun path _ => .annotated path output annotated⟩
  have emptyCase : ∀ {record originals entries state},
      NodeLaw (width := width) lib record originals (.editBelow entries) (.empty : Value Symbol Guard) state .empty state := by
    intro record originals entries state ready _ _ _ _ _ available closed _
    exact ⟨ready, .refl _, available, closed, fun _ route => route⟩
  have ordinaryCase : ∀ {record originals entries edges before rebuilt middle value heap entry depth free}
      (actual : EditRows record originals entries edges before rebuilt middle),
      run (makeNode rebuilt) middle.checked.native.machine.heap = (value, heap) →
      RowsLaw (width := width) lib record originals entries edges before rebuilt middle →
      NodeLaw (width := width) lib record originals (.editBelow entries) (.node entry edges depth free) before value (advanceHeap middle heap) := by
    intro record originals entries edges before rebuilt middle value heap entry depth free _ built ih
      ready originalAvailable originalClosed originalRoutes populated _ available closed paths
    have facts := ready.checked.semantic.ready.semantic.1.normal.facts
    have resident := InternedEdgeResidency.resident_edges _ facts.linked _ available.resident
    have edgeClosed := MergedColdReaderClosed.node_children_closed _ facts entry edges depth free available closed
    obtain ⟨current, first, resultRows, rowsClosed, routes⟩ := ih ready originalAvailable originalClosed originalRoutes
      populated resident edgeClosed (fun row member => node_to_children paths row member)
    obtain ⟨next, last, returned, resultClosed⟩ :=
      SourceSynthesisNativeTypeSharedHeap.node lib built current resultRows rowsClosed
    refine ⟨next, first.trans last, returned, resultClosed, ?_⟩
    have retained := SourceCurrentHereditaryTypeRouteConstructors.makeNode_routes (Origin lib)
      entry edges depth free rebuilt middle.checked.native.machine.heap
      current.checked.semantic.ready.semantic.1.normal.facts resultRows routes
    simpa only [NodeRoutes, built] using retained
  have recursiveCase : ∀ {record originals entries input} {before : SharedState width} {exposed heap output after}
      (recursive : SourceEqualityRequiredGraph.Recursive input)
      (head : SourceEqualityRequiredHead.Head input before.checked.native.machine.heap exposed heap)
      (body : EditNode record originals (.editBelow entries) exposed (advanceHeap before heap) output after),
      NodeLaw (width := width) lib record originals (.editBelow entries) exposed (advanceHeap before heap) output after →
      NodeLaw (width := width) lib record originals (.editBelow entries) input before output after := by
    intro record originals entries input before exposed heap output after recursive head _ ih
      ready originalAvailable originalClosed originalRoutes populated nonempty available closed paths
    have annotated := recursive_annotated recursive nonempty paths
    obtain ⟨current, first, exposedAvailable, exposedClosed, exposedTyped⟩ :=
      SourceSynthesisNativeTypeSharedHeap.head lib head ready available closed annotated
    obtain ⟨next, last, returned, resultClosed, retained⟩ := ih current
      (fun original member => first.available original (originalAvailable original member)) originalClosed originalRoutes
      populated nonempty exposedAvailable exposedClosed (fun path _ _ => .annotated path exposed exposedTyped)
    have resultTyped := route_nil (retained [] (.annotated [] exposed exposedTyped))
    exact ⟨next, first.trans last, returned, resultClosed, fun path _ => .annotated path output resultTyped⟩
  have nilChildren : ∀ {record originals entries offset state},
      ChildrenLaw (width := width) lib record originals entries offset ([] : List (Value Symbol Guard)) state [] state := by
    intro record originals entries offset state ready _ _ _ _ _ _ _
    refine ⟨ready, .refl _, ?_, ?_, .nil⟩
    · intro value member; cases member
    · intro value member; cases member
  have unselectedCase : ∀ {record originals entries inputs before outputs after input} (offset : Nat),
      SourceEqualityNeededMap.lookup (offset : Int) entries = none →
      (actual : EditChildren record originals entries (offset + 1) inputs before outputs after) →
      ChildrenLaw (width := width) lib record originals entries (offset + 1) inputs before outputs after →
      ChildrenLaw (width := width) lib record originals entries offset (input :: inputs) before (input :: outputs) after := by
    intro record originals entries inputs before outputs after input offset _ _ ih
      ready originalAvailable originalClosed originalRoutes populated available closed paths
    obtain ⟨next, extension, returned, resultClosed, retained⟩ := ih ready originalAvailable originalClosed originalRoutes
      populated (fun value member => available value (List.mem_cons_of_mem _ member))
      (fun value member => closed value (List.mem_cons_of_mem _ member)) (children_tail paths)
    refine ⟨next, extension, ?_, ?_, .cons (fun _ route => route) retained⟩
    · intro value member
      rcases List.mem_cons.mp member with rfl | member
      · exact extension.available value (available value List.mem_cons_self)
      · exact returned value member
    · intro value member
      rcases List.mem_cons.mp member with rfl | member
      · exact closed value List.mem_cons_self
      · exact resultClosed value member
  have selectedCase : ∀ {record originals entries edits input before result middle inputs outputs after} (offset : Nat),
      SourceEqualityNeededMap.lookup (offset : Int) entries = some edits →
      (first : EditNode record originals edits input before result middle) →
      (rest : EditChildren record originals entries (offset + 1) inputs middle outputs after) →
      NodeLaw (width := width) lib record originals edits input before result middle →
      ChildrenLaw (width := width) lib record originals entries (offset + 1) inputs middle outputs after →
      ChildrenLaw (width := width) lib record originals entries offset (input :: inputs) before (result :: outputs) after := by
    intro record originals entries edits input before result middle inputs outputs after offset found _ _ firstIH restIH
      ready originalAvailable originalClosed originalRoutes populated available closed paths
    have populatedChild := selected_populated populated found
    obtain ⟨current, first, resultAvailable, ownClosed, ownRoutes⟩ := firstIH ready originalAvailable originalClosed originalRoutes
      populatedChild.1 populatedChild.2 (available input List.mem_cons_self) (closed input List.mem_cons_self)
      (children_selected paths found)
    obtain ⟨next, last, returned, resultClosed, retained⟩ := restIH current
      (fun original member => first.available original (originalAvailable original member)) originalClosed originalRoutes
      populated (fun value member => first.available value (available value (List.mem_cons_of_mem _ member)))
      (fun value member => closed value (List.mem_cons_of_mem _ member)) (children_tail paths)
    refine ⟨next, first.trans last, ?_, ?_, .cons ownRoutes retained⟩
    · intro value member
      rcases List.mem_cons.mp member with rfl | member
      · exact last.available value resultAvailable
      · exact returned value member
    · intro value member
      rcases List.mem_cons.mp member with rfl | member
      · exact ownClosed
      · exact resultClosed value member
  have nilRows : ∀ {record originals entries state},
      RowsLaw (width := width) lib record originals entries ([] : List (EdgeValue Symbol Guard)) state [] state := by
    intro record originals entries state ready _ _ _ _ _ _ _
    refine ⟨ready, .refl _, ?_, ?_, ?_⟩
    · intro edge member; cases member
    · intro edge member; cases member
    · intro edge member; cases member
  have consRows : ∀ {record originals entries before values middle result heap edges results after edge},
      (children : EditChildren record originals entries 0 edge.children before values middle) →
      run (makeEdge edge.entry.key.symbol edge.entry.key.constraint values) middle.checked.native.machine.heap = (result, heap) →
      (rest : EditRows record originals entries edges (advanceHeap middle heap) results after) →
      ChildrenLaw (width := width) lib record originals entries 0 edge.children before values middle →
      RowsLaw (width := width) lib record originals entries edges (advanceHeap middle heap) results after →
      RowsLaw (width := width) lib record originals entries (edge :: edges) before (result :: results) after := by
    intro record originals entries before values middle result heap edges results after edge _ built _ firstIH restIH
      ready originalAvailable originalClosed originalRoutes populated resident closed paths
    have facts := ready.checked.semantic.ready.semantic.1.normal.facts
    obtain ⟨current, first, valuesAvailable, valuesClosed, aligned⟩ := firstIH ready originalAvailable originalClosed originalRoutes
      populated (facts.cached.edges _ _ (resident edge List.mem_cons_self))
      (closed edge List.mem_cons_self) (paths edge List.mem_cons_self)
    have oldRow := InternedEdgeResidency.edge_grows _ _ first.heap edge (resident edge List.mem_cons_self)
    obtain ⟨constructed, edgeExtension, resultResident, exactChildren, exactGuard⟩ :=
      SourceSynthesisNativeTypeSharedHeap.edge lib edge values built current oldRow valuesAvailable
    have preceding := first.trans edgeExtension
    obtain ⟨next, last, resultRows, rowsClosed, rowRoutes⟩ := restIH constructed
      (fun original member => preceding.available original (originalAvailable original member)) originalClosed originalRoutes
      populated (fun row member => InternedEdgeResidency.edge_grows _ _ preceding.heap row
        (resident row (List.mem_cons_of_mem _ member)))
      (fun row member => closed row (List.mem_cons_of_mem _ member))
      (fun row member => paths row (List.mem_cons_of_mem _ member))
    refine ⟨next, preceding.trans last, ?_, ?_, ?_⟩
    · intro row member
      rcases List.mem_cons.mp member with rfl | member
      · exact InternedEdgeResidency.edge_grows _ _ last.heap row resultResident
      · exact resultRows row member
    · intro row member
      rcases List.mem_cons.mp member with rfl | member
      · simpa only [exactChildren] using valuesClosed
      · exact rowsClosed row member
    · intro row member
      rcases List.mem_cons.mp member with rfl | member
      · refine ⟨edge, List.mem_cons_self, exactGuard, ?_⟩
        simpa only [exactChildren] using aligned_forest aligned
      · obtain ⟨original, included, guard, retained⟩ := rowRoutes row member
        exact ⟨original, List.mem_cons_of_mem _ included, guard, retained⟩
  refine ⟨?_, ?_, ?_⟩
  · intro record originals edits input before output after actual
    exact EditNode.rec
      (motive_1 := fun edits input before output after _ => NodeLaw (width := width) lib record originals edits input before output after)
      (motive_2 := fun entries offset inputs before outputs after _ => ChildrenLaw (width := width) lib record originals entries offset inputs before outputs after)
      (motive_3 := fun entries inputs before outputs after _ => RowsLaw (width := width) lib record originals entries inputs before outputs after)
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
      (motive_1 := fun edits input before output after _ => NodeLaw (width := width) lib record originals edits input before output after)
      (motive_2 := fun entries offset inputs before outputs after _ => ChildrenLaw (width := width) lib record originals entries offset inputs before outputs after)
      (motive_3 := fun entries inputs before outputs after _ => RowsLaw (width := width) lib record originals entries inputs before outputs after)
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
      (motive_1 := fun edits input before output after _ => NodeLaw (width := width) lib record originals edits input before output after)
      (motive_2 := fun entries offset inputs before outputs after _ => ChildrenLaw (width := width) lib record originals entries offset inputs before outputs after)
      (motive_3 := fun entries inputs before outputs after _ => RowsLaw (width := width) lib record originals entries inputs before outputs after)
      (fun {_ _ _ _ _} actual => leafCase actual)
      (fun {_ _} => emptyCase)
      (fun {_ _ _ _ _ _ _ _ _ _} actual built ih => ordinaryCase actual built ih)
      (fun {_ _ _ _ _ _ _} recursive head body ih => recursiveCase recursive head body ih)
      (fun {_ _ _} => nilChildren)
      (fun {_ _ _ _ _ _} offset absent rest ih => unselectedCase offset absent rest ih)
      (fun {_ _ _ _ _ _ _ _ _} offset found first rest firstIH restIH => selectedCase offset found first rest firstIH restIH)
      (fun {_ _} => nilRows)
      (fun {_ _ _ _ _ _ _ _ _ _} children built rest firstIH restIH => consRows children built rest firstIH restIH) actual

/-- Every actual node leaf derives its input Type annotation from a retained route. -/
theorem node (lib : Library) {record originals edits input before output after}
    (actual : EditNode (width := width) record originals edits input before output after)
    (ready : Ready lib before) (originalAvailable : Values before.checked.native.machine.heap originals)
    (originalClosed : ClosedValues originals)
    (originalRoutes : ∀ own ∈ record.paths, ForestPath (Origin lib) (own.map Int.ofNat) originals)
    (populated : Populated edits) (nonempty : HasLeaf edits)
    (available : Available before.checked.native.machine.heap input) (closed : input.free = [])
    (paths : NodePaths (Origin lib) edits input) :
    Ready lib after ∧ Extension before.checked.native.machine after.checked.native.machine ∧
      Available after.checked.native.machine.heap output ∧ output.free = [] ∧
      ∀ path, TypePath (Origin lib) path input → TypePath (Origin lib) path output :=
  (preserved lib).1 actual ready originalAvailable originalClosed originalRoutes populated nonempty available closed paths

/-- Ordered child calls retain every forest route and each actual returned state. -/
theorem children (lib : Library) {record originals entries offset inputs before outputs after}
    (actual : EditChildren (width := width) record originals entries offset inputs before outputs after)
    (ready : Ready lib before) (originalAvailable : Values before.checked.native.machine.heap originals)
    (originalClosed : ClosedValues originals)
    (originalRoutes : ∀ own ∈ record.paths, ForestPath (Origin lib) (own.map Int.ofNat) originals)
    (populated : Populated (.editBelow entries)) (available : Values before.checked.native.machine.heap inputs)
    (closed : ClosedValues inputs) (paths : ChildrenPaths (Origin lib) entries offset inputs) :
    Ready lib after ∧ Extension before.checked.native.machine after.checked.native.machine ∧
      Values after.checked.native.machine.heap outputs ∧ ClosedValues outputs ∧ ForestRoutes (Origin lib) inputs outputs := by
  obtain ⟨next, extension, returned, resultClosed, retained⟩ :=
    (preserved lib).2.1 actual ready originalAvailable originalClosed originalRoutes populated available closed paths
  exact ⟨next, extension, returned, resultClosed, aligned_forest retained⟩

/-- Actual row reconstruction retains full guards and every original child route. -/
theorem rows (lib : Library) {record originals entries inputs before outputs after}
    (actual : EditRows (width := width) record originals entries inputs before outputs after)
    (ready : Ready lib before) (originalAvailable : Values before.checked.native.machine.heap originals)
    (originalClosed : ClosedValues originals)
    (originalRoutes : ∀ own ∈ record.paths, ForestPath (Origin lib) (own.map Int.ofNat) originals)
    (populated : Populated (.editBelow entries)) (resident : Edges before.checked.native.machine.heap inputs)
    (closed : ClosedEdges inputs) (paths : ∀ row ∈ inputs, ChildrenPaths (Origin lib) entries 0 row.children) :
    Ready lib after ∧ Extension before.checked.native.machine after.checked.native.machine ∧
      Edges after.checked.native.machine.heap outputs ∧ ClosedEdges outputs ∧ RowRoutes (Origin lib) inputs outputs :=
  (preserved lib).2.2 actual ready originalAvailable originalClosed originalRoutes populated resident closed paths

/-- The actual list entry needs only populated source edits and initial structural routes. -/
theorem list (lib : Library) {record originals edits inputs before outputs after}
    (actual : EditList (width := width) record originals edits inputs before outputs after)
    (ready : Ready lib before) (originalAvailable : Values before.checked.native.machine.heap originals)
    (originalClosed : ClosedValues originals)
    (originalRoutes : ∀ own ∈ record.paths, ForestPath (Origin lib) (own.map Int.ofNat) originals)
    (populated : Populated edits) (available : Values before.checked.native.machine.heap inputs)
    (closed : ClosedValues inputs) (paths : ForestPaths (Origin lib) edits inputs) :
    Ready lib after ∧ Extension before.checked.native.machine after.checked.native.machine ∧
      Values after.checked.native.machine.heap outputs ∧ ClosedValues outputs ∧ ForestRoutes (Origin lib) inputs outputs := by
  cases actual with
  | leaf => exact ⟨ready, .refl _, available, closed, fun _ route => route⟩
  | children actual =>
      exact children lib actual ready originalAvailable originalClosed originalRoutes populated available closed (forest_to_children paths)

end MicroCFTA.SourceSynthesisNativeTypeSharedEdit
