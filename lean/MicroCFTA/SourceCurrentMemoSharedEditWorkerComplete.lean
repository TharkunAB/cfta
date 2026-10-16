import MicroCFTA.SourceCurrentMemoSharedEditWorkerSound
import MicroCFTA.SourceEqualityRequiredWorkerComplete

/-!
# Stable execution of shared simultaneous edit graphs

The graph supplies six independent bounds for edit recursion and actual
target stages. Every larger tuple returns the same value, full native
state, and every returned shared target slot.
-/
namespace MicroCFTA.SourceCurrentMemoSharedEditWorkerComplete
open InternedConstructorTemplates SourceEqualityEdits SourceCurrentMemoSharedTargetState SourceCurrentMemoSharedLeafWorker SourceCurrentMemoSharedEditGraph SourceCurrentMemoSharedEditWorker

/-- Six independent finite bounds give identical results and full shared state at all larger bounds. -/
def StableRun (evaluation : Nat → Nat → Nat → Nat → Nat → Nat → Outcome width Symbol Guard A) (result : A) (after : SharedState width Symbol Guard) : Prop :=
  ∃ workerBound projectionBound readBound mergeBound comparisonBound nativeBound, ∀ fuel p readFuel w c nativeFuel,
    workerBound ≤ fuel → projectionBound ≤ p → readBound ≤ readFuel → mergeBound ≤ w → comparisonBound ≤ c → nativeBound ≤ nativeFuel →
    evaluation fuel p readFuel w c nativeFuel = .done result after

/-- Completed actual head reads remain stable inside their unchanged native wrapper. -/
theorem head_stable [DecidableEq (EdgeKey Symbol Guard)]
    {value result : Value Symbol Guard} {before : SharedState width Symbol Guard} {heap : InternedConstructorTemplates.State Symbol Guard}
    (trace : SourceEqualityRequiredHead.Head value before.native.machine.heap result heap) :
    ∃ bound, ∀ fuel, bound ≤ fuel → head fuel value before = .done result (advanceHeap before heap) := by
  obtain ⟨bound, stable⟩ := SourceEqualityRequiredWorkerComplete.head_stable trace
  exact ⟨bound, by intro fuel enough; simp only [head, stable fuel enough]⟩

variable {Symbol Guard : Type}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
variable (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (clear : Guard → Bool) (top : Guard)
variable (record : SourceEqualityClassOrder.Record) (originals : List (Value Symbol Guard))

private def NodeStable (edits : Edits EqualityNormalize.Path) (value : Value Symbol Guard) (before : SharedState width Symbol Guard)
    (result : Value Symbol Guard) (after : SharedState width Symbol Guard) :=
  StableRun (fun fuel p readFuel w c nativeFuel => edit emptyGuard conjoin clear top record originals fuel p readFuel w c nativeFuel edits value before) result after

private def ChildrenStable (entries : List (Int × Edits EqualityNormalize.Path)) (index : Nat) (values : List (Value Symbol Guard))
    (before : SharedState width Symbol Guard) (results : List (Value Symbol Guard)) (after : SharedState width Symbol Guard) :=
  StableRun (fun fuel p readFuel w c nativeFuel => children (edit emptyGuard conjoin clear top record originals fuel p readFuel w c nativeFuel) entries index values before) results after

private def RowsStable (entries : List (Int × Edits EqualityNormalize.Path)) (edges : List (EdgeValue Symbol Guard))
    (before : SharedState width Symbol Guard) (results : List (EdgeValue Symbol Guard)) (after : SharedState width Symbol Guard) :=
  StableRun (fun fuel p readFuel w c nativeFuel => rows (edit emptyGuard conjoin clear top record originals fuel p readFuel w c nativeFuel) entries edges before) results after

local notation "NodeLaw" => NodeStable (Symbol := Symbol) (width := width) emptyGuard conjoin clear top record originals
local notation "ChildrenLaw" => ChildrenStable (Symbol := Symbol) (width := width) emptyGuard conjoin clear top record originals
local notation "RowsLaw" => RowsStable (Symbol := Symbol) (width := width) emptyGuard conjoin clear top record originals

private theorem stable :
    (∀ edits (value : Value Symbol Guard) (before : SharedState width Symbol Guard) result after,
      EditNode emptyGuard conjoin clear top record originals edits value before result after → NodeLaw edits value before result after) ∧
    (∀ entries index (values : List (Value Symbol Guard)) (before : SharedState width Symbol Guard) results after,
      EditChildren emptyGuard conjoin clear top record originals entries index values before results after → ChildrenLaw entries index values before results after) ∧
    (∀ entries (edges : List (EdgeValue Symbol Guard)) (before : SharedState width Symbol Guard) results after,
      EditRows emptyGuard conjoin clear top record originals entries edges before results after → RowsLaw entries edges before results after) := by
  have leafCase : ∀ {target value before result after}, SourceCurrentMemoSharedTargetLeaf.Leaf emptyGuard conjoin clear top record originals target value before result after →
      NodeLaw (.editAt target) value before result after := by
    intro target value before result after step
    obtain ⟨p, h, w, c, n, stable⟩ := SourceCurrentMemoSharedLeafWorkerProofs.leaf_stable emptyGuard conjoin clear top record originals step
    refine ⟨1, p, h, w, c, n, ?_⟩
    intro fuel projection readFuel w comparison nativeFuel enough ep eh ew ec en
    cases fuel with
    | zero => omega
    | succ fuel => exact stable projection readFuel w comparison nativeFuel ep eh ew ec en
  have emptyCase : ∀ {entries state}, NodeLaw (.editBelow entries) (.empty : Value Symbol Guard) state .empty state := by
    intro entries state
    refine ⟨1, 0, 0, 0, 0, 0, ?_⟩
    intro fuel p readFuel w c nativeFuel enough _ _ _ _ _
    cases fuel with
    | zero => omega
    | succ fuel => rfl
  have ordinaryCase : ∀ {entries edges before rebuilt middle value heap entry depth free},
      EditRows emptyGuard conjoin clear top record originals entries edges before rebuilt middle → run (makeNode rebuilt) middle.native.machine.heap = (value, heap) →
      RowsLaw entries edges before rebuilt middle → NodeLaw (.editBelow entries) (.node entry edges depth free) before value (advanceHeap middle heap) := by
    intro entries edges before rebuilt middle value heap entry depth free _ built ih
    obtain ⟨bound, projectionBound, readBound, mergeBound, comparisonBound, nativeBound, stable⟩ := ih
    refine ⟨bound + 1, projectionBound, readBound, mergeBound, comparisonBound, nativeBound, ?_⟩
    intro fuel p readFuel w c nativeFuel enough projectionEnough readEnough mergeEnough comparisonEnough nativeEnough
    cases fuel with
    | zero => omega
    | succ fuel => simp only [edit, stable fuel p readFuel w c nativeFuel (by omega) projectionEnough readEnough mergeEnough comparisonEnough nativeEnough, Outcome.bind, work, built]
  have recursiveCase : ∀ {entries original before exposed heap result after},
      SourceEqualityRequiredGraph.Recursive original → SourceEqualityRequiredHead.Head original before.native.machine.heap exposed heap →
      EditNode emptyGuard conjoin clear top record originals (.editBelow entries) exposed (advanceHeap before heap) result after →
      NodeLaw (.editBelow entries) exposed (advanceHeap before heap) result after → NodeLaw (.editBelow entries) original before result after := by
    intro entries original before exposed heap result after recursive head _ ih
    obtain ⟨bound, projectionBound, readBound, mergeBound, comparisonBound, nativeBound, stable⟩ := ih
    obtain ⟨headBound, headStable⟩ := head_stable head
    refine ⟨bound + 1, projectionBound, max readBound headBound, mergeBound, comparisonBound, nativeBound, ?_⟩
    intro fuel p readFuel w c nativeFuel enough projectionEnough readEnough mergeEnough comparisonEnough nativeEnough
    cases fuel with
    | zero => omega
    | succ fuel =>
        have first := headStable readFuel (Nat.le_trans (Nat.le_max_right _ _) readEnough)
        have body := stable fuel p readFuel w c nativeFuel (by omega) projectionEnough (Nat.le_trans (Nat.le_max_left _ _) readEnough) mergeEnough comparisonEnough nativeEnough
        cases original with
        | empty | reference | node => cases recursive
        | union | mu => simp only [edit, first, Outcome.bind, body]
  have nilChildren : ∀ {entries index state}, ChildrenLaw entries index ([] : List (Value Symbol Guard)) state [] state := by
    intros; exact ⟨0, 0, 0, 0, 0, 0, by intros; rfl⟩
  have unselectedCase : ∀ {entries values before results after value} (index : Nat),
      SourceEqualityNeededMap.lookup (index : Int) entries = none → EditChildren emptyGuard conjoin clear top record originals entries (index + 1) values before results after →
      ChildrenLaw entries (index + 1) values before results after → ChildrenLaw entries index (value :: values) before (value :: results) after := by
    intro entries values before results after value index absent _ ih
    obtain ⟨bound, projectionBound, readBound, mergeBound, comparisonBound, nativeBound, stable⟩ := ih
    refine ⟨bound, projectionBound, readBound, mergeBound, comparisonBound, nativeBound, ?_⟩
    intro fuel p readFuel w c nativeFuel enough projectionEnough readEnough mergeEnough comparisonEnough nativeEnough
    simp only [children, absent, stable fuel p readFuel w c nativeFuel enough projectionEnough readEnough mergeEnough comparisonEnough nativeEnough, Outcome.bind]
  have selectedCase : ∀ {entries edits value before result middle values results after} (index : Nat),
      SourceEqualityNeededMap.lookup (index : Int) entries = some edits → EditNode emptyGuard conjoin clear top record originals edits value before result middle →
      EditChildren emptyGuard conjoin clear top record originals entries (index + 1) values middle results after → NodeLaw edits value before result middle →
      ChildrenLaw entries (index + 1) values middle results after → ChildrenLaw entries index (value :: values) before (result :: results) after := by
    intro entries edits value before result middle values results after index found _ _ firstIH restIH
    obtain ⟨firstBound, firstProjection, firstRead, firstMerge, firstComparison, firstNative, firstStable⟩ := firstIH
    obtain ⟨restBound, restProjection, restRead, restMerge, restComparison, restNative, restStable⟩ := restIH
    refine ⟨max firstBound restBound, max firstProjection restProjection, max firstRead restRead, max firstMerge restMerge, max firstComparison restComparison, max firstNative restNative, ?_⟩
    intro fuel p readFuel w c nativeFuel enough projectionEnough readEnough mergeEnough comparisonEnough nativeEnough
    simp only [children, found,
      firstStable fuel p readFuel w c nativeFuel (Nat.le_trans (Nat.le_max_left _ _) enough) (Nat.le_trans (Nat.le_max_left _ _) projectionEnough) (Nat.le_trans (Nat.le_max_left _ _) readEnough) (Nat.le_trans (Nat.le_max_left _ _) mergeEnough) (Nat.le_trans (Nat.le_max_left _ _) comparisonEnough) (Nat.le_trans (Nat.le_max_left _ _) nativeEnough),
      Outcome.bind, restStable fuel p readFuel w c nativeFuel (Nat.le_trans (Nat.le_max_right _ _) enough) (Nat.le_trans (Nat.le_max_right _ _) projectionEnough) (Nat.le_trans (Nat.le_max_right _ _) readEnough) (Nat.le_trans (Nat.le_max_right _ _) mergeEnough) (Nat.le_trans (Nat.le_max_right _ _) comparisonEnough) (Nat.le_trans (Nat.le_max_right _ _) nativeEnough)]
  have nilRows : ∀ {entries state}, RowsLaw entries ([] : List (EdgeValue Symbol Guard)) state [] state := by
    intros; exact ⟨0, 0, 0, 0, 0, 0, by intros; rfl⟩
  have consCase : ∀ {entries before values middle result heap edges results after edge},
      EditChildren emptyGuard conjoin clear top record originals entries 0 edge.children before values middle →
      run (makeEdge edge.entry.key.symbol edge.entry.key.constraint values) middle.native.machine.heap = (result, heap) →
      EditRows emptyGuard conjoin clear top record originals entries edges (advanceHeap middle heap) results after → ChildrenLaw entries 0 edge.children before values middle →
      RowsLaw entries edges (advanceHeap middle heap) results after → RowsLaw entries (edge :: edges) before (result :: results) after := by
    intro entries before values middle result heap edges results after edge _ built _ childIH restIH
    obtain ⟨childBound, childProjection, childRead, childMerge, childComparison, childNative, childStable⟩ := childIH
    obtain ⟨restBound, restProjection, restRead, restMerge, restComparison, restNative, restStable⟩ := restIH
    refine ⟨max childBound restBound, max childProjection restProjection, max childRead restRead, max childMerge restMerge, max childComparison restComparison, max childNative restNative, ?_⟩
    intro fuel p readFuel w c nativeFuel enough projectionEnough readEnough mergeEnough comparisonEnough nativeEnough
    simp only [rows,
      childStable fuel p readFuel w c nativeFuel (Nat.le_trans (Nat.le_max_left _ _) enough) (Nat.le_trans (Nat.le_max_left _ _) projectionEnough) (Nat.le_trans (Nat.le_max_left _ _) readEnough) (Nat.le_trans (Nat.le_max_left _ _) mergeEnough) (Nat.le_trans (Nat.le_max_left _ _) comparisonEnough) (Nat.le_trans (Nat.le_max_left _ _) nativeEnough),
      Outcome.bind, work, built, restStable fuel p readFuel w c nativeFuel (Nat.le_trans (Nat.le_max_right _ _) enough) (Nat.le_trans (Nat.le_max_right _ _) projectionEnough) (Nat.le_trans (Nat.le_max_right _ _) readEnough) (Nat.le_trans (Nat.le_max_right _ _) mergeEnough) (Nat.le_trans (Nat.le_max_right _ _) comparisonEnough) (Nat.le_trans (Nat.le_max_right _ _) nativeEnough)]
  refine ⟨?_, ?_, ?_⟩
  · intro edits value before result after trace
    exact EditNode.rec (motive_1 := fun edits value before result after _ => NodeLaw edits value before result after)
      (motive_2 := fun entries index values before results after _ => ChildrenLaw entries index values before results after)
      (motive_3 := fun entries edges before results after _ => RowsLaw entries edges before results after)
      leafCase emptyCase ordinaryCase recursiveCase (fun {_ _ _} => nilChildren) unselectedCase selectedCase (fun {_ _} => nilRows) consCase trace
  · intro entries index values before results after trace
    exact EditChildren.rec (motive_1 := fun edits value before result after _ => NodeLaw edits value before result after)
      (motive_2 := fun entries index values before results after _ => ChildrenLaw entries index values before results after)
      (motive_3 := fun entries edges before results after _ => RowsLaw entries edges before results after)
      leafCase emptyCase ordinaryCase recursiveCase (fun {_ _ _} => nilChildren) unselectedCase selectedCase (fun {_ _} => nilRows) consCase trace
  · intro entries edges before results after trace
    exact EditRows.rec (motive_1 := fun edits value before result after _ => NodeLaw edits value before result after)
      (motive_2 := fun entries index values before results after _ => ChildrenLaw entries index values before results after)
      (motive_3 := fun entries edges before results after _ => RowsLaw entries edges before results after)
      leafCase emptyCase ordinaryCase recursiveCase (fun {_ _ _} => nilChildren) unselectedCase selectedCase (fun {_ _} => nilRows) consCase trace

/-- Every complete native node edit executes at every sufficient larger bound tuple. -/
theorem node_stable {edits value before result after} (trace : EditNode (Symbol := Symbol) (width := width) emptyGuard conjoin clear top record originals edits value before result after) :
    NodeLaw edits value before result after := (stable (Symbol := Symbol) emptyGuard conjoin clear top record originals).1 _ _ _ _ _ trace

/-- Every complete native child scan executes at every sufficient larger bound tuple. -/
theorem children_stable {entries index values before results after}
    (trace : EditChildren (Symbol := Symbol) (width := width) emptyGuard conjoin clear top record originals entries index values before results after) :
    ChildrenLaw entries index values before results after := (stable (Symbol := Symbol) emptyGuard conjoin clear top record originals).2.1 _ _ _ _ _ _ trace

/-- Every complete native list edit executes at every sufficient larger bound tuple. -/
theorem list_stable {edits values before results after} (trace : EditList (Symbol := Symbol) (width := width) emptyGuard conjoin clear top record originals edits values before results after) :
    StableRun (fun fuel p readFuel w c nativeFuel => editList (edit emptyGuard conjoin clear top record originals fuel p readFuel w c nativeFuel) edits values before) results after := by
  cases trace with
  | leaf => exact ⟨0, 0, 0, 0, 0, 0, by intros; rfl⟩
  | children trace => exact children_stable emptyGuard conjoin clear top record originals trace

end MicroCFTA.SourceCurrentMemoSharedEditWorkerComplete
