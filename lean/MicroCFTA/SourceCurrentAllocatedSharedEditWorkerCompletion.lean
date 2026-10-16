import MicroCFTA.SourceCurrentAllocatedSharedEditWorker
import MicroCFTA.SourceCurrentAllocatedSharedTargetWorkerCompletion
import MicroCFTA.SourceEqualityRequiredWorkerComplete

/-!
# Stable execution of current checked simultaneous edits

The graph supplies six independent bounds for edit recursion and actual
target stages. Every larger tuple returns the same value, full native
state, equality operations, completed merge table, and target slots.
These are graph completion bounds. They do not establish outer termination
or host demand and publication.
-/
namespace MicroCFTA.SourceCurrentAllocatedSharedEditWorkerCompletion
open InternedConstructorTemplates SourceEqualityEdits
open SourceCurrentAllocatedSharedEditGraph SourceCurrentAllocatedSharedEditWorker
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula

/-- Six independent finite bounds give identical results and full shared state at all larger bounds. -/
def StableRun (evaluation : Nat → Nat → Nat → Nat → Nat → Nat → Outcome width A) (result : A) (after : SharedState width) : Prop :=
  ∃ workerBound projectionBound readBound mergeBound comparisonBound nativeBound, ∀ fuel p readFuel w c nativeFuel,
    workerBound ≤ fuel → projectionBound ≤ p → readBound ≤ readFuel → mergeBound ≤ w → comparisonBound ≤ c → nativeBound ≤ nativeFuel →
    evaluation fuel p readFuel w c nativeFuel = .done result after

/-- One shared upper bound supplies all six independently derived stage bounds. -/
theorem stable_uniform {evaluation : Nat → Nat → Nat → Nat → Nat → Nat → Outcome width A}
    {result : A} {after : SharedState width} (actual : StableRun evaluation result after) :
    ∃ bound, ∀ fuel, bound ≤ fuel → evaluation fuel fuel fuel fuel fuel fuel = .done result after := by
  obtain ⟨e, p, h, m, s, n, done⟩ := actual
  refine ⟨max (max (max (max (max e p) h) m) s) n, ?_⟩
  intro fuel enough
  exact done fuel fuel fuel fuel fuel fuel (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)

/-- Completed actual head reads remain stable inside their unchanged native wrapper. -/
theorem head_stable [DecidableEq (EdgeKey Symbol Guard)]
    {value result : Value Symbol Guard} {before : SharedState width} {heap : InternedConstructorTemplates.State Symbol Guard}
    (trace : SourceEqualityRequiredHead.Head value before.checked.native.machine.heap result heap) :
    ∃ bound, ∀ fuel, bound ≤ fuel → head fuel value before = .done result (advanceHeap before heap) := by
  obtain ⟨bound, stable⟩ := SourceEqualityRequiredWorkerComplete.head_stable trace
  exact ⟨bound, by intro fuel enough; simp only [head, stable fuel enough]⟩

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
variable (record : SourceEqualityClassOrder.Record) (originals : List (Value Symbol Guard))

private def NodeStable (edits : Edits EqualityNormalize.Path) (value : Value Symbol Guard) (before : SharedState width)
    (result : Value Symbol Guard) (after : SharedState width) :=
  StableRun (fun fuel p readFuel w c nativeFuel => edit record originals fuel p readFuel w c nativeFuel edits value before) result after

private def ChildrenStable (entries : List (Int × Edits EqualityNormalize.Path)) (index : Nat) (values : List (Value Symbol Guard))
    (before : SharedState width) (results : List (Value Symbol Guard)) (after : SharedState width) :=
  StableRun (fun fuel p readFuel w c nativeFuel => children (edit record originals fuel p readFuel w c nativeFuel) entries index values before) results after

private def RowsStable (entries : List (Int × Edits EqualityNormalize.Path)) (edges : List (EdgeValue Symbol Guard))
    (before : SharedState width) (results : List (EdgeValue Symbol Guard)) (after : SharedState width) :=
  StableRun (fun fuel p readFuel w c nativeFuel => rows (edit record originals fuel p readFuel w c nativeFuel) entries edges before) results after

local notation "NodeLaw" => NodeStable (width := width) record originals
local notation "ChildrenLaw" => ChildrenStable (width := width) record originals
local notation "RowsLaw" => RowsStable (width := width) record originals

private theorem stable :
    (∀ edits (value : Value Symbol Guard) (before : SharedState width) result after,
      EditNode record originals edits value before result after → NodeLaw edits value before result after) ∧
    (∀ entries index (values : List (Value Symbol Guard)) (before : SharedState width) results after,
      EditChildren record originals entries index values before results after → ChildrenLaw entries index values before results after) ∧
    (∀ entries (edges : List (EdgeValue Symbol Guard)) (before : SharedState width) results after,
      EditRows record originals entries edges before results after → RowsLaw entries edges before results after) := by
  have leafCase : ∀ {target value before result after}, SourceCurrentAllocatedSharedTargetLeaf.Leaf record originals target value before result after →
      NodeLaw (.editAt target) value before result after := by
    intro target value before result after step
    obtain ⟨p, h, w, c, n, stable⟩ := SourceCurrentAllocatedSharedTargetWorkerCompletion.leaf_complete step
    refine ⟨1, p, h, w, c, n, ?_⟩
    intro fuel projection readFuel w comparison nativeFuel enough ep eh ew ec en
    cases fuel with
    | zero => omega
    | succ fuel =>
        simp only [edit, leaf, lift,
          stable projection readFuel w comparison nativeFuel ep eh ew ec en]
  have emptyCase : ∀ {entries state}, NodeLaw (.editBelow entries) (.empty : Value Symbol Guard) state .empty state := by
    intro entries state
    refine ⟨1, 0, 0, 0, 0, 0, ?_⟩
    intro fuel p readFuel w c nativeFuel enough _ _ _ _ _
    cases fuel with
    | zero => omega
    | succ fuel => rfl
  have ordinaryCase : ∀ {entries edges before rebuilt middle value heap entry depth free},
      EditRows record originals entries edges before rebuilt middle → run (makeNode rebuilt) middle.checked.native.machine.heap = (value, heap) →
      RowsLaw entries edges before rebuilt middle → NodeLaw (.editBelow entries) (.node entry edges depth free) before value (advanceHeap middle heap) := by
    intro entries edges before rebuilt middle value heap entry depth free _ built ih
    obtain ⟨bound, projectionBound, readBound, mergeBound, comparisonBound, nativeBound, stable⟩ := ih
    refine ⟨bound + 1, projectionBound, readBound, mergeBound, comparisonBound, nativeBound, ?_⟩
    intro fuel p readFuel w c nativeFuel enough projectionEnough readEnough mergeEnough comparisonEnough nativeEnough
    cases fuel with
    | zero => omega
    | succ fuel => simp only [edit, stable fuel p readFuel w c nativeFuel (by omega) projectionEnough readEnough mergeEnough comparisonEnough nativeEnough, Outcome.bind, work, built]
  have recursiveCase : ∀ {entries original before exposed heap result after},
      SourceEqualityRequiredGraph.Recursive original → SourceEqualityRequiredHead.Head original before.checked.native.machine.heap exposed heap →
      EditNode record originals (.editBelow entries) exposed (advanceHeap before heap) result after →
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
      SourceEqualityNeededMap.lookup (index : Int) entries = none → EditChildren record originals entries (index + 1) values before results after →
      ChildrenLaw entries (index + 1) values before results after → ChildrenLaw entries index (value :: values) before (value :: results) after := by
    intro entries values before results after value index absent _ ih
    obtain ⟨bound, projectionBound, readBound, mergeBound, comparisonBound, nativeBound, stable⟩ := ih
    refine ⟨bound, projectionBound, readBound, mergeBound, comparisonBound, nativeBound, ?_⟩
    intro fuel p readFuel w c nativeFuel enough projectionEnough readEnough mergeEnough comparisonEnough nativeEnough
    simp only [children, absent, stable fuel p readFuel w c nativeFuel enough projectionEnough readEnough mergeEnough comparisonEnough nativeEnough, Outcome.bind]
  have selectedCase : ∀ {entries edits value before result middle values results after} (index : Nat),
      SourceEqualityNeededMap.lookup (index : Int) entries = some edits → EditNode record originals edits value before result middle →
      EditChildren record originals entries (index + 1) values middle results after → NodeLaw edits value before result middle →
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
      EditChildren record originals entries 0 edge.children before values middle →
      run (makeEdge edge.entry.key.symbol edge.entry.key.constraint values) middle.checked.native.machine.heap = (result, heap) →
      EditRows record originals entries edges (advanceHeap middle heap) results after → ChildrenLaw entries 0 edge.children before values middle →
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

variable {record originals}

/-- Every complete checked node edit executes at every sufficient larger bound tuple. -/
theorem node_complete {edits value before result after} (trace : EditNode (width := width) record originals edits value before result after) :
    StableRun (fun e p h m s n => edit record originals e p h m s n edits value before) result after :=
  (stable record originals).1 _ _ _ _ _ trace

/-- Every complete native child scan executes at every sufficient larger bound tuple. -/
theorem children_complete {entries index values before results after}
    (trace : EditChildren (width := width) record originals entries index values before results after) :
    StableRun (fun e p h m s n => children (edit record originals e p h m s n) entries index values before) results after :=
  (stable record originals).2.1 _ _ _ _ _ _ trace

/-- Every complete ordered row traversal executes with its exact edge constructor states. -/
theorem rows_complete {entries edges before results after}
    (trace : EditRows (width := width) record originals entries edges before results after) :
    StableRun (fun e p h m s n => rows (edit record originals e p h m s n) entries edges before) results after :=
  (stable record originals).2.2 _ _ _ _ _ trace

/-- Every complete native list edit executes at every sufficient larger bound tuple. -/
theorem list_complete {edits values before results after} (trace : EditList (width := width) record originals edits values before results after) :
    StableRun (fun fuel p readFuel w c nativeFuel => editList (edit record originals fuel p readFuel w c nativeFuel) edits values before) results after := by
  cases trace with
  | leaf => exact ⟨0, 0, 0, 0, 0, 0, by intros; rfl⟩
  | children trace => exact children_complete trace

/-- Compiling the literal signed edit list retains the same graph-derived bounds. -/
theorem editAll_complete {edits : List (Path × EqualityNormalize.Path)} {values before results after}
    (trace : EditList (width := width) record originals (build edits) values before results after) :
    StableRun (fun e p h m s n => editAll record originals e p h m s n edits values before) results after :=
  list_complete trace

/-- A completed checked node edit derives one uniform fuel for all six stages. -/
theorem node_uniform {edits value before result after}
    (trace : EditNode (width := width) record originals edits value before result after) :
    ∃ bound, ∀ fuel, bound ≤ fuel → edit record originals fuel fuel fuel fuel fuel fuel edits value before = .done result after :=
  stable_uniform (node_complete trace)

/-- A completed child-list edit derives one uniform fuel and the same full shared state. -/
theorem list_uniform {edits values before results after}
    (trace : EditList (width := width) record originals edits values before results after) :
    ∃ bound, ∀ fuel, bound ≤ fuel →
      editList (edit record originals fuel fuel fuel fuel fuel fuel) edits values before = .done results after :=
  stable_uniform (list_complete trace)

/-- A completed signed edit list derives a uniform bound for its literal compiled worker. -/
theorem editAll_uniform {edits : List (Path × EqualityNormalize.Path)} {values before results after}
    (trace : EditList (width := width) record originals (build edits) values before results after) :
    ∃ bound, ∀ fuel, bound ≤ fuel →
      editAll record originals fuel fuel fuel fuel fuel fuel edits values before = .done results after :=
  stable_uniform (editAll_complete trace)

end MicroCFTA.SourceCurrentAllocatedSharedEditWorkerCompletion
