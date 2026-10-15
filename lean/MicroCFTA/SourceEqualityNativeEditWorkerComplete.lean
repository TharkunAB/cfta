import MicroCFTA.SourceEqualityNativeEditWorkerSound
import MicroCFTA.SourceEqualityRequiredWorkerComplete

/-!
# Stable execution of complete simultaneous native edit graphs

The graph supplies independent recursion, head-read, and native-request
bounds. Every larger triple returns the same value and full native state.
-/
namespace MicroCFTA.SourceEqualityNativeEditWorkerComplete
open InternedConstructorTemplates SourceEqualityEdits SourceEqualityNativeScoped SourceEqualityNativeEditGraph SourceEqualityNativeEditWorker

/-- One finite bound triple suffices for identical values and full native states at every larger triple. -/
def StableRun (evaluation : Nat → Nat → Nat → Result width Symbol Guard A) (result : A) (after : NativeState width Symbol Guard) : Prop :=
  ∃ workerBound readBound nativeBound, ∀ fuel readFuel nativeFuel, workerBound ≤ fuel → readBound ≤ readFuel → nativeBound ≤ nativeFuel →
    evaluation fuel readFuel nativeFuel = .done result after

/-- Completed actual head reads remain stable inside their unchanged native wrapper. -/
theorem head_stable [DecidableEq (EdgeKey Symbol Guard)]
    {value result : Value Symbol Guard} {before : NativeState width Symbol Guard} {heap : InternedConstructorTemplates.State Symbol Guard}
    (trace : SourceEqualityRequiredHead.Head value before.machine.heap result heap) :
    ∃ bound, ∀ fuel, bound ≤ fuel → head fuel value before = .done result (advanceHeap before heap) := by
  obtain ⟨bound, stable⟩ := SourceEqualityRequiredWorkerComplete.head_stable trace
  exact ⟨bound, by intro fuel enough; simp only [head, stable fuel enough]⟩

variable {Symbol Guard : Type}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
variable (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)

private def NodeStable (edits : Edits (Value Symbol Guard)) (value : Value Symbol Guard) (before : NativeState width Symbol Guard)
    (result : Value Symbol Guard) (after : NativeState width Symbol Guard) :=
  StableRun (fun fuel readFuel nativeFuel => edit emptyGuard conjoin fuel readFuel nativeFuel edits value before) result after

private def ChildrenStable (entries : List (Int × Edits (Value Symbol Guard))) (index : Nat) (values : List (Value Symbol Guard))
    (before : NativeState width Symbol Guard) (results : List (Value Symbol Guard)) (after : NativeState width Symbol Guard) :=
  StableRun (fun fuel readFuel nativeFuel => children (edit emptyGuard conjoin fuel readFuel nativeFuel) entries index values before) results after

private def RowsStable (entries : List (Int × Edits (Value Symbol Guard))) (edges : List (EdgeValue Symbol Guard))
    (before : NativeState width Symbol Guard) (results : List (EdgeValue Symbol Guard)) (after : NativeState width Symbol Guard) :=
  StableRun (fun fuel readFuel nativeFuel => rows (edit emptyGuard conjoin fuel readFuel nativeFuel) entries edges before) results after

local notation "NodeLaw" => NodeStable (Symbol := Symbol) (width := width) emptyGuard conjoin
local notation "ChildrenLaw" => ChildrenStable (Symbol := Symbol) (width := width) emptyGuard conjoin
local notation "RowsLaw" => RowsStable (Symbol := Symbol) (width := width) emptyGuard conjoin

private theorem stable :
    (∀ edits (value : Value Symbol Guard) (before : NativeState width Symbol Guard) result after,
      EditNode emptyGuard conjoin edits value before result after → NodeLaw edits value before result after) ∧
    (∀ entries index (values : List (Value Symbol Guard)) (before : NativeState width Symbol Guard) results after,
      EditChildren emptyGuard conjoin entries index values before results after → ChildrenLaw entries index values before results after) ∧
    (∀ entries (edges : List (EdgeValue Symbol Guard)) (before : NativeState width Symbol Guard) results after,
      EditRows emptyGuard conjoin entries edges before results after → RowsLaw entries edges before results after) := by
  have leafCase : ∀ {target value before result after}, Step emptyGuard conjoin target value before result after →
      NodeLaw (.editAt target) value before result after := by
    intro target value before result after step
    obtain ⟨bound, stable⟩ := step.stable
    refine ⟨1, 0, bound, ?_⟩
    intro fuel readFuel nativeFuel enough _ nativeEnough
    cases fuel with
    | zero => omega
    | succ fuel => simp only [edit, leaf, stable nativeFuel nativeEnough]
  have emptyCase : ∀ {entries state}, NodeLaw (.editBelow entries) (.empty : Value Symbol Guard) state .empty state := by
    intro entries state
    refine ⟨1, 0, 0, ?_⟩
    intro fuel readFuel nativeFuel enough _ _
    cases fuel with
    | zero => omega
    | succ fuel => rfl
  have ordinaryCase : ∀ {entries edges before rebuilt middle value heap entry depth free},
      EditRows emptyGuard conjoin entries edges before rebuilt middle → run (makeNode rebuilt) middle.machine.heap = (value, heap) →
      RowsLaw entries edges before rebuilt middle → NodeLaw (.editBelow entries) (.node entry edges depth free) before value (advanceHeap middle heap) := by
    intro entries edges before rebuilt middle value heap entry depth free _ built ih
    obtain ⟨bound, readBound, nativeBound, stable⟩ := ih
    refine ⟨bound + 1, readBound, nativeBound, ?_⟩
    intro fuel readFuel nativeFuel enough readEnough nativeEnough
    cases fuel with
    | zero => omega
    | succ fuel => simp only [edit, stable fuel readFuel nativeFuel (by omega) readEnough nativeEnough, Result.bind, work, built]
  have recursiveCase : ∀ {entries original before exposed heap result after},
      SourceEqualityRequiredGraph.Recursive original → SourceEqualityRequiredHead.Head original before.machine.heap exposed heap →
      EditNode emptyGuard conjoin (.editBelow entries) exposed (advanceHeap before heap) result after →
      NodeLaw (.editBelow entries) exposed (advanceHeap before heap) result after → NodeLaw (.editBelow entries) original before result after := by
    intro entries original before exposed heap result after recursive head _ ih
    obtain ⟨bound, readBound, nativeBound, stable⟩ := ih
    obtain ⟨headBound, headStable⟩ := head_stable head
    refine ⟨bound + 1, max readBound headBound, nativeBound, ?_⟩
    intro fuel readFuel nativeFuel enough readEnough nativeEnough
    cases fuel with
    | zero => omega
    | succ fuel =>
        have first := headStable readFuel (Nat.le_trans (Nat.le_max_right _ _) readEnough)
        have body := stable fuel readFuel nativeFuel (by omega) (Nat.le_trans (Nat.le_max_left _ _) readEnough) nativeEnough
        cases original with
        | empty | reference | node => cases recursive
        | union | mu => simp only [edit, first, Result.bind, body]
  have nilChildren : ∀ {entries index state}, ChildrenLaw entries index ([] : List (Value Symbol Guard)) state [] state := by
    intros; exact ⟨0, 0, 0, by intros; rfl⟩
  have unselectedCase : ∀ {entries values before results after value} (index : Nat),
      SourceEqualityNeededMap.lookup (index : Int) entries = none → EditChildren emptyGuard conjoin entries (index + 1) values before results after →
      ChildrenLaw entries (index + 1) values before results after → ChildrenLaw entries index (value :: values) before (value :: results) after := by
    intro entries values before results after value index absent _ ih
    obtain ⟨bound, readBound, nativeBound, stable⟩ := ih
    refine ⟨bound, readBound, nativeBound, ?_⟩
    intro fuel readFuel nativeFuel enough readEnough nativeEnough
    simp only [children, absent, stable fuel readFuel nativeFuel enough readEnough nativeEnough, Result.bind]
  have selectedCase : ∀ {entries edits value before result middle values results after} (index : Nat),
      SourceEqualityNeededMap.lookup (index : Int) entries = some edits → EditNode emptyGuard conjoin edits value before result middle →
      EditChildren emptyGuard conjoin entries (index + 1) values middle results after → NodeLaw edits value before result middle →
      ChildrenLaw entries (index + 1) values middle results after → ChildrenLaw entries index (value :: values) before (result :: results) after := by
    intro entries edits value before result middle values results after index found _ _ firstIH restIH
    obtain ⟨firstBound, firstRead, firstNative, firstStable⟩ := firstIH
    obtain ⟨restBound, restRead, restNative, restStable⟩ := restIH
    refine ⟨max firstBound restBound, max firstRead restRead, max firstNative restNative, ?_⟩
    intro fuel readFuel nativeFuel enough readEnough nativeEnough
    simp only [children, found,
      firstStable fuel readFuel nativeFuel (Nat.le_trans (Nat.le_max_left _ _) enough) (Nat.le_trans (Nat.le_max_left _ _) readEnough) (Nat.le_trans (Nat.le_max_left _ _) nativeEnough),
      Result.bind, restStable fuel readFuel nativeFuel (Nat.le_trans (Nat.le_max_right _ _) enough) (Nat.le_trans (Nat.le_max_right _ _) readEnough) (Nat.le_trans (Nat.le_max_right _ _) nativeEnough)]
  have nilRows : ∀ {entries state}, RowsLaw entries ([] : List (EdgeValue Symbol Guard)) state [] state := by
    intros; exact ⟨0, 0, 0, by intros; rfl⟩
  have consCase : ∀ {entries before values middle result heap edges results after edge},
      EditChildren emptyGuard conjoin entries 0 edge.children before values middle →
      run (makeEdge edge.entry.key.symbol edge.entry.key.constraint values) middle.machine.heap = (result, heap) →
      EditRows emptyGuard conjoin entries edges (advanceHeap middle heap) results after → ChildrenLaw entries 0 edge.children before values middle →
      RowsLaw entries edges (advanceHeap middle heap) results after → RowsLaw entries (edge :: edges) before (result :: results) after := by
    intro entries before values middle result heap edges results after edge _ built _ childIH restIH
    obtain ⟨childBound, childRead, childNative, childStable⟩ := childIH
    obtain ⟨restBound, restRead, restNative, restStable⟩ := restIH
    refine ⟨max childBound restBound, max childRead restRead, max childNative restNative, ?_⟩
    intro fuel readFuel nativeFuel enough readEnough nativeEnough
    simp only [rows,
      childStable fuel readFuel nativeFuel (Nat.le_trans (Nat.le_max_left _ _) enough) (Nat.le_trans (Nat.le_max_left _ _) readEnough) (Nat.le_trans (Nat.le_max_left _ _) nativeEnough),
      Result.bind, work, built, restStable fuel readFuel nativeFuel (Nat.le_trans (Nat.le_max_right _ _) enough) (Nat.le_trans (Nat.le_max_right _ _) readEnough) (Nat.le_trans (Nat.le_max_right _ _) nativeEnough)]
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

/-- Every complete native node edit executes at every sufficient larger bound triple. -/
theorem node_stable {edits value before result after} (trace : EditNode (Symbol := Symbol) (width := width) emptyGuard conjoin edits value before result after) :
    NodeLaw edits value before result after := (stable (Symbol := Symbol) emptyGuard conjoin).1 _ _ _ _ _ trace

/-- Every complete native child scan executes at every sufficient larger bound triple. -/
theorem children_stable {entries index values before results after}
    (trace : EditChildren (Symbol := Symbol) (width := width) emptyGuard conjoin entries index values before results after) :
    ChildrenLaw entries index values before results after := (stable (Symbol := Symbol) emptyGuard conjoin).2.1 _ _ _ _ _ _ trace

/-- Every complete native list edit executes at every sufficient larger bound triple. -/
theorem list_stable {edits values before results after} (trace : EditList (Symbol := Symbol) (width := width) emptyGuard conjoin edits values before results after) :
    StableRun (fun fuel readFuel nativeFuel => editList (edit emptyGuard conjoin fuel readFuel nativeFuel) edits values before) results after := by
  cases trace with
  | leaf => exact ⟨0, 0, 0, by intros; rfl⟩
  | children trace => exact children_stable emptyGuard conjoin trace

end MicroCFTA.SourceEqualityNativeEditWorkerComplete
