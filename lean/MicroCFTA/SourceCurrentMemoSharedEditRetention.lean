import MicroCFTA.SourceCurrentMemoSharedEditGraph

/-!
# Exact shared target value retention through simultaneous edits

First force fills an empty closure slot. No later source branch replaces
that returned value. Native requests, recursive heads, and every ordered
row retain the original physical value in each previously returned slot.
-/
namespace MicroCFTA.SourceCurrentMemoSharedEditRetention
open InternedConstructorTemplates SourceEqualityEdits
open SourceCurrentMemoSharedTargetState SourceCurrentMemoSharedTargetForce SourceCurrentMemoSharedTargetLeaf SourceCurrentMemoSharedEditGraph

/-- A first force preserves every previously returned slot; reuse preserves the entire shared state. -/
theorem force_retains [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {emptyGuard : Guard} {conjoin : Guard → Guard → Guard} {clear : Guard → Bool} {top : Guard}
    {record : SourceEqualityClassOrder.Record} {originals : List (Value Symbol Guard)} {path : EqualityNormalize.Path}
    {before after : SharedState width Symbol Guard} {value : Value Symbol Guard}
    (trace : Force emptyGuard conjoin clear top record originals path before value after) : Retains before after := by
  cases trace with
  | hit => exact fun _ _ present => present
  | miss absent _ =>
      intro other target present
      by_cases same : other = path
      · subst other; rw [absent] at present; cases present
      · simpa only [SourceCurrentMemoSharedTargetState.store, Cache.put, same, ite_false] using present

/-- A returned slot permits only exact reuse; no later force can reconstruct its target. -/
theorem force_reuses [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {emptyGuard : Guard} {conjoin : Guard → Guard → Guard} {clear : Guard → Bool} {top : Guard}
    {record : SourceEqualityClassOrder.Record} {originals : List (Value Symbol Guard)} {path : EqualityNormalize.Path}
    {before after : SharedState width Symbol Guard} {value stored : Value Symbol Guard}
    (trace : Force emptyGuard conjoin clear top record originals path before value after) (present : before.targets path = some stored) :
    value = stored ∧ after = before := by
  cases trace with
  | hit actual => exact ⟨Option.some.inj (actual.symm.trans present), rfl⟩
  | miss absent _ => rw [absent] at present; cases present

/-- Actual native leaves retain all returned class target values without semantic premises. -/
theorem leaf_retains [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {emptyGuard : Guard} {conjoin : Guard → Guard → Guard} {clear : Guard → Bool} {top : Guard}
    {record : SourceEqualityClassOrder.Record} {originals : List (Value Symbol Guard)} {path : EqualityNormalize.Path}
    {before after : SharedState width Symbol Guard} {input result : Value Symbol Guard}
    (trace : Leaf (width := width) emptyGuard conjoin clear top record originals path input before result after) : Retains before after := by
  cases trace with
  | apply forced _ => exact (force_retains forced).trans (advance_retains _ _)

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
variable (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (clear : Guard → Bool) (top : Guard)
variable (record : SourceEqualityClassOrder.Record) (originals : List (Value Symbol Guard))

private theorem all_retains :
    (∀ edits (value : Value Symbol Guard) (before : SharedState width Symbol Guard) result after,
      EditNode (width := width) emptyGuard conjoin clear top record originals edits value before result after → Retains before after) ∧
    (∀ entries index (values : List (Value Symbol Guard)) (before : SharedState width Symbol Guard) results after,
      EditChildren (width := width) emptyGuard conjoin clear top record originals entries index values before results after → Retains before after) ∧
    (∀ entries (edges : List (EdgeValue Symbol Guard)) (before : SharedState width Symbol Guard) results after,
      EditRows (width := width) emptyGuard conjoin clear top record originals entries edges before results after → Retains before after) := by
  have leafCase : ∀ {target value before result after}, Leaf (width := width) emptyGuard conjoin clear top record originals target value before result after → Retains before after :=
    fun trace => leaf_retains trace
  have emptyCase : ∀ {entries : List (Int × Edits EqualityNormalize.Path)} {state}, Retains (state : SharedState width Symbol Guard) state := fun _ _ present => present
  have ordinaryCase : ∀ {entries edges before rebuilt middle value heap} {entry : Cache.Interned InternedBinderProtocol.NodeKey} {depth : Nat} {free : List InternedBinderProtocol.Reference},
      EditRows (width := width) emptyGuard conjoin clear top record originals entries edges before rebuilt middle →
      run (makeNode rebuilt) middle.native.machine.heap = (value, heap) → Retains before middle → Retains before (advanceHeap middle heap) := by
    intro entries edges before rebuilt middle value heap entry depth free _ _ kept
    exact kept.trans (advance_retains _ _)
  have recursiveCase : ∀ {original exposed heap entries before result after},
      SourceEqualityRequiredGraph.Recursive original → SourceEqualityRequiredHead.Head original before.native.machine.heap exposed heap →
      EditNode (width := width) emptyGuard conjoin clear top record originals (.editBelow entries) exposed (advanceHeap before heap) result after →
      Retains (advanceHeap before heap) after → Retains before after := by
    intro original exposed heap entries before result after _ _ _ kept
    exact (advance_retains _ _).trans kept
  have nilChildren : ∀ {entries : List (Int × Edits EqualityNormalize.Path)} {index : Nat} {state}, Retains (state : SharedState width Symbol Guard) state := fun _ _ present => present
  have unselectedCase : ∀ {entries values before results after} {value : Value Symbol Guard} (index : Nat),
      SourceEqualityNeededMap.lookup (index : Int) entries = none →
      EditChildren (width := width) emptyGuard conjoin clear top record originals entries (index + 1) values before results after → Retains before after → Retains before after := by
    intro entries values before results after value index _ _ kept; exact kept
  have selectedCase : ∀ {entries edits value before result middle values results after} (index : Nat),
      SourceEqualityNeededMap.lookup (index : Int) entries = some edits →
      EditNode (width := width) emptyGuard conjoin clear top record originals edits value before result middle →
      EditChildren (width := width) emptyGuard conjoin clear top record originals entries (index + 1) values middle results after →
      Retains before middle → Retains middle after → Retains before after := by
    intro entries edits value before result middle values results after index _ _ _ first rest; exact first.trans rest
  have nilRows : ∀ {entries : List (Int × Edits EqualityNormalize.Path)} {state}, Retains (state : SharedState width Symbol Guard) state := fun _ _ present => present
  have consCase : ∀ {entries before values middle result heap edges results after} {edge : EdgeValue Symbol Guard},
      EditChildren (width := width) emptyGuard conjoin clear top record originals entries 0 edge.children before values middle →
      run (makeEdge edge.entry.key.symbol edge.entry.key.constraint values) middle.native.machine.heap = (result, heap) →
      EditRows (width := width) emptyGuard conjoin clear top record originals entries edges (advanceHeap middle heap) results after →
      Retains before middle → Retains (advanceHeap middle heap) after → Retains before after := by
    intro entries before values middle result heap edges results after edge _ _ _ first rest
    exact first.trans ((advance_retains _ _).trans rest)
  refine ⟨?_, ?_, ?_⟩
  · intro edits value before result after trace
    exact EditNode.rec (motive_1 := fun _ _ before _ after _ => Retains before after)
      (motive_2 := fun _ _ _ before _ after _ => Retains before after) (motive_3 := fun _ _ before _ after _ => Retains before after)
      @leafCase @emptyCase @ordinaryCase @recursiveCase @nilChildren @unselectedCase @selectedCase @nilRows @consCase trace
  · intro entries index values before results after trace
    exact EditChildren.rec (motive_1 := fun _ _ before _ after _ => Retains before after)
      (motive_2 := fun _ _ _ before _ after _ => Retains before after) (motive_3 := fun _ _ before _ after _ => Retains before after)
      @leafCase @emptyCase @ordinaryCase @recursiveCase @nilChildren @unselectedCase @selectedCase @nilRows @consCase trace
  · intro entries edges before results after trace
    exact EditRows.rec (motive_1 := fun _ _ before _ after _ => Retains before after)
      (motive_2 := fun _ _ _ before _ after _ => Retains before after) (motive_3 := fun _ _ before _ after _ => Retains before after)
      @leafCase @emptyCase @ordinaryCase @recursiveCase @nilChildren @unselectedCase @selectedCase @nilRows @consCase trace

/-- Every completed node edit retains all earlier returned target slots exactly. -/
theorem node {edits value before result after} (trace : EditNode (width := width) emptyGuard conjoin clear top record originals edits value before result after) : Retains before after :=
  (all_retains emptyGuard conjoin clear top record originals).1 _ _ _ _ _ trace

/-- Every ordered child scan retains all earlier returned target slots exactly. -/
theorem children {entries index values before results after}
    (trace : EditChildren (width := width) emptyGuard conjoin clear top record originals entries index values before results after) : Retains before after :=
  (all_retains emptyGuard conjoin clear top record originals).2.1 _ _ _ _ _ _ trace

/-- Every ordered row scan retains all earlier returned target slots exactly. -/
theorem rows {entries edges before results after}
    (trace : EditRows (width := width) emptyGuard conjoin clear top record originals entries edges before results after) : Retains before after :=
  (all_retains emptyGuard conjoin clear top record originals).2.2 _ _ _ _ _ trace

/-- Completed merge entries retain their values and actual producer histories. -/
private def Entries (before after : SharedState width Symbol Guard) : Prop :=
  Cache.Extends before.memo after.memo ∧
    (SourceCurrentMemoMergeOrigins.Produced clear top before.memo → SourceCurrentMemoMergeOrigins.Produced clear top after.memo)

private theorem Entries.trans {clear : Guard → Bool} {top : Guard} {before middle after : SharedState width Symbol Guard}
    (first : Entries clear top before middle) (second : Entries clear top middle after) : Entries clear top before after :=
  ⟨Cache.extends_trans first.1 second.1, fun produced => second.2 (first.2 produced)⟩

private theorem advance_entries (before : SharedState width Symbol Guard) (native : SourceRecursiveIntersectionThunks.State width Symbol Guard) :
    Entries clear top before (advance before native) := ⟨Cache.extends_refl _, id⟩

private theorem all_entries :
    (∀ edits (value : Value Symbol Guard) (before : SharedState width Symbol Guard) result after,
      EditNode (width := width) emptyGuard conjoin clear top record originals edits value before result after → Entries clear top before after) ∧
    (∀ entries index (values : List (Value Symbol Guard)) (before : SharedState width Symbol Guard) results after,
      EditChildren (width := width) emptyGuard conjoin clear top record originals entries index values before results after → Entries clear top before after) ∧
    (∀ entries (edges : List (EdgeValue Symbol Guard)) (before : SharedState width Symbol Guard) results after,
      EditRows (width := width) emptyGuard conjoin clear top record originals entries edges before results after → Entries clear top before after) := by
  have leafCase : ∀ {target value before result after}, Leaf (width := width) emptyGuard conjoin clear top record originals target value before result after → Entries clear top before after :=
    fun trace => ⟨trace.extends, trace.produced⟩
  have emptyCase : ∀ {entries : List (Int × Edits EqualityNormalize.Path)} {state}, Entries clear top (state : SharedState width Symbol Guard) state := ⟨Cache.extends_refl _, id⟩
  have ordinaryCase : ∀ {entries edges before rebuilt middle value heap} {entry : Cache.Interned InternedBinderProtocol.NodeKey} {depth : Nat} {free : List InternedBinderProtocol.Reference},
      EditRows (width := width) emptyGuard conjoin clear top record originals entries edges before rebuilt middle →
      run (makeNode rebuilt) middle.native.machine.heap = (value, heap) → Entries clear top before middle → Entries clear top before (advanceHeap middle heap) := by
    intro entries edges before rebuilt middle value heap entry depth free _ _ kept
    exact kept.trans (advance_entries clear top _ _)
  have recursiveCase : ∀ {original exposed heap entries before result after},
      SourceEqualityRequiredGraph.Recursive original → SourceEqualityRequiredHead.Head original before.native.machine.heap exposed heap →
      EditNode (width := width) emptyGuard conjoin clear top record originals (.editBelow entries) exposed (advanceHeap before heap) result after →
      Entries clear top (advanceHeap before heap) after → Entries clear top before after := by
    intro original exposed heap entries before result after _ _ _ kept
    exact (advance_entries clear top _ _).trans kept
  have nilChildren : ∀ {entries : List (Int × Edits EqualityNormalize.Path)} {index : Nat} {state}, Entries clear top (state : SharedState width Symbol Guard) state := ⟨Cache.extends_refl _, id⟩
  have unselectedCase : ∀ {entries values before results after} {value : Value Symbol Guard} (index : Nat),
      SourceEqualityNeededMap.lookup (index : Int) entries = none →
      EditChildren (width := width) emptyGuard conjoin clear top record originals entries (index + 1) values before results after → Entries clear top before after → Entries clear top before after := by
    intro entries values before results after value index _ _ kept; exact kept
  have selectedCase : ∀ {entries edits value before result middle values results after} (index : Nat),
      SourceEqualityNeededMap.lookup (index : Int) entries = some edits →
      EditNode (width := width) emptyGuard conjoin clear top record originals edits value before result middle →
      EditChildren (width := width) emptyGuard conjoin clear top record originals entries (index + 1) values middle results after →
      Entries clear top before middle → Entries clear top middle after → Entries clear top before after := by
    intro entries edits value before result middle values results after index _ _ _ first rest; exact first.trans rest
  have nilRows : ∀ {entries : List (Int × Edits EqualityNormalize.Path)} {state}, Entries clear top (state : SharedState width Symbol Guard) state := ⟨Cache.extends_refl _, id⟩
  have consCase : ∀ {entries before values middle result heap edges results after} {edge : EdgeValue Symbol Guard},
      EditChildren (width := width) emptyGuard conjoin clear top record originals entries 0 edge.children before values middle →
      run (makeEdge edge.entry.key.symbol edge.entry.key.constraint values) middle.native.machine.heap = (result, heap) →
      EditRows (width := width) emptyGuard conjoin clear top record originals entries edges (advanceHeap middle heap) results after →
      Entries clear top before middle → Entries clear top (advanceHeap middle heap) after → Entries clear top before after := by
    intro entries before values middle result heap edges results after edge _ _ _ first rest
    exact first.trans ((advance_entries clear top _ _).trans rest)
  refine ⟨?_, ?_, ?_⟩
  · intro edits value before result after trace
    exact EditNode.rec (motive_1 := fun _ _ before _ after _ => Entries clear top before after)
      (motive_2 := fun _ _ _ before _ after _ => Entries clear top before after) (motive_3 := fun _ _ before _ after _ => Entries clear top before after)
      @leafCase @emptyCase @ordinaryCase @recursiveCase @nilChildren @unselectedCase @selectedCase @nilRows @consCase trace
  · intro entries index values before results after trace
    exact EditChildren.rec (motive_1 := fun _ _ before _ after _ => Entries clear top before after)
      (motive_2 := fun _ _ _ before _ after _ => Entries clear top before after) (motive_3 := fun _ _ before _ after _ => Entries clear top before after)
      @leafCase @emptyCase @ordinaryCase @recursiveCase @nilChildren @unselectedCase @selectedCase @nilRows @consCase trace
  · intro entries edges before results after trace
    exact EditRows.rec (motive_1 := fun _ _ before _ after _ => Entries clear top before after)
      (motive_2 := fun _ _ _ before _ after _ => Entries clear top before after) (motive_3 := fun _ _ before _ after _ => Entries clear top before after)
      @leafCase @emptyCase @ordinaryCase @recursiveCase @nilChildren @unselectedCase @selectedCase @nilRows @consCase trace

/-- Every completed node edit retains all earlier returned merge entries and their producers. -/
theorem node_entries {edits value before result after} (trace : EditNode (width := width) emptyGuard conjoin clear top record originals edits value before result after) : Entries clear top before after :=
  (all_entries emptyGuard conjoin clear top record originals).1 _ _ _ _ _ trace

/-- Every ordered child scan retains all earlier returned merge entries and their producers. -/
theorem children_entries {entries index values before results after}
    (trace : EditChildren (width := width) emptyGuard conjoin clear top record originals entries index values before results after) : Entries clear top before after :=
  (all_entries emptyGuard conjoin clear top record originals).2.1 _ _ _ _ _ _ trace

/-- Every ordered row scan retains all earlier returned merge entries and their producers. -/
theorem rows_entries {entries edges before results after}
    (trace : EditRows (width := width) emptyGuard conjoin clear top record originals entries edges before results after) : Entries clear top before after :=
  (all_entries emptyGuard conjoin clear top record originals).2.2 _ _ _ _ _ trace

end MicroCFTA.SourceCurrentMemoSharedEditRetention
