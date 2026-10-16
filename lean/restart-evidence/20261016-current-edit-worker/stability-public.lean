import MicroCFTA.SourceCurrentAllocatedSharedEditWorkerStability

#print axioms MicroCFTA.SourceCurrentAllocatedSharedTargetWorkerStability.force_done_stable
#print axioms MicroCFTA.SourceCurrentAllocatedSharedTargetWorkerStability.step_done_stable
#print axioms MicroCFTA.SourceCurrentAllocatedSharedTargetWorkerStability.leaf_done_stable
#print axioms MicroCFTA.SourceCurrentAllocatedSharedTargetWorkerStability.leaf_done_unique
#print axioms MicroCFTA.SourceCurrentAllocatedSharedEditWorkerStability.leaf_done_stable
#print axioms MicroCFTA.SourceCurrentAllocatedSharedEditWorkerStability.head_done_stable
#print axioms MicroCFTA.SourceCurrentAllocatedSharedEditWorkerStability.children_done_stable
#print axioms MicroCFTA.SourceCurrentAllocatedSharedEditWorkerStability.rows_done_stable
#print axioms MicroCFTA.SourceCurrentAllocatedSharedEditWorkerStability.edit_done_stable
#print axioms MicroCFTA.SourceCurrentAllocatedSharedEditWorkerStability.editList_done_stable
#print axioms MicroCFTA.SourceCurrentAllocatedSharedEditWorkerStability.editAll_done_stable
#print axioms MicroCFTA.SourceCurrentAllocatedSharedEditWorkerStability.edit_done_unique
#print axioms MicroCFTA.SourceCurrentAllocatedSharedEditWorkerStability.editList_done_unique
#print axioms MicroCFTA.SourceCurrentAllocatedSharedEditWorkerStability.editAll_done_unique
#print axioms MicroCFTA.SourceCurrentAllocatedSharedEditWorkerStability.children_edit_done_stable
#print axioms MicroCFTA.SourceCurrentAllocatedSharedEditWorkerStability.rows_edit_done_stable
#print axioms MicroCFTA.SourceCurrentAllocatedSharedEditWorkerStability.children_edit_done_unique
#print axioms MicroCFTA.SourceCurrentAllocatedSharedEditWorkerStability.rows_edit_done_unique
set_option pp.universes true in
#check @MicroCFTA.SourceCurrentAllocatedSharedTargetWorkerStability.force_done_stable
set_option pp.universes true in
#check @MicroCFTA.SourceCurrentAllocatedSharedTargetWorkerStability.step_done_stable
set_option pp.universes true in
#check @MicroCFTA.SourceCurrentAllocatedSharedTargetWorkerStability.leaf_done_stable
set_option pp.universes true in
#check @MicroCFTA.SourceCurrentAllocatedSharedTargetWorkerStability.leaf_done_unique
set_option pp.universes true in
#check @MicroCFTA.SourceCurrentAllocatedSharedEditWorkerStability.leaf_done_stable
set_option pp.universes true in
#check @MicroCFTA.SourceCurrentAllocatedSharedEditWorkerStability.head_done_stable
set_option pp.universes true in
#check @MicroCFTA.SourceCurrentAllocatedSharedEditWorkerStability.children_done_stable
set_option pp.universes true in
#check @MicroCFTA.SourceCurrentAllocatedSharedEditWorkerStability.rows_done_stable
set_option pp.universes true in
#check @MicroCFTA.SourceCurrentAllocatedSharedEditWorkerStability.edit_done_stable
set_option pp.universes true in
#check @MicroCFTA.SourceCurrentAllocatedSharedEditWorkerStability.editList_done_stable
set_option pp.universes true in
#check @MicroCFTA.SourceCurrentAllocatedSharedEditWorkerStability.editAll_done_stable
set_option pp.universes true in
#check @MicroCFTA.SourceCurrentAllocatedSharedEditWorkerStability.edit_done_unique
set_option pp.universes true in
#check @MicroCFTA.SourceCurrentAllocatedSharedEditWorkerStability.editList_done_unique
set_option pp.universes true in
#check @MicroCFTA.SourceCurrentAllocatedSharedEditWorkerStability.editAll_done_unique
set_option pp.universes true in
#check @MicroCFTA.SourceCurrentAllocatedSharedEditWorkerStability.children_edit_done_stable
set_option pp.universes true in
#check @MicroCFTA.SourceCurrentAllocatedSharedEditWorkerStability.rows_edit_done_stable
set_option pp.universes true in
#check @MicroCFTA.SourceCurrentAllocatedSharedEditWorkerStability.children_edit_done_unique
set_option pp.universes true in
#check @MicroCFTA.SourceCurrentAllocatedSharedEditWorkerStability.rows_edit_done_unique

namespace MicroCFTA.AllocatedEditStabilityChecks
open Cache InternedConstructorTemplates SourceEqualityEdits
open SourceCurrentAllocatedSharedEditGraph (SharedState advanceHeap)
open SourceCurrentAllocatedSharedEditWorker
open SourceCurrentAllocatedSharedEditWorkerStability
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Record" => SourceEqualityClassOrder.Record
variable {width : Nat} [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

-- Node-edit exhaustion does not become a success. Positive fuel admits an actual Empty branch.
example (record : Record) (originals : List (Value Symbol Guard)) (before : SharedState width) :
    edit record originals 0 0 0 0 0 0 (.editBelow []) .empty before = .failed (.exhausted .worker) before ∧
      edit record originals 1 0 0 0 0 0 (.editBelow []) .empty before = .done .empty before := ⟨rfl, rfl⟩

-- The child-list root leaf ignores every bound and retains the whole state.
example (record : Record) (originals values : List (Value Symbol Guard))
    (path : EqualityNormalize.Path) (before : SharedState width) (e p h m s n : Nat) :
    editList (edit record originals 0 0 0 0 0 0) (.editAt path) values before = .done values before ∧
      editList (edit record originals e p h m s n) (.editAt path) values before = .done values before := ⟨rfl, rfl⟩

-- A literal row performs raw makeEdge, then makeNode, at their actual returned heaps.
example (record : Record) (originals : List (Value Symbol Guard)) (before : SharedState width)
    (entry : Interned InternedBinderProtocol.NodeKey) (edgeEntry : Interned (EdgeKey Symbol Guard))
    (e p h m s n : Nat) (enough : 1 ≤ e) :
    let edgeResult := run (makeEdge edgeEntry.key.symbol edgeEntry.key.constraint []) before.checked.native.machine.heap
    let middle := advanceHeap before edgeResult.2
    let nodeResult := run (makeNode [edgeResult.1]) middle.checked.native.machine.heap
    edit record originals e p h m s n (.editBelow []) (.node entry [.mk edgeEntry []] 0 []) before =
      .done nodeResult.1 (advanceHeap middle nodeResult.2) := by
  dsimp only
  apply edit_done_stable (e := 1) (p := 0) (h := 0) (m := 0) (s := 0) (n := 0)
    (largerE := e) (largerP := p) (largerH := h) (largerM := m) (largerS := s) (largerN := n)
    (enoughE := enough) (enoughP := Nat.zero_le _) (enoughH := Nat.zero_le _)
    (enoughM := Nat.zero_le _) (enoughS := Nat.zero_le _) (enoughN := Nat.zero_le _)
  rfl

-- A ready target slot and literal native success derive stable edit success without physical laws.
example (record : Record) (originals : List (Value Symbol Guard)) (before : SharedState width)
    (path : EqualityNormalize.Path) (target input result : Value Symbol Guard)
    (checked : SourceEqualityNativeDemand.State width) (native e p h m s n : Nat)
    (present : before.targets path = some target) (enoughE : 1 ≤ e) (enoughN : native ≤ n)
    (done : SourceEqualityNativeDemand.execute native
      (.code (SourceRecursiveIntersectionCode.requestNode IntersectionEmptyDomain.emptyDomain target input)) before.checked =
        .done result checked) :
    edit record originals e p h m s n (.editAt path) input before =
      .done result (SourceCurrentAllocatedSharedTargetState.advance before checked) := by
  have first : edit record originals 1 0 0 0 0 native (.editAt path) input before =
      .done result (SourceCurrentAllocatedSharedTargetState.advance before checked) := by
    simp only [edit, leaf, lift, SourceCurrentAllocatedSharedTargetWorker.leaf,
      SourceCurrentAllocatedSharedTargetWorker.force_hit _ _ _ _ _ _ _ _ _ _ present,
      SourceCurrentAllocatedSharedTargetWorker.Outcome.bind, SourceCurrentAllocatedSharedTargetWorker.step, done]
  exact edit_done_stable first enoughE (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) enoughN

-- Cross-bound compiled success identifies operations, native tables, slots, and the merge memo.
example {record : Record} {originals values first second : List (Value Symbol Guard)}
    {edits : List (Path × EqualityNormalize.Path)} {before after later : SharedState width}
    {e p h m s n otherE otherP otherH otherM otherS otherN : Nat}
    (one : editAll record originals e p h m s n edits values before = .done first after)
    (two : editAll record originals otherE otherP otherH otherM otherS otherN edits values before = .done second later) :
    first = second ∧ after.checked.operations = later.checked.operations ∧
      after.checked.native = later.checked.native ∧ after.targets = later.targets ∧ after.memo = later.memo := by
  obtain ⟨same, states⟩ := editAll_done_unique one two
  cases states
  exact ⟨same, rfl, rfl, rfl, rfl⟩

end MicroCFTA.AllocatedEditStabilityChecks
