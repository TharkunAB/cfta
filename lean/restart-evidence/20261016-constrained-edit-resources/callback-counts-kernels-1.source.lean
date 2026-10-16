import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryEditCallbackCounts

namespace MicroCFTA.EditCallbackCountKernels
open Cache InternedConstructorTemplates SourceEqualityEdits
open SourceCurrentAllocatedSharedEditGraph
open SourceCurrentAllocatedFiniteOrdinaryEditCallbackCounts
open SourceCurrentAllocatedFiniteOrdinaryNativeProfile
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Leaf" => SourceCurrentAllocatedSharedTargetLeaf.Leaf
local notation "EdgeCount" => SourceCurrentAllocatedFiniteOrdinaryOccurrenceBounds.edgeCount
local notation "Positions" => SourceCurrentAllocatedFiniteOrdinaryValuePositions.node
local notation "RowPositions" => SourceCurrentAllocatedFiniteOrdinaryValuePositions.rows
local notation "ChildPositions" => SourceCurrentAllocatedFiniteOrdinaryValuePositions.children
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}

theorem ignored_branches (record : SourceEqualityClassOrder.Record) (originals : List (Value Symbol Guard))
    (entries : List (Int × Edits EqualityNormalize.Path)) (path : EqualityNormalize.Path) (state : SharedState width) :
    NodeCount (.empty (record := record) (originals := originals) (entries := entries) (state := state)) 0 ∧
      0 ≤ Positions (.empty : Value Symbol Guard) ∧
      ListCount (.leaf (record := record) (originals := originals) (target := path)
        (values := [.empty, .empty]) (state := state)) 0 ∧
      0 ≤ ChildPositions ([.empty, .empty] : List (Value Symbol Guard)) := by
  have first : NodeCount (.empty (record := record) (originals := originals) (entries := entries) (state := state)) 0 := .empty
  have last : ListCount (.leaf (record := record) (originals := originals) (target := path)
      (values := [.empty, .empty]) (state := state)) 0 := .leaf
  exact ⟨first, first.bound .empty, last, last.bound (.cons .empty (.cons .empty .nil))⟩

theorem empty_leaf {record originals path result} {before after : SharedState width}
    (actual : Leaf record originals path .empty before result after) :
    NodeCount (.leaf actual) 1 ∧ 1 ≤ 1 + 0 * EdgeCount 0 0 0 := by
  have own : NodeCount (.leaf actual) 1 := .leaf actual
  exact ⟨own, own.profile 0 0 0 (by trivial) (by rfl)⟩

theorem repeated_empty_positions {record originals path firstResult lastResult}
    {before middle after : SharedState width}
    (first : Leaf record originals path .empty before firstResult middle)
    (last : Leaf record originals path .empty middle lastResult after) :
    let entries : List (Int × Edits EqualityNormalize.Path) := [(0, .editAt path), (1, .editAt path)]
    ∃ actual : EditList record originals (.editBelow entries) [.empty, .empty] before [firstResult, lastResult] after,
      ListCount actual 2 ∧ 2 ≤ 2 * (1 + 0 * EdgeCount 0 0 0) := by
  intro entries
  have foundFirst : SourceEqualityNeededMap.lookup (0 : Int) entries = some (.editAt path) := rfl
  have foundLast : SourceEqualityNeededMap.lookup (1 : Int) entries = some (.editAt path) := rfl
  let tail : EditChildren record originals entries 1 [.empty] middle [lastResult] after :=
    .selected 1 foundLast (.leaf last) .nil
  let actual : EditList record originals (.editBelow entries) [.empty, .empty] before [firstResult, lastResult] after :=
    .children (.selected 0 foundFirst (.leaf first) tail)
  have tailCount : ChildrenCount tail 1 := .selected (found := foundLast) (.leaf last) .nil
  have own : ListCount actual 2 := .children (.selected (found := foundFirst) (.leaf first) tailCount)
  have profile : ChildrenShape 0 0 ([.empty, .empty] : List (Value Symbol Guard)) := by
    simp [ChildrenShape, NodeShape]
  exact ⟨actual, own, own.profile 0 0 2 0 profile (by rfl)
    (by simp [MergedOrdinaryHeight.childrenHeight, MergedOrdinaryHeight.height])⟩

theorem repeated_rows {record originals path firstResult lastResult}
    (rowEntry : Interned (EdgeKey Symbol Guard)) {before middle afterLeaf : SharedState width}
    (first : Leaf record originals path .empty before firstResult middle)
    (last : Leaf record originals path .empty
      (advanceHeap middle (run (makeEdge rowEntry.key.symbol rowEntry.key.constraint [firstResult])
        middle.checked.native.machine.heap).2) lastResult afterLeaf) :
    let row : EdgeValue Symbol Guard := .mk rowEntry [.empty]
    let firstBuilt := run (makeEdge rowEntry.key.symbol rowEntry.key.constraint [firstResult]) middle.checked.native.machine.heap
    let next := advanceHeap middle firstBuilt.2
    let lastBuilt := run (makeEdge rowEntry.key.symbol rowEntry.key.constraint [lastResult]) afterLeaf.checked.native.machine.heap
    let after := advanceHeap afterLeaf lastBuilt.2
    ∃ actual : EditRows record originals [(0, .editAt path)] [row, row] before [firstBuilt.1, lastBuilt.1] after,
      RowsCount actual 2 ∧ 2 ≤ RowPositions [row, row] := by
  intro row firstBuilt next lastBuilt after
  have found : SourceEqualityNeededMap.lookup (0 : Int) [(0, .editAt path)] = some (.editAt path) := rfl
  let headChildren : EditChildren record originals [(0, .editAt path)] 0 [.empty] before [firstResult] middle :=
    .selected 0 found (.leaf first) .nil
  let tailChildren : EditChildren record originals [(0, .editAt path)] 0 [.empty] next [lastResult] afterLeaf :=
    .selected 0 found (.leaf last) .nil
  let tailRows : EditRows record originals [(0, .editAt path)] [row] next [lastBuilt.1] after :=
    .cons tailChildren rfl .nil
  let actual : EditRows record originals [(0, .editAt path)] [row, row] before [firstBuilt.1, lastBuilt.1] after :=
    .cons headChildren rfl tailRows
  have headCount : ChildrenCount headChildren 1 := .selected (found := found) (.leaf first) .nil
  have tailCount : ChildrenCount tailChildren 1 := .selected (found := found) (.leaf last) .nil
  have restCount : RowsCount tailRows 1 := .cons (rebuilt := rfl) tailCount .nil
  have own : RowsCount actual 2 := .cons (rebuilt := rfl) headCount restCount
  exact ⟨actual, own, own.bound (.cons (.cons .empty .nil) (.cons (.cons .empty .nil) .nil))⟩

#check ignored_branches
#print axioms ignored_branches
#check empty_leaf
#print axioms empty_leaf
#check repeated_empty_positions
#print axioms repeated_empty_positions
#check repeated_rows
#print axioms repeated_rows

end MicroCFTA.EditCallbackCountKernels
