import MicroCFTA.SourceEqualityNativeDemandControl

/-!
# Complete native mismatch demand

A demanded edge with unequal input arities returns the actual sentinel.
The execution retains its original completion handle, empty-field equality
allocation, and exact edge heap. No original field lookup or child request
occurs. A fresh publication supplies the demanded original request.
-/
namespace MicroCFTA.SourceEqualityNativeDemand
open Cache InternedConstructorTemplates SourceRecursiveIntersectionCode SourceRecursiveIntersectionThunks
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula

/-- A started mismatched edge completes through its original native handle and actual sentinel heap. -/
theorem mismatch_complete [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (request : EdgeRequest Symbol Guard) (state : State width)
    (mismatch : request.left.children.length ≠ request.right.children.length)
    (started : (demandEdge (lookupEdge width request state.native).1 (lookupEdge width request state.native).2).1 = .evaluate request) :
    let selected := lookupEdge width request state.native
    let current := (demandEdge selected.1 selected.2).2
    let built := InternedConstructorTemplates.run
      (makeEdge request.left.entry.key.symbol SourceEqualityConstraintConstructors.top [.empty]) current.machine.heap
    execute 5 (.code (.edge request .pure)) state =
      .done built.1 ⟨SourceRecursiveIntersectionThunks.finishEdge selected.1 built.1
        (advance current {current.machine with heap := built.2}), SourceEqualityMkEdgeAllocation.emptyField state.operations⟩ := by
  simp only [execute, step, started, body_mismatch request _ _ mismatch]
  rfl

/-- A fresh actual edge publication starts its captured original request without an answer premise. -/
theorem edge_miss_starts (request : EdgeRequest Symbol Guard) (state : State width)
    (missing : state.native.edges.table
      (SourceRecursiveIntersectionEdgeMemo.requestKey width request.domain request.left request.right) = none) :
    (demandEdge (lookupEdge width request state.native).1 (lookupEdge width request state.native).2).1 = .evaluate request := by
  simp [lookupEdge, FlatMemoThunk.lookupOrInsert, missing, demandEdge, FlatMemoThunk.demand, Cache.put]

/-- Every fresh mismatched native request completes after the actual publication and constructor effects. -/
theorem mismatch_miss_complete [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (request : EdgeRequest Symbol Guard) (state : State width)
    (mismatch : request.left.children.length ≠ request.right.children.length)
    (missing : state.native.edges.table
      (SourceRecursiveIntersectionEdgeMemo.requestKey width request.domain request.left request.right) = none) :
    let selected := lookupEdge width request state.native
    let current := (demandEdge selected.1 selected.2).2
    let built := InternedConstructorTemplates.run
      (makeEdge request.left.entry.key.symbol SourceEqualityConstraintConstructors.top [.empty]) current.machine.heap
    execute 5 (.code (.edge request .pure)) state =
      .done built.1 ⟨SourceRecursiveIntersectionThunks.finishEdge selected.1 built.1
        (advance current {current.machine with heap := built.2}), SourceEqualityMkEdgeAllocation.emptyField state.operations⟩ :=
  mismatch_complete request state mismatch (edge_miss_starts request state missing)

end MicroCFTA.SourceEqualityNativeDemand
