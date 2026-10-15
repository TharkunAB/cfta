import MicroCFTA.SourceMergedAPI
import MicroCFTA.SourceMergedExamples

/-!
# Kernel check for allocating general merge completion

Five source rows invoke actual repaired recursive-cover comparisons.
The first demanded read allocates a closed nested Mu. The retained column
keeps its recursive boundary. Larger bounds retain the exact final cache.
-/
namespace MicroCFTA.SourceMergedCompletionExamples
open InternedConstructorTemplates InternedNestedConstruction

/-- One recursive and four ordinary operands form the actual large source group. -/
def expression : Syntax Nat Unit := .node [
  .mk 7 () [SourceMergedExamples.nested],
  .mk 7 () [.node [.mk 2 () []]],
  .mk 7 () [.node [.mk 3 () []]],
  .mk 7 () [.node [.mk 4 () []]],
  .mk 7 () [.node [.mk 5 () []]]]

/-- Observe actual allocation, the retained union, and identical complete results at larger bounds. -/
def Completed : Outcome Nat Unit (Value Nat Unit) → Prop
  | .pending .. => False
  | .done value before =>
      match SourceMergedWorker.execute (fun _ => true) () 8 value before with
      | .failed .. => False
      | .done result after =>
          before.nodes.next < after.nodes.next ∧
          (match result with
          | .node _ [edge] _ [] => match edge.children with
            | [.union _ members _ []] => members.length = 5
            | _ => False
          | _ => False) ∧
          SourceMergedWorker.worker MergedSourceGrouping.groups (fun _ => true) ()
            (MergedOrdinaryHeight.height value + 3) 12 value before = .done result after

/-- The actual large general merge completes, allocates Mu, retains its union boundary, and has exact larger-bound stability. -/
theorem allocating_large_group : Completed (InternedFreshOrdinaryConstruction.build expression [] empty) := by
  set_option maxRecDepth 20000 in
  set_option cbv.maxSteps 30000000 in cbv

end MicroCFTA.SourceMergedCompletionExamples
