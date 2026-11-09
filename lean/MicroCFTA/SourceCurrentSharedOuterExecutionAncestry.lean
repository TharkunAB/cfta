import MicroCFTA.SourceCurrentAllocatedSharedPartialWorker
import MicroCFTA.SourceCurrentOuterCopiedWarmHit

/-!
# Literal unfinished prefixes of the shared outer worker

The phase type contains only the remaining fuel and current caller data.
Each new transition uses the actual shared worker. A sibling starts only
after the preceding call returns at that exact caller. No old execution
relation, resource receipt or completed whole-call result is an input.

These relations describe finite prefixes. This module does not extract a
prefix from every failed execution or exclude busy requests.
-/
namespace MicroCFTA.SourceCurrentSharedOuterExecutionAncestry
open InternedConstructorTemplates SourceCurrentAllocatedPartialState
open SourceCurrentAllocatedSharedPartialWorker
open SourceCurrentOuterCopiedWarmHit (Phase)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Edge" => EdgeValue Symbol Guard
local notation "Caller" => SourceCurrentAllocatedPartialState.State
variable {width : Nat}

/-- Every literal phase retains its complete current caller. -/
def caller : Phase width → Caller width
  | .node _ _ before | .body _ _ before => before
  | .rows _ _ _ before | .descendants _ _ _ before | .children _ _ _ before => before
  | .walk _ _ _ _ before => before

variable [DecidableEq Symbol]
  [DecidableEq (InternedConstructorTemplates.EdgeKey Symbol Guard)] [DecidableEq Node]

/-- A prefix enters a literal branch or skips only completed earlier calls. -/
inductive Step (g s r e p h m c n budget : Nat) : Phase width → Phase width → Prop where
  /-- A node enters its exact stored owner after demand. -/
  | node_evaluate (actual : beginNode request before = (handle, .evaluate original, running)) :
      Step g s r e p h m c n budget (.node fuel request before) (.body fuel original running)
  /-- An ordinary body enters its original rows. -/
  | body_rows (actual : request.value = .node entry originals depth free) :
      Step g s r e p h m c n budget (.body (fuel + 1) request before)
        (.rows fuel request.inherited originals before)
  /-- A completed parent edge precedes its actual descendants. -/
  | rows_edge
      (actual : edgeCall fuel g s r e p h m c n budget ⟨inherited, original⟩ before = .done narrowed middle) :
      Step g s r e p h m c n budget (.rows (fuel + 1) inherited (original :: rest) before)
        (.descendants fuel inherited narrowed middle)
  /-- The row suffix starts after the exact completed parent and descendants. -/
  | rows_tail
      (edge : edgeCall fuel g s r e p h m c n budget ⟨inherited, original⟩ before = .done narrowed middle)
      (children : descendants fuel g s r e p h m c n budget inherited narrowed middle = .done result after) :
      Step g s r e p h m c n budget (.rows (fuel + 1) inherited (original :: rest) before)
        (.rows fuel inherited rest after)
  /-- The inherited prefix enters the exact returned children. -/
  | descendants_children {edge : Edge}
      (actual : (SourceCurrentAllocatedInheritedPrefix.run edge.entry.key.constraint inherited
        before.checked.operations).1 = .ok (some combined)) :
      Step g s r e p h m c n budget (.descendants fuel inherited edge before)
        (.children fuel combined edge.children (SourceCurrentAllocatedSharedPartialGraph.prefixState before edge inherited))
  /-- A live combined payload enters its indexed walk. -/
  | children_walk (live : combined ≠ .contradiction) :
      Step g s r e p h m c n budget (.children fuel combined values before) (.walk fuel combined 0 values before)
  /-- The next node uses the actual indexed descent. -/
  | walk_head :
      Step g s r e p h m c n budget (.walk (fuel + 1) combined index (value :: rest) before)
        (.node fuel ⟨(SourceCurrentAllocatedSharedPartialGraph.descend before combined index).1, value⟩
          (SourceCurrentAllocatedSharedPartialGraph.descend before combined index).2)
  /-- The next slot starts after the actual completed earlier node. -/
  | walk_tail
      (actual : nodeCall fuel g s r e p h m c n budget
        ⟨(SourceCurrentAllocatedSharedPartialGraph.descend before combined index).1, value⟩
        (SourceCurrentAllocatedSharedPartialGraph.descend before combined index).2 = .done result middle) :
      Step g s r e p h m c n budget (.walk (fuel + 1) combined index (value :: rest) before)
        (.walk fuel combined (index + 1) rest middle)

/-- A finite literal prefix retains every completed earlier-call witness. -/
inductive Reached (g s r e p h m c n budget : Nat) : Phase width → Phase width → Prop where
  /-- The entry phase is already reached. -/
  | refl (phase) : Reached g s r e p h m c n budget phase phase
  /-- An actual branch extends the preceding prefix. -/
  | snoc (earlier : Reached g s r e p h m c n budget first middle)
      (last : Step g s r e p h m c n budget middle final) :
      Reached g s r e p h m c n budget first final

/-- Consecutive actual prefixes form one prefix. -/
theorem Reached.trans (first : Reached g s r e p h m c n budget entryPhase middle)
    (last : Reached g s r e p h m c n budget middle final) :
    Reached g s r e p h m c n budget entryPhase final := by
  induction last with
  | refl => exact first
  | snoc earlier last ih => exact .snoc ih last

end MicroCFTA.SourceCurrentSharedOuterExecutionAncestry
