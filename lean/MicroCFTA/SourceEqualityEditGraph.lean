import MicroCFTA.SourceEqualityEdits
import MicroCFTA.SourceEqualityRequiredWorkerSound

/-!
# Physical successful call graphs for simultaneous edits

A leaf executes its actual callback before node inspection. A child-list
leaf executes no callback. Non-leaf recursive nodes expose constructor rows.
Every ordinary row is rebuilt with its original symbol and complete guard.
Callbacks retain their actual result equation, including the returned cache.
-/
namespace MicroCFTA.SourceEqualityEditGraph
open InternedConstructorTemplates SourceEqualityEdits SourceEqualityRequiredHead
open SourceEqualityRequiredWorker (Result)

/-- The supplied operation executes one source edit callback with explicit failure outcomes. -/
abbrev Callback (Action Symbol Guard : Type) :=
  Action → Value Symbol Guard → State Symbol Guard → Result Symbol Guard (Value Symbol Guard)

mutual
  /-- One actual node edit follows source callback and node branch priority. -/
  inductive EditNode [DecidableEq (EdgeKey Symbol Guard)] (call : Callback Action Symbol Guard) :
      Edits Action → Value Symbol Guard → State Symbol Guard → Value Symbol Guard → State Symbol Guard → Prop where
    | leaf (actual : call action value before = .done result after) :
        EditNode call (.editAt action) value before result after
    | empty : EditNode call (.editBelow entries) .empty state .empty state
    | ordinary (rows : EditRows call entries edges before rebuilt middle)
        (result : run (makeNode rebuilt) middle = (value, after)) :
        EditNode call (.editBelow entries) (.node entry edges depth free) before value after
    | recursive (recursive : SourceEqualityRequiredGraph.Recursive original)
        (head : Head original before exposed middle)
        (body : EditNode call (.editBelow entries) exposed middle value after) :
        EditNode call (.editBelow entries) original before value after

  /-- Visit existing child positions and execute only their selected edit subtree. -/
  inductive EditChildren [DecidableEq (EdgeKey Symbol Guard)] (call : Callback Action Symbol Guard) :
      List (Int × Edits Action) → Nat → List (Value Symbol Guard) → State Symbol Guard →
        List (Value Symbol Guard) → State Symbol Guard → Prop where
    | nil : EditChildren call entries index [] state [] state
    | unselected (index : Nat) (absent : SourceEqualityNeededMap.lookup (index : Int) entries = none)
        (rest : EditChildren call entries (index + 1) values before results after) :
        EditChildren call entries index (value :: values) before (value :: results) after
    | selected (index : Nat) (found : SourceEqualityNeededMap.lookup (index : Int) entries = some edits)
        (first : EditNode call edits value before result middle)
        (rest : EditChildren call entries (index + 1) values middle results after) :
        EditChildren call entries index (value :: values) before (result :: results) after

  /-- Rebuild all original alternatives without a required-path arity rejection. -/
  inductive EditRows [DecidableEq (EdgeKey Symbol Guard)] (call : Callback Action Symbol Guard) :
      List (Int × Edits Action) → List (EdgeValue Symbol Guard) → State Symbol Guard →
        List (EdgeValue Symbol Guard) → State Symbol Guard → Prop where
    | nil : EditRows call entries [] state [] state
    | cons (children : EditChildren call entries 0 edge.children before values middle)
        (rebuilt : run (makeEdge edge.entry.key.symbol edge.entry.key.constraint values) middle = (result, afterEdge))
        (rest : EditRows call entries edges afterEdge results after) :
        EditRows call entries (edge :: edges) before (result :: results) after
end

/-- A source child-list leaf is ignored; a below-node executes its signed child map. -/
inductive EditList [DecidableEq (EdgeKey Symbol Guard)] (call : Callback Action Symbol Guard) :
    Edits Action → List (Value Symbol Guard) → State Symbol Guard →
      List (Value Symbol Guard) → State Symbol Guard → Prop where
  | leaf : EditList call (.editAt action) values state values state
  | children (trace : EditChildren call entries 0 values before results after) :
      EditList call (.editBelow entries) values before results after

/-- Simultaneous child edits preserve every original position. -/
theorem EditChildren.length [DecidableEq (EdgeKey Symbol Guard)]
    {call : Callback Action Symbol Guard} {entries index values before results after}
    (trace : EditChildren call entries index values before results after) : results.length = values.length := by
  refine EditChildren.rec
    (motive_1 := fun _ _ _ _ _ _ => True)
    (motive_2 := fun _ _ original _ output _ _ => output.length = original.length)
    (motive_3 := fun _ _ _ _ _ _ => True)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ trace
  all_goals intros
  all_goals simp_all

end MicroCFTA.SourceEqualityEditGraph
