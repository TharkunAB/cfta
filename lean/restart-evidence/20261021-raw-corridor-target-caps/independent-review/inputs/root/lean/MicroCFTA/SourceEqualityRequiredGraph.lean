import MicroCFTA.SourceEqualityRequiredHead
import MicroCFTA.SourceEqualityNeededAdjustMeaning

/-!
# Physical successful call graphs for requireAll

Empty requirements return before node inspection. Nonempty ordinary requests
filter each row by its maximum required key before they visit any child.
Recursive requests first perform the actual row-head normalization. Child
positions retain the source signed-map lookup behavior. Edges and nodes use
the actual constructor requests and returned caches.

These are logical ordered call graphs. They do not claim a verified native
lazy evaluation schedule. A nonempty request at a bare reference has no
successful graph; the source reports an unresolved-reference error there.
-/
namespace MicroCFTA.SourceEqualityRequiredGraph
open InternedConstructorTemplates SourceEqualityNeeded
open SourceEqualityRequiredHead

/-- Only Mu and stored union heads need constructor-row exposure. -/
def Recursive : Value Symbol Guard → Prop
  | .mu .. | .union .. => True
  | _ => False

mutual
  /-- One physical required-node request, with exact source branch priority. -/
  inductive RequireNode [DecidableEq (EdgeKey Symbol Guard)] :
      Needed → Value Symbol Guard → State Symbol Guard → Value Symbol Guard → State Symbol Guard → Prop where
    | identity : RequireNode (.node []) value state value state
    | empty (nonempty : entries ≠ []) : RequireNode (.node entries) .empty state .empty state
    | ordinary (nonempty : entries ≠ [])
        (rows : RequireRows entries edges before rebuilt middle)
        (result : run (makeNode rebuilt) middle = (value, after)) :
        RequireNode (.node entries) (.node entry edges depth free) before value after
    | recursive (nonempty : entries ≠ []) (recursive : Recursive original)
        (head : Head original before exposed middle)
        (body : RequireNode (.node entries) exposed middle value after) :
        RequireNode (.node entries) original before value after

  /-- Visit existing child positions in their original list order. -/
  inductive RequireChildren [DecidableEq (EdgeKey Symbol Guard)] :
      List (Int × Needed) → Nat → List (Value Symbol Guard) → State Symbol Guard →
        List (Value Symbol Guard) → State Symbol Guard → Prop where
    | nil : RequireChildren entries index [] state [] state
    | unselected (index : Nat) (absent : SourceEqualityNeededMap.lookup (index : Int) entries = none)
        (rest : RequireChildren entries (index + 1) values before results after) :
        RequireChildren entries index (value :: values) before (value :: results) after
    | selected (index : Nat) (found : SourceEqualityNeededMap.lookup (index : Int) entries = some needed)
        (first : RequireNode needed value before result middle)
        (rest : RequireChildren entries (index + 1) values middle results after) :
        RequireChildren entries index (value :: values) before (result :: results) after

  /-- Reject an absent required index before child recursion and actual edge reconstruction. -/
  inductive RequireRows [DecidableEq (EdgeKey Symbol Guard)] :
      List (Int × Needed) → List (EdgeValue Symbol Guard) → State Symbol Guard →
        List (EdgeValue Symbol Guard) → State Symbol Guard → Prop where
    | nil : RequireRows entries [] state [] state
    | rejected (doesNotFit : fits (.node entries) edge.children.length = false)
        (rest : RequireRows entries edges before results after) :
        RequireRows entries (edge :: edges) before results after
    | kept (doesFit : fits (.node entries) edge.children.length = true)
        (children : RequireChildren entries 0 edge.children before values middle)
        (rebuilt : run (makeEdge edge.entry.key.symbol edge.entry.key.constraint values) middle = (result, afterEdge))
        (rest : RequireRows entries edges afterEdge results after) :
        RequireRows entries (edge :: edges) before (result :: results) after
end

/-- Child adjustment never changes the original list arity. -/
theorem RequireChildren.length [DecidableEq (EdgeKey Symbol Guard)]
    {entries : List (Int × Needed)} {index : Nat} {values results : List (Value Symbol Guard)}
    {before after : State Symbol Guard} (trace : RequireChildren entries index values before results after) :
    results.length = values.length := by
  refine RequireChildren.rec
    (motive_1 := fun _ _ _ _ _ _ => True)
    (motive_2 := fun _ _ original _ output _ _ => output.length = original.length)
    (motive_3 := fun _ _ _ _ _ _ => True)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ trace
  all_goals intros
  all_goals simp_all

end MicroCFTA.SourceEqualityRequiredGraph
