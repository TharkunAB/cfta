import MicroCFTA.InternedNormalizedPreparedSites
import MicroCFTA.InternedRetainedCompletion

/-!
# One source grammar combines retained and normalized erased dependencies

Retained binders use their declared enclosing-reference edges. Subprograms
can read enclosing inputs and erase them below nested constructors. Actual
earlier depth traces prepare those source calls before each reservation.
-/
namespace MicroCFTA.InternedNormalizedCombinedConstruction
open InternedConstructorTemplates InternedNestedConstruction InternedNormalizedPreparedSites InternedNestedTraceSites
open InternedRetainedConstruction (Declared)

mutual
/-- Source syntax combines retained binders with subprograms whose enclosing dependencies normalize away. -/
def Combined (depth : Nat) (expression : Syntax Symbol Guard) : Prop := Leaf expression ∨
  match expression with
  | .empty | .var _ => True
  | .node edges => EdgesCombined depth edges
  | .union members => ManyCombined depth members
  | .binder _ body => match body with
    | .node edges => Declared depth edges ∧ EdgesCombined (depth + 1) edges
    | _ => False
termination_by sizeOf expression

/-- Every source child uses the same combined completion rules. -/
def ManyCombined (depth : Nat) : List (Syntax Symbol Guard) → Prop
  | [] => True
  | first :: rest => Combined depth first ∧ ManyCombined depth rest
termination_by expressions => sizeOf expressions

/-- Every edge keeps its actual ordered child requirements. -/
def EdgesCombined (depth : Nat) : List (EdgeSyntax Symbol Guard) → Prop
  | [] => True
  | .mk _ _ children :: rest => ManyCombined depth children ∧ EdgesCombined depth rest
termination_by expressions => sizeOf expressions
end

/-- A completed source trace prepares each source site below the current child list. -/
def ManyReady [DecidableEq (EdgeKey Symbol Guard)] (expressions : List (Syntax Symbol Guard))
    (state : State Symbol Guard) : Prop := ∀ expression ∈ expressions, Ready expression state

/-- A completed source trace prepares each source site below every current edge child. -/
def EdgesReady [DecidableEq (EdgeKey Symbol Guard)] (expressions : List (EdgeSyntax Symbol Guard))
    (state : State Symbol Guard) : Prop :=
  ∀ symbol constraint children, .mk symbol constraint children ∈ expressions → ManyReady children state

/-- Node child preparation comes from exact declared positions in the earlier source trace. -/
theorem ready_node [DecidableEq (EdgeKey Symbol Guard)] {edges : List (EdgeSyntax Symbol Guard)} {state : State Symbol Guard}
    (ready : Ready (.node edges) state) : EdgesReady edges state := by
  intro symbol constraint children edge child member
  exact ready.descendant (.node edge member (.here child))

/-- Union child preparation comes from the same exact earlier source trace. -/
theorem ready_union [DecidableEq (EdgeKey Symbol Guard)] {members : List (Syntax Symbol Guard)} {state : State Symbol Guard}
    (ready : Ready (.union members) state) : ManyReady members state :=
  fun child member => ready.descendant (.union member (.here child))

/-- Later completed source effects retain every prepared child request. -/
theorem ManyReady.grows [DecidableEq (EdgeKey Symbol Guard)] {expressions : List (Syntax Symbol Guard)}
    {before after : State Symbol Guard} (ready : ManyReady expressions before)
    (growth : Grows before after) : ManyReady expressions after :=
  fun expression member => (ready expression member).grows growth

/-- Later edge and child effects retain each earlier prepared request below the remaining edges. -/
theorem EdgesReady.grows [DecidableEq (EdgeKey Symbol Guard)] {expressions : List (EdgeSyntax Symbol Guard)}
    {before after : State Symbol Guard} (ready : EdgesReady expressions before)
    (growth : Grows before after) : EdgesReady expressions after :=
  fun symbol constraint children member => (ready symbol constraint children member).grows growth

end MicroCFTA.InternedNormalizedCombinedConstruction
