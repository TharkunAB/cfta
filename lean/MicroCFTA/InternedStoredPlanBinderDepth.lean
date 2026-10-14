import MicroCFTA.InternedStoredSubstitution
import MicroCFTA.InternedFreshOrdinaryActiveOrigins
import MicroCFTA.InternedFreshOrdinaryStoredSubstitution

/-!
# Binder depth in the actual stored substitution plan

Closed records become constant input slots. Only open stored Mu records
emit binder instructions. The executable record measure below is exactly
the maximum binder nesting in that prepared source plan. This theorem does
not assert a decrease during unfolding or finite cold-reader termination.
-/
namespace MicroCFTA.InternedStoredPlanBinderDepth
open InternedConstructorTemplates InternedStoredSubstitution
open InternedNestedConstruction (Syntax EdgeSyntax)
open InternedStoredShallowCompletion (BinderFree ManyBinderFree EdgesBinderFree)
open InternedBinderProtocol (Reference)

mutual
/-- Count maximum binder nesting in one source constructor plan. -/
def syntaxDepth : Syntax Symbol Guard → Nat
  | .empty | .var _ => 0
  | .node edges => syntaxEdgesDepth edges
  | .union members => syntaxManyDepth members
  | .binder _ body => 1 + syntaxDepth body
termination_by expression => sizeOf expression

/-- Ordered source child plans contribute their maximum binder depth. -/
def syntaxManyDepth : List (Syntax Symbol Guard) → Nat
  | [] => 0
  | first :: rest => max (syntaxDepth first) (syntaxManyDepth rest)
termination_by expressions => sizeOf expressions

/-- Edge labels do not change the maximum binder nesting of their children. -/
def syntaxEdgesDepth : List (EdgeSyntax Symbol Guard) → Nat
  | [] => 0
  | .mk _ _ children :: rest => max (syntaxManyDepth children) (syntaxEdgesDepth rest)
termination_by expressions => sizeOf expressions
end

mutual
/-- Count open stored binders while treating closed captured records as constants. -/
def valueDepth (value : Value Symbol Guard) : Nat :=
  if value.free.isEmpty then 0 else
  match value with
  | .empty | .reference _ => 0
  | .node _ edges .. => edgesDepth edges
  | .union _ members .. => manyDepth members
  | .mu _ body .. => 1 + valueDepth body
termination_by sizeOf value

/-- Original ordered value lists contribute their maximum open binder depth. -/
def manyDepth : List (Value Symbol Guard) → Nat
  | [] => 0
  | first :: rest => max (valueDepth first) (manyDepth rest)
termination_by values => sizeOf values

/-- Actual edge children determine the open binder depth of their stored plan. -/
def edgesDepth : List (EdgeValue Symbol Guard) → Nat
  | [] => 0
  | .mk _ children :: rest => max (manyDepth children) (edgesDepth rest)
termination_by edges => sizeOf edges
end

/-- Measure the actual body plan that one outer Mu unfolding executes. -/
def bodyDepth : Value Symbol Guard → Nat
  | .mu _ body .. => valueDepth body
  | _ => 0

mutual
/-- The actual stored compiler emits exactly the binder nesting counted from its original record. -/
theorem encode_depth (context : List (Value Symbol Guard)) (locals : List Reference) (value : Value Symbol Guard) :
    syntaxDepth (encode context locals value) = valueDepth value := by
  rw [encode.eq_def, valueDepth.eq_def]
  split
  · rw [syntaxDepth]
  · cases value with
    | empty => rw [syntaxDepth]
    | reference name =>
        dsimp only
        split <;> rw [syntaxDepth]
    | node entry edges depth free => rw [syntaxDepth]; exact encodeEdges_depth context locals edges
    | union entry members depth free => rw [syntaxDepth]; exact encodeMany_depth context locals members
    | mu entry body depth ordinary =>
        rw [syntaxDepth, encode_depth context (.interned entry.identity :: locals) body]
termination_by sizeOf value

/-- The compiler retains the maximum binder depth of the exact ordered original members. -/
theorem encodeMany_depth (context : List (Value Symbol Guard)) (locals : List Reference) (values : List (Value Symbol Guard)) :
    syntaxManyDepth (encodeMany context locals values) = manyDepth values := by
  cases values with
  | nil => rw [encodeMany, syntaxManyDepth, manyDepth]
  | cons first rest =>
      rw [encodeMany, syntaxManyDepth, manyDepth, encode_depth context locals first, encodeMany_depth context locals rest]
termination_by sizeOf values

/-- The compiler retains binder nesting through every actual edge and child position. -/
theorem encodeEdges_depth (context : List (Value Symbol Guard)) (locals : List Reference) (edges : List (EdgeValue Symbol Guard)) :
    syntaxEdgesDepth (encodeEdges context locals edges) = edgesDepth edges := by
  cases edges with
  | nil => rw [encodeEdges, syntaxEdgesDepth, edgesDepth]
  | cons first rest =>
      cases first with
      | mk entry children =>
          rw [encodeEdges, syntaxEdgesDepth, edgesDepth, encodeMany_depth context locals children,
            encodeEdges_depth context locals rest]
termination_by sizeOf edges
end

/-- Closed captured records emit no binder instruction and have measure zero. -/
theorem closed_zero (value : Value Symbol Guard) (closed : value.free = []) : valueDepth value = 0 := by
  rw [valueDepth.eq_def, closed]
  rfl

mutual
/-- Zero source-plan binder depth is exactly the absence of binder instructions. -/
theorem syntax_zero (expression : Syntax Symbol Guard) : syntaxDepth expression = 0 ↔ BinderFree expression := by
  cases expression with
  | empty | var => simp [syntaxDepth, BinderFree]
  | binder => simp [syntaxDepth, BinderFree]
  | node edges => rw [syntaxDepth, BinderFree]; exact syntaxEdges_zero edges
  | union members => rw [syntaxDepth, BinderFree]; exact syntaxMany_zero members
termination_by sizeOf expression

/-- Zero depth in an ordered child plan is exactly binder-free execution of every child. -/
theorem syntaxMany_zero (expressions : List (Syntax Symbol Guard)) :
    syntaxManyDepth expressions = 0 ↔ ManyBinderFree expressions := by
  cases expressions with
  | nil => simp [syntaxManyDepth, ManyBinderFree]
  | cons first rest =>
      rw [syntaxManyDepth, ManyBinderFree, Nat.max_eq_zero_iff, syntax_zero first, syntaxMany_zero rest]
termination_by sizeOf expressions

/-- Zero edge-plan depth is exactly the absence of binders in every ordered child plan. -/
theorem syntaxEdges_zero (expressions : List (EdgeSyntax Symbol Guard)) :
    syntaxEdgesDepth expressions = 0 ↔ EdgesBinderFree expressions := by
  cases expressions with
  | nil => simp [syntaxEdgesDepth, EdgesBinderFree]
  | cons first rest =>
      cases first with
      | mk symbol guard children =>
          rw [syntaxEdgesDepth, EdgesBinderFree, Nat.max_eq_zero_iff, syntaxMany_zero children, syntaxEdges_zero rest]
termination_by sizeOf expressions
end

/-- An actual repaired stored plan of depth zero cannot add a complete Mu record. -/
theorem execute_zero_noNewMu [DecidableEq (EdgeKey Symbol Guard)] (value : Value Symbol Guard)
    (environment : Environment Symbol Guard) (state : State Symbol Guard) (zero : valueDepth value = 0) :
    InternedShallowHeap.NoNewMu state (InternedFreshOrdinaryStoredSubstitution.execute value environment state).state := by
  have free := (syntax_zero (encode (leaves value) [] value)).mp ((encode_depth (leaves value) [] value).trans zero)
  unfold InternedFreshOrdinaryStoredSubstitution.execute
  rw [InternedFreshOrdinaryStoredSubstitution.build_eq _ _ state free]
  exact InternedShallowHeap.build_noNewMu _ _ state free

/-- The zero case of actual repaired outer unfolding retains every complete Mu from the initial cache. -/
theorem unfold_zero_noNewMu [DecidableEq (EdgeKey Symbol Guard)] (value : Value Symbol Guard)
    (state : State Symbol Guard) (zero : bodyDepth value = 0) :
    InternedShallowHeap.NoNewMu state (InternedFreshOrdinaryStoredSubstitution.unfold value state).state := by
  cases value with
  | empty | reference | node | union => exact InternedShallowHeap.noNewMu_refl state
  | mu => exact execute_zero_noNewMu _ _ state zero

/-- Every selected source child has at most the maximum binder depth of its ordered list. -/
theorem many_member (expressions : List (Syntax Symbol Guard)) (expression : Syntax Symbol Guard)
    (member : expression ∈ expressions) : syntaxDepth expression ≤ syntaxManyDepth expressions := by
  induction expressions with
  | nil => cases member
  | cons first rest ih =>
      rw [syntaxManyDepth]
      rcases List.mem_cons.mp member with rfl | included
      · exact Nat.le_max_left _ _
      · exact Nat.le_trans (ih included) (Nat.le_max_right _ _)

/-- Every selected source edge has at most the maximum binder depth of its original edge list. -/
theorem edge_member (edges : List (EdgeSyntax Symbol Guard)) (symbol : Symbol) (guard : Guard)
    (children : List (Syntax Symbol Guard)) (member : .mk symbol guard children ∈ edges) :
    syntaxManyDepth children ≤ syntaxEdgesDepth edges := by
  induction edges with
  | nil => cases member
  | cons first rest ih =>
      cases first with
      | mk firstSymbol firstGuard firstChildren =>
          rw [syntaxEdgesDepth]
          rcases List.mem_cons.mp member with same | included
          · cases same
            exact Nat.le_max_left _ _
          · exact Nat.le_trans (ih included) (Nat.le_max_right _ _)

end MicroCFTA.InternedStoredPlanBinderDepth

namespace MicroCFTA.InternedFreshOrdinaryActiveOrigins
open InternedConstructorTemplates
open InternedNestedConstruction (Syntax)
open InternedStoredPlanBinderDepth

/-- Actual source callback crossings consume the original plan's binder-depth budget. -/
theorem Path.plan_depth_bound [DecidableEq (EdgeKey Symbol Guard)]
    {root expression : Syntax Symbol Guard} {initial environment : List (Value Symbol Guard)}
    {crossings : List (Crossing Symbol Guard)} (path : Path root initial expression environment crossings) :
    syntaxDepth expression + crossings.length ≤ syntaxDepth root := by
  induction path with
  | here => simp
  | node edge child nested ih =>
      rw [syntaxDepth]
      exact Nat.le_trans ih (Nat.le_trans (many_member _ _ child) (edge_member _ _ _ _ edge))
  | union child nested ih =>
      rw [syntaxDepth]
      exact Nat.le_trans ih (many_member _ _ child)
  | binder crossing nested ih =>
      rw [syntaxDepth, List.length_append, List.length_singleton]
      omega

end MicroCFTA.InternedFreshOrdinaryActiveOrigins
