import MicroCFTA.InternedSelectivePreparedSites

/-!
# Requests retain older ancestors and may erase their immediate parent

Each binder directly retains all older lexical inputs. It either retains
its immediate parent too, or declares structural erasure of that one slot.
The rest of its source body follows the same rules recursively.
-/
namespace MicroCFTA.InternedSelectiveConstruction
open InternedConstructorTemplates InternedNestedConstruction InternedRecordCoherence
open InternedNestedTraceSites InternedSelectivePreparedSites InternedErasureSyntax
open InternedRetainedConstruction (Frame Active)

/-- Direct unary source edges retain all older inputs and optionally the nearest parent. -/
def Declared (depth : Nat) (keepHead : Bool) (edges : List (EdgeSyntax Symbol Guard)) : Prop :=
  ∀ index < depth, keepHead = true ∨ 0 < index → ∃ symbol constraint, .mk symbol constraint [.var (index + 1)] ∈ edges

mutual
/-- Nested requests either retain every enclosing input or erase only the immediate parent while retaining all older inputs. -/
def Selective (depth : Nat) : Syntax Symbol Guard → Prop
  | .empty | .var _ => True
  | .node edges => EdgesSelective depth edges
  | .union members => ManySelective depth members
  | .binder _ body => match body with
    | .node edges => (∃ keepHead, Declared depth keepHead edges ∧ (keepHead = false → Erased 1 (.node edges))) ∧
        EdgesSelective (depth + 1) edges
    | _ => False
termination_by expression => sizeOf expression

/-- Each ordinary child follows the same selective-retention declaration. -/
def ManySelective (depth : Nat) : List (Syntax Symbol Guard) → Prop
  | [] => True
  | first :: rest => Selective depth first ∧ ManySelective depth rest
termination_by expressions => sizeOf expressions

/-- Source edge children preserve their actual lexical depth. -/
def EdgesSelective (depth : Nat) : List (EdgeSyntax Symbol Guard) → Prop
  | [] => True
  | .mk _ _ children :: rest => ManySelective depth children ∧ EdgesSelective depth rest
termination_by expressions => sizeOf expressions
end

/-- Actual immediate-parent preparation is available for every remaining ordinary child. -/
def ManyReady [DecidableEq (EdgeKey Symbol Guard)] (expressions : List (Syntax Symbol Guard))
    (environment : List (Value Symbol Guard)) (state : State Symbol Guard) : Prop :=
  ∀ expression ∈ expressions, Ready expression environment state

/-- Actual immediate-parent preparation is available below every remaining source edge. -/
def EdgesReady [DecidableEq (EdgeKey Symbol Guard)] (expressions : List (EdgeSyntax Symbol Guard))
    (environment : List (Value Symbol Guard)) (state : State Symbol Guard) : Prop :=
  ∀ symbol constraint children, .mk symbol constraint children ∈ expressions → ManyReady children environment state

/-- Node child sites cross no new binder before their direct execution. -/
theorem ready_node [DecidableEq (EdgeKey Symbol Guard)] {edges : List (EdgeSyntax Symbol Guard)}
    {environment : List (Value Symbol Guard)} {state : State Symbol Guard}
    (ready : Ready (.node edges) environment state) : EdgesReady edges environment state := by
  intro symbol constraint children edge child member
  exact ready.descendant (.node edge member (.here child))

/-- Union child sites also retain the same actual immediate parent. -/
theorem ready_union [DecidableEq (EdgeKey Symbol Guard)] {members : List (Syntax Symbol Guard)}
    {environment : List (Value Symbol Guard)} {state : State Symbol Guard}
    (ready : Ready (.union members) environment state) : ManyReady members environment state :=
  fun child member => ready.descendant (.union member (.here child))

/-- Later source effects preserve the actual prepared sites of every remaining child. -/
theorem ManyReady.grows [DecidableEq (EdgeKey Symbol Guard)] {expressions : List (Syntax Symbol Guard)}
    {environment : List (Value Symbol Guard)} {before after : State Symbol Guard}
    (ready : ManyReady expressions environment before) (growth : Grows before after) :
    ManyReady expressions environment after := fun expression member => (ready expression member).grows growth

/-- If the nearest input is not an active erased frame, direct older retention covers every pending key. -/
theorem retained_frames (frames : List (Frame Symbol Guard)) (environment : List (Value Symbol Guard))
    (depth : Nat) (length : environment.length = depth) (active : Active frames environment)
    (keepHead : Bool) (headSafe : keepHead = true ∨ ¬ HeadActive frames environment)
    (value : Value Symbol Guard)
    (retained : ∀ index name, index < depth → (keepHead = true ∨ 0 < index) →
      environment[index]?.getD .empty = .reference name → name ∈ value.free) :
    ∀ frame ∈ frames, frame.name ∈ value.free := by
  intro frame member
  obtain ⟨index, bound, lookup⟩ := List.mem_iff_getElem.mp (active frame member)
  have allowed : keepHead = true ∨ 0 < index := by
    rcases headSafe with kept | absent
    · exact .inl kept
    · right
      by_cases zero : index = 0
      · subst index
        exact False.elim (absent ⟨frame, member, by
          cases environment with
          | nil => simp at bound
          | cons first rest => simpa using congrArg some lookup⟩)
      · omega
  exact retained index frame.name (by simpa only [length] using bound) allowed
    (by simp only [List.getElem?_eq_getElem bound, lookup, Option.getD_some])

end MicroCFTA.InternedSelectiveConstruction
