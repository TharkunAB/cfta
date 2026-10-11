import MicroCFTA.DistinctRank

/-!
# Union with an enclosing recursion reference

`Interned.Operations.union` concatenates `nodeEdges`. A bare `Rec` contributes
no edges. This source behavior is documented, but it is weaker than language
union inside a nested binder. The example is `A = a | wrap(B); B = A | b`.
The source union drops the reference to A, leaving `A = a | wrap(b)`.
-/

namespace MicroCFTA.OpenUnion
open Language

/-- An open reference or an explicit alternative list. -/
inductive Operand (State Symbol : Type) where
  | reference : State → Operand State Symbol
  | alternatives : List (Edge State Symbol) → Operand State Symbol

/-- The source union ignores bare references when it reads alternatives. -/
def sourceUnion (operands : List (Operand State Symbol)) : List (Edge State Symbol) :=
  operands.flatMap fun
    | .reference _ => []
    | .alternatives edges => edges

/-- A reference contributes no edge in the actual source operation. -/
theorem reference_discarded (q : State) (edges : List (Edge State Symbol)) :
    sourceUnion [.reference q, .alternatives edges] = edges := by
  simp [sourceUnion]

/-- One unconstrained transition in the example. -/
def edge (symbol : Nat) (children : List Bool) : Edge Bool Nat := ⟨symbol, children, fun _ => true⟩

/-- The ordinary finite graph for the declared two mutually recursive languages. -/
def intended : Automaton Bool Nat
  | false => [edge 0 [], edge 2 [true]]
  | true => [edge 0 [], edge 2 [true], edge 1 []]

/-- The graph after `sourceUnion` discards the enclosing recursion reference. -/
def actual : Automaton Bool Nat
  | false => [edge 0 [], edge 2 [true]]
  | true => sourceUnion [.reference false, .alternatives [edge 1 []]]

/-- The finite term `wrap(a)` belongs to the declared language. -/
def witness : Term Nat := .node 2 [.node 0 []]

/-- The source operation can omit a concrete finite term inside a closed outer binder. -/
theorem enclosing_reference_loses_term :
    Accepts intended false witness ∧ ¬ Accepts actual false witness := by
  constructor
  · exact ((mem_enumerate_iff intended 2 false witness).mp (by decide +kernel)).1
  · intro accepted
    have member := (mem_enumerate_iff actual 2 false witness).mpr ⟨accepted, by simp [witness, Term.height]⟩
    have absent : witness ∉ enumerate actual 2 false := by decide +kernel
    exact absent member

end MicroCFTA.OpenUnion
