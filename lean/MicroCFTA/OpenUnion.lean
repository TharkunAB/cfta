import MicroCFTA.DistinctRank
import MicroCFTA.EpsilonUnion

/-!
# Union with an enclosing recursion reference

At baseline `d7f7c11`, `Interned.Operations.union` concatenated `nodeEdges`.
A bare `Rec` contributed no edges. This historical behavior is weaker than language
union inside a nested binder. The example is `A = a | wrap(B); B = A | b`.
The old union dropped the reference to A, leaving `A = a | wrap(b)`.
The repaired operation retains epsilon operands, as modeled in `EpsilonUnion`.
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

/-- The repaired graph retains the reference from B to A as an epsilon edge. -/
def repaired : EpsilonUnion.Graph Bool Nat where
  references
    | false => []
    | true => [false]
  transitions
    | false => [edge 0 [], edge 2 [true]]
    | true => [edge 1 []]

/-- The enclosing reference supplies the missing child without consuming a constructor. -/
theorem repaired_accepts : EpsilonUnion.Accepts repaired false witness := by
  apply EpsilonUnion.Accepts.node (edge 2 [true]) [.node 0 []] (by simp [repaired])
  · apply All₂.cons ?_ .nil
    apply EpsilonUnion.Accepts.reference (target := false) (by simp [repaired])
    exact .node (edge 0 []) [] (by simp [repaired]) .nil rfl
  · rfl

/-- Executable depth-first epsilon elimination retains the previously lost term. -/
theorem repaired_collection_accepts :
    Accepts (EpsilonUnion.collect [false, true] repaired) false witness := by
  exact (EpsilonUnion.collect_exact [false, true]
    (by intro state; cases state <;> simp) (by simp) repaired false witness).mpr repaired_accepts

end MicroCFTA.OpenUnion
