import MicroCFTA.RecursiveJoinTyped

/-!
# Concrete recursive join field checks

The examples use independent pure leaf fields. Kernel reduction checks the
private wrappers, size-split order, invalid keys, and the nullary branch.
-/
set_option maxRecDepth 4096

namespace MicroCFTA.RecursiveJoinExamples
open Language GeneratorCombinators IntegerTermViews SizedRank
open RecursiveCallbackTermination RecursiveCallbackTables
open RecursiveJoinFields RecursiveJoinCallbacks

/-- One independently indexed pure term at size zero. -/
def atom (symbol : Nat) : Finite Nat :=
  ⟨fun size => if size = 0 then 1 else 0,
    fun position => if position = ⟨0, 0⟩ then some (.node (.user symbol) []) else none,
    fun view wanted => if project view (.node (.user symbol) []) = wanted then [(⟨0, 0⟩, true)] else []⟩

/-- These leaves have the declared finite index interval. -/
theorem atom_indexed (symbol : Nat) : FiniteIndex (atom symbol) := by
  intro ⟨size, rank⟩
  cases size <;> cases rank <;> simp [atom]

/-- These leaves have complete inverse fields in every source view. -/
theorem atom_exact (symbol : Nat) : FiniteExact (atom symbol) := by
  intro view wanted ⟨size, rank⟩
  cases size <;> cases rank <;> simp [atom]

/-- A nullary join still retains its center and operation. -/
theorem nullary :
    (field 7 (atom 20) []).counts 0 = 1 ∧
    (field 7 (atom 20) []).select ⟨0, 0⟩ =
      some (.node .joinN [.node .centerKeyed [.node (.user 20) []]]) ∧
    (field 7 (atom 20) []).positions .whole
      [.node .joinN [.node .centerKeyed [.node (.user 20) []]]] = [(⟨0, 0⟩, true)] := by
  cbv

/-- The first argument has two alternatives at the same positive size. -/
def alternative : Finite Nat :=
  RecursiveFieldCombinators.pay (RecursiveFieldCombinators.field (.choice (.finite (atom 1)) (.finite (atom 2))))

def arguments : List (Finite Nat) :=
  [alternative, atom 3, RecursiveFieldCombinators.pay (RecursiveFieldCombinators.pay (atom 4))]

def chosen : EngineTerm Nat :=
  SupportJoin.joinTerm 7 (.node (.user 20) [])
    [.node (.choice 1) [.node (.user 2) []], .node (.user 3) [], .node (.user 4) []]

/-- Three arguments retain their position keys and the independent size-class rank. -/
theorem ternary :
    (field 7 (atom 20) arguments).counts 3 = 2 ∧
    (field 7 (atom 20) arguments).select ⟨3, 1⟩ = some chosen ∧
    (field 7 (atom 20) arguments).select ⟨3, 2⟩ = none ∧
    (field 7 (atom 20) arguments).positions .whole [chosen] = [(⟨3, 1⟩, true)] ∧
    (field 7 (atom 20) arguments).positions .spine [chosen] = [(⟨3, 1⟩, true)] ∧
    (field 7 (atom 20) arguments).positions .labelled (project .labelled chosen) = [(⟨3, 1⟩, true)] := by
  cbv

/-- The same payload with the wrong component remains a bounded unchecked candidate. -/
def wrongComponent : EngineTerm Nat :=
  SupportJoin.joinTerm 8 (.node (.user 20) [])
    [.node (.choice 1) [.node (.user 2) []], .node (.user 3) [], .node (.user 4) []]

theorem wrong_component :
    (field 7 (atom 20) arguments).positions .whole [wrongComponent] = [(⟨3, 1⟩, false)] ∧
    (field 7 (atom 20) arguments).positions .spine [wrongComponent] = [(⟨3, 1⟩, false)] ∧
    (field 7 (atom 20) arguments).positions .labelled (project .labelled wrongComponent) = [(⟨3, 1⟩, false)] := by
  cbv

/-- A missing argument cannot silently truncate the Cartesian request. -/
theorem wrong_arity :
    (field 7 (atom 20) arguments).positions .whole
      [SupportJoin.joinTerm 7 (.node (.user 20) []) []] = [] ∧
    (field 7 (atom 20) arguments).positions .labelled
      [.node .centerKeyed [.node (.user 20) []], .node .argKeyed [.node (.user 1) []]] = [] := by
  cbv

/-- Each operand has one class-zero and one class-one member. -/
def twoSizes (left right : Nat) : Finite Nat :=
  RecursiveFieldCombinators.field (.choice (.finite (atom left)) (.pay (.finite (atom right))))

/-- Left size is the outer split order. No diagonal product is dropped. -/
theorem split_order :
    (field 0 (twoSizes 10 11) [twoSizes 12 13]).counts 1 = 2 ∧
    (field 0 (twoSizes 10 11) [twoSizes 12 13]).select ⟨1, 0⟩ =
      some (SupportJoin.joinTerm 0 (.node (.choice 0) [.node (.user 10) []])
        [.node (.choice 1) [.node (.user 13) []]]) ∧
    (field 0 (twoSizes 10 11) [twoSizes 12 13]).select ⟨1, 1⟩ =
      some (SupportJoin.joinTerm 0 (.node (.choice 1) [.node (.user 11) []])
        [.node (.choice 0) [.node (.user 12) []]]) := by
  cbv

/-- A correlated leaf can contain a user value of any type. -/
def pureLeaf (value : Value) (symbol : Nat) : RecursiveJoinTyped.Leaf Nat Value :=
  ⟨⟨fun size => if size = 0 then 1 else 0,
    fun position => if position = ⟨0, 0⟩ then some (value, .node (.user symbol) []) else none⟩,
    (atom symbol).positions⟩

/-- Different argument types remain independent in the curried source chain. -/
def heterogeneous : RecursiveJoinTyped.Chain Nat (Bool → Nat → Nat) Nat :=
  .cons (pureLeaf true 1) (.cons (pureLeaf 6 2) .nil)

def heterogeneousOperation : RecursiveJoinTyped.Leaf Nat (Bool → Nat → Nat) :=
  pureLeaf (fun flag value => if flag then value + 1 else value) 20

/-- The typed value selector and join-term selector share the same complete rank. -/
theorem heterogeneous_rank :
    (heterogeneous.values heterogeneousOperation.values).select ⟨0, 0⟩ = some 7 ∧
    (field 3 heterogeneousOperation.terms heterogeneous.terms).select ⟨0, 0⟩ =
      some (SupportJoin.joinTerm 3 (.node (.user 20) []) [.node (.user 1) [], .node (.user 2) []]) ∧
    (field 3 heterogeneousOperation.terms heterogeneous.terms).positions .whole
      [SupportJoin.joinTerm 3 (.node (.user 20) []) [.node (.user 1) [], .node (.user 2) []]] = [(⟨0, 0⟩, true)] := by
  cbv

end MicroCFTA.RecursiveJoinExamples
