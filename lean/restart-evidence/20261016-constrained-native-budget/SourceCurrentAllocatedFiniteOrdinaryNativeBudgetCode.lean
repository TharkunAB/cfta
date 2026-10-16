import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryReservations
import MicroCFTA.SourceEqualityNativeDemand

/-!
# Compositional constructor-request budgets for source code

A scheme fixes admitted recursive requests and their costs. Work budgets
bound literal constructor requests on every heap. Continuations have a
uniform bound before any returned value is known. This algebra states no
execution completion or physical returned-state law.
-/
namespace MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryNativeBudgetCode
open InternedConstructorTemplates SourceRecursiveIntersectionCode SourceRecursiveIntersectionThunks
open SourceCurrentAllocatedFiniteOrdinaryReservations
variable {Symbol Guard A B : Type}

/-- A scheme fixes the independent recursive request domain and its budget. -/
structure Scheme (Symbol Guard : Type) where
  nodeInputs : NodeRequest Symbol Guard → Prop
  edgeInputs : EdgeRequest Symbol Guard → Prop
  nodeCost : NodeRequest Symbol Guard → Nat
  edgeCost : EdgeRequest Symbol Guard → Nat

variable [DecidableEq (EdgeKey Symbol Guard)]

/-- Each instruction reserves its own request budget and a uniform continuation budget. -/
def Bound (scheme : Scheme Symbol Guard) : Code Symbol Guard A → Nat → Prop
  | .pure _, _ | .fail _, _ => True
  | .work job next, budget => ∃ own tail, own + tail ≤ budget ∧
      (∀ heap, nodeRequests (observe job heap) + edgeRequests (observe job heap) ≤ own) ∧
      ∀ value, Bound scheme (next value) tail
  | .node request next, budget => scheme.nodeInputs request ∧ ∃ tail,
      scheme.nodeCost request + tail ≤ budget ∧ ∀ value, Bound scheme (next value) tail
  | .edge request next, budget => scheme.edgeInputs request ∧ ∃ tail,
      scheme.edgeCost request + tail ≤ budget ∧ ∀ value, Bound scheme (next value) tail
  | .finishNode _ _ next, budget | .finishEdge _ _ next, budget => Bound scheme next budget
  | .enter .., _ | .read .., _ | .optionalBinder .., _ => False

namespace Bound
variable {scheme : Scheme Symbol Guard}

/-- Increasing a budget retains the same code certificate. -/
theorem weaken {code : Code Symbol Guard A} {budget larger : Nat}
    (bound : Bound scheme code budget) (enough : budget ≤ larger) : Bound scheme code larger := by
  induction code generalizing budget larger with
  | pure | fail => trivial
  | work job next _ =>
      obtain ⟨own, tail, within, requests, rest⟩ := bound
      exact ⟨own, tail, Nat.le_trans within enough, requests, rest⟩
  | node request next _ | edge request next _ =>
      obtain ⟨inputs, tail, within, rest⟩ := bound
      exact ⟨inputs, tail, Nat.le_trans within enough, rest⟩
  | finishNode handle value next ih | finishEdge handle value next ih => exact ih bound enough
  | enter | read | optionalBinder => exact False.elim bound

/-- Sequencing adds independent budgets without executing either continuation. -/
theorem bind {code : Code Symbol Guard A} {next : A → Code Symbol Guard B} {first second : Nat}
    (bound : Bound scheme code first) (rest : ∀ value, Bound scheme (next value) second) :
    Bound scheme (code.bind next) (first + second) := by
  induction code generalizing first with
  | pure value => exact (rest value).weaken (by omega)
  | fail failure => trivial
  | work job resume ih =>
      obtain ⟨own, tail, within, requests, remaining⟩ := bound
      exact ⟨own, tail + second, by omega, requests, fun value => ih value (remaining value)⟩
  | node request resume ih | edge request resume ih =>
      obtain ⟨inputs, tail, within, remaining⟩ := bound
      exact ⟨inputs, tail + second, by omega, fun value => ih value (remaining value)⟩
  | finishNode handle value next ih | finishEdge handle value next ih => exact ih bound
  | enter | read | optionalBinder => exact False.elim bound

/-- Pure results make no constructor request, including at budget zero. -/
theorem pure (scheme : Scheme Symbol Guard) (value : A) (budget : Nat) :
    Bound scheme (.pure value) budget := True.intro

/-- Explicit failure makes no constructor request and asserts no successful return. -/
theorem fail (scheme : Scheme Symbol Guard) (failure : SourceRecursiveIntersectionKernel.Failure) (budget : Nat) :
    Bound scheme (.fail failure : Code Symbol Guard A) budget := True.intro

/-- A node request adds its fixed scheme cost before its uniform continuation. -/
theorem node {request : NodeRequest Symbol Guard} {next : Value Symbol Guard → Code Symbol Guard A} {tail : Nat}
    (inputs : scheme.nodeInputs request) (rest : ∀ value, Bound scheme (next value) tail) :
    Bound scheme (.node request next) (scheme.nodeCost request + tail) :=
  ⟨inputs, tail, Nat.le_refl _, rest⟩

/-- An edge request adds its fixed scheme cost before its uniform continuation. -/
theorem edge {request : EdgeRequest Symbol Guard} {next : EdgeValue Symbol Guard → Code Symbol Guard A} {tail : Nat}
    (inputs : scheme.edgeInputs request) (rest : ∀ value, Bound scheme (next value) tail) :
    Bound scheme (.edge request next) (scheme.edgeCost request + tail) :=
  ⟨inputs, tail, Nat.le_refl _, rest⟩

/-- An ordered walk adds each call's independent static cost in source order. -/
theorem walk_sum (call : A → Code Symbol Guard B) (cost : A → Nat) (values : List A)
    (calls : ∀ value ∈ values, Bound scheme (call value) (cost value)) :
    Bound scheme (walk call values) (values.map cost).sum := by
  induction values with
  | nil => trivial
  | cons value values ih =>
      have remaining := ih (fun child member => calls child (List.mem_cons_of_mem _ member))
      have returned : ∀ first, Bound scheme
          ((walk call values).bind (fun rest => .pure (first :: rest))) (values.map cost).sum := by
        intro first
        simpa only [Nat.add_zero] using remaining.bind (fun rest => pure scheme (first :: rest) 0)
      exact (calls value List.mem_cons_self).bind returned

/-- A uniform per-call bound multiplies by the literal list length. -/
theorem walk (call : A → Code Symbol Guard B) (values : List A) (perCall : Nat)
    (calls : ∀ value ∈ values, Bound scheme (call value) perCall) :
    Bound scheme (SourceRecursiveIntersectionCode.walk call values) (perCall * values.length) := by
  have result := walk_sum call (fun _ => perCall) values calls
  have summed : (values.map (fun _ => perCall)).sum = perCall * values.length := by
    rw [List.map_const', List.sum_replicate_nat, Nat.mul_comm]
  simpa only [summed] using result

/-- A literal Work request uses a heap-independent bound and a uniform continuation. -/
theorem work {X : Type} (job : Work Symbol Guard X) {next : X → Code Symbol Guard A} {own tail : Nat}
    (requests : ∀ heap, nodeRequests (observe job heap) + edgeRequests (observe job heap) ≤ own)
    (rest : ∀ value, Bound scheme (next value) tail) : Bound scheme (.work job next) (own + tail) :=
  ⟨own, tail, Nat.le_refl _, requests, rest⟩

/-- Raw node construction makes at most one request on every heap. -/
theorem work_makeNode (edges : List (EdgeValue Symbol Guard))
    {next : Value Symbol Guard → Code Symbol Guard A} {tail : Nat}
    (rest : ∀ value, Bound scheme (next value) tail) : Bound scheme (.work (makeNode edges) next) (1 + tail) := by
  apply work _ ?_ rest
  intro heap
  have requests := makeNode_requests edges heap
  rw [requests.1, requests.2]
  split <;> omega

/-- Raw edge construction makes exactly one request on every heap. -/
theorem work_makeEdge (symbol : Symbol) (guard : Guard) (values : List (Value Symbol Guard))
    {next : EdgeValue Symbol Guard → Code Symbol Guard A} {tail : Nat}
    (rest : ∀ value, Bound scheme (next value) tail) :
    Bound scheme (.work (makeEdge symbol guard values) next) (1 + tail) := by
  apply work _ ?_ rest
  intro heap
  simp only [makeEdge_observe, nodeRequests, edgeRequests]
  omega
end Bound

local notation "SourceSymbol" => SourceObservations.Label FullSyntax.Formula
local notation "SourceGuard" => SourceSymbolicIndex.Constraint FullSyntax.Formula

/-- A checked edge body retains the same request cost before its literal continuation. -/
def ControlBound [DecidableEq (EdgeKey SourceSymbol SourceGuard)]
    (scheme : Scheme SourceSymbol SourceGuard) : SourceEqualityNativeDemand.Control A → Nat → Prop
  | .code code, budget => Bound scheme code budget
  | .edgeBody request next, budget => scheme.edgeInputs request ∧ ∃ tail,
      scheme.edgeCost request + tail ≤ budget ∧ ∀ value, Bound scheme (next value) tail

namespace ControlBound
variable [DecidableEq (EdgeKey SourceSymbol SourceGuard)]
variable {scheme : Scheme SourceSymbol SourceGuard}

/-- A larger control budget retains the exact checked control. -/
theorem weaken {control : SourceEqualityNativeDemand.Control A} {budget larger : Nat}
    (bound : ControlBound scheme control budget) (enough : budget ≤ larger) :
    ControlBound scheme control larger := by
  cases control with
  | code code => exact Bound.weaken bound enough
  | edgeBody request next =>
      obtain ⟨inputs, tail, within, rest⟩ := bound
      exact ⟨inputs, tail, Nat.le_trans within enough, rest⟩
end ControlBound

end MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryNativeBudgetCode
