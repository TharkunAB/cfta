import MicroCFTA.InternedFreshOrdinaryUniformMass
import MicroCFTA.InternedStoredEncodingMass
import MicroCFTA.SourceCurrentAllocatedRecursiveOptionalBudget

/-!
# Optional-binder resources from one initial payload bound

A positive bound on current stored payloads bounds an available body's
complete encoding. Numeric constructor charges and a numeric returned-store
bound then depend only on that initial number. The actual stopping outcome
retains both bounds. No later encoded body or callback result is a premise.
-/
namespace MicroCFTA.SourceCurrentAllocatedRecursiveMassBudget
open InternedConstructorTemplates InternedProbeProvenance InternedNestedFacts
open InternedNestedConstruction (Outcome)
open InternedStoredSubstitution (leaves encode leaves_available)
open InternedFreshOrdinaryAllocationBudget (nodeBudget edgeBudget)
open SourceCurrentAllocatedRecursiveOptionalBudget (constructionSyntax)
local notation "mass" => InternedValueMass.value
local notation "Stored" => InternedValueMassHeap.Stored
local notation "maybeMu" => SourceRecursiveIntersectionMaybeMu.maybeMu
variable {Symbol Guard : Type}

/-- One initial payload bound pays for every constructor identity in this instruction. -/
def charge (bound : Nat) : Nat := 6 * 3 ^ bound

/-- A conservative number of payload growth steps covers the complete binder syntax. -/
def growthSteps (bound : Nat) : Nat := 12 * 3 ^ bound + 4

/-- The returned store bound uses only the initial common payload bound. -/
def ceiling (bound : Nat) : Nat := InternedFreshOrdinaryUniformMass.evolve bound (growthSteps bound) bound

/-- The numeric returned-store bound retains its initial bound. -/
theorem ceiling_ge (bound : Nat) : bound ≤ ceiling bound := by
  simpa only [ceiling, InternedFreshOrdinaryUniformMass.evolve] using
    InternedFreshOrdinaryUniformMass.evolve_count_mono bound (Nat.zero_le (growthSteps bound)) bound

/-- Both actual local optional charges are bounded by the initial body mass. -/
theorem body_charges (key : Nat × Nat) (body : Value Symbol Guard) (bound : Nat)
    (small : mass body ≤ bound) :
    SourceCurrentAllocatedRecursiveOptionalBudget.nodeBudget key body + 2 ≤ charge bound ∧
      SourceCurrentAllocatedRecursiveOptionalBudget.edgeBudget key body + 2 ≤ charge bound := by
  have encoded := InternedStoredEncodingMass.encode_bound (leaves body)
    [InternedBinderProtocol.Reference.intersection key.1 key.2] body
  have larger := Nat.pow_le_pow_right (by decide : 1 ≤ 3) small
  by_cases used : InternedBinderProtocol.Reference.intersection key.1 key.2 ∈ body.free
  · simp only [SourceCurrentAllocatedRecursiveOptionalBudget.nodeBudget,
      SourceCurrentAllocatedRecursiveOptionalBudget.edgeBudget, used, ite_true,
      constructionSyntax, nodeBudget, edgeBudget, charge]
    omega
  · have positive := Nat.pow_le_pow_right (by decide : 1 ≤ 3) (Nat.zero_le bound)
    simp only [Nat.pow_zero] at positive
    simp only [SourceCurrentAllocatedRecursiveOptionalBudget.nodeBudget,
      SourceCurrentAllocatedRecursiveOptionalBudget.edgeBudget, used, ite_false, Nat.zero_add, charge]
    omega

/-- The complete optional syntax fits the initial numeric growth schedule. -/
theorem syntax_transform (key : Nat × Nat) (body : Value Symbol Guard) (bound : Nat)
    (small : mass body ≤ bound) :
    InternedFreshOrdinaryResultMass.transform (constructionSyntax key body) bound ≤ ceiling bound := by
  have widths : InternedStoredEncodingWidth.Width bound (constructionSyntax key body) := by
    simp only [constructionSyntax, InternedStoredEncodingWidth.Width]
    exact InternedStoredEncodingWidth.encode_width (leaves body) [_] body bound small
  have encoded := InternedStoredEncodingMass.encode_bound (leaves body)
    [InternedBinderProtocol.Reference.intersection key.1 key.2] body
  have larger := Nat.pow_le_pow_right (by decide : 1 ≤ 3) small
  have count : nodeBudget (constructionSyntax key body) + edgeBudget (constructionSyntax key body) ≤ growthSteps bound := by
    simp only [constructionSyntax, nodeBudget, edgeBudget, growthSteps]
    omega
  exact Nat.le_trans (InternedFreshOrdinaryUniformMass.transform_bound bound (constructionSyntax key body) bound widths)
    (InternedFreshOrdinaryUniformMass.evolve_count_mono bound count bound)

/-- Every actual optional outcome derives its numeric causal store and returned payload bound. -/
theorem stored_bound [DecidableEq (EdgeKey Symbol Guard)] (key : Nat × Nat) (body : Value Symbol Guard)
    (before : State Symbol Guard) (bound : Nat) (facts : Facts before)
    (stored : Stored bound before) (available : Available before body) :
    Stored (ceiling bound) (maybeMu key body before).state ∧
      ∀ value after, maybeMu key body before = .done value after → mass value ≤ ceiling bound := by
  have small := InternedValueMassHeap.available before stored body available
  have supported := syntax_transform key body bound small
  have inputs : ∀ value ∈ leaves body, mass value ≤ bound := by
    intro value member
    exact InternedValueMassHeap.available before stored value (leaves_available body before available value member)
  rw [SourceRecursiveIntersectionMaybeMu.maybeMu_eq key body before before facts available]
  by_cases used : InternedBinderProtocol.Reference.intersection key.1 key.2 ∈ body.free
  · simp only [used, ite_true]
    have built := InternedFreshOrdinaryResultMass.build_bound (constructionSyntax key body) (leaves body) before bound stored inputs
    exact ⟨built.1.mono supported, fun value after done => Nat.le_trans (built.2 value after done) supported⟩
  · simp only [used, ite_false, Outcome.state]
    refine ⟨stored.mono (ceiling_ge bound), ?_⟩
    intro value after done
    cases done
    exact Nat.le_trans small (ceiling_ge bound)

/-- All actual stopping counters fit one numeric charge from the initial store bound. -/
theorem allocation_bound [DecidableEq (EdgeKey Symbol Guard)] (key : Nat × Nat) (body : Value Symbol Guard)
    (before : State Symbol Guard) (bound : Nat) (facts : Facts before)
    (stored : Stored bound before) (available : Available before body) :
    (maybeMu key body before).state.nodes.next ≤ before.nodes.next + charge bound ∧
      (maybeMu key body before).state.edges.next ≤ before.edges.next + charge bound := by
  have raw := SourceCurrentAllocatedRecursiveOptionalBudget.bound key body before facts available
  have paid := body_charges key body bound (InternedValueMassHeap.available before stored body available)
  constructor <;> omega

/-- Initial source records produce the bound used by an actual optional instruction. -/
theorem initial [DecidableEq (EdgeKey Symbol Guard)] (key : Nat × Nat) (body : Value Symbol Guard)
    (before : State Symbol Guard) (facts : Facts before) (available : Available before body) :
    Stored (ceiling (InternedValueMassHeap.initialBound before)) (maybeMu key body before).state ∧
      (maybeMu key body before).state.nodes.next ≤ before.nodes.next + charge (InternedValueMassHeap.initialBound before) ∧
      (maybeMu key body before).state.edges.next ≤ before.edges.next + charge (InternedValueMassHeap.initialBound before) ∧
      ∀ value after, maybeMu key body before = .done value after → mass value ≤ ceiling (InternedValueMassHeap.initialBound before) := by
  have stored := InternedValueMassHeap.initial before facts
  have size := stored_bound key body before _ facts stored available
  have counters := allocation_bound key body before _ facts stored available
  exact ⟨size.1, counters.1, counters.2, size.2⟩

end MicroCFTA.SourceCurrentAllocatedRecursiveMassBudget
