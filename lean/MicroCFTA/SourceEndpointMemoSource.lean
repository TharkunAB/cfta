import MicroCFTA.SourceEndpointMemoCorrect
import MicroCFTA.SourceEndpointGateCompletion

/-!
# Descendant memo readback from original source construction

Actual construction supplies coherent resident inputs. A completed query
stores its exact immutable input and concrete answer. The next identical
query returns that answer without changing either memo family.
-/
namespace MicroCFTA.SourceEndpointMemoSource
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open SourceObservations SourceSymbolicIndex SourceEndpointMemo
open InternedNestedConstruction (Syntax Outcome)
local notation "Symbol" => Label FullSyntax.Formula
local notation "Guard" => Constraint FullSyntax.Formula
local notation "source" => SourceMemoGate.unconstrained

/-- First-value storage always leaves a completed entry at the queried identity. -/
theorem save_present (memo : Memo) (input : Value Symbol Guard) (answer : Bool) :
    ∃ original result, save memo input answer input.referenceOf = some (original, result) := by
  cases found : memo input.referenceOf with
  | none => exact ⟨input, answer, by simp [save, found]⟩
  | some pair => rcases pair with ⟨original, result⟩; exact ⟨original, result, by simp [save, found]⟩

/-- Every completed helper query retains an entry for its own original physical key. -/
theorem run_present (input : Value Symbol Guard) (memos : Memos) :
    ∃ original result, (SourceEndpointMemo.run input memos).2.descendants input.referenceOf = some (original, result) := by
  rw [SourceEndpointMemo.run.eq_def]
  cases found : memos.descendants input.referenceOf with
  | some pair => rcases pair with ⟨original, result⟩; exact ⟨original, result, found⟩
  | none => exact save_present _ _ _

/-- Coherent original inputs derive exact complete saved-record readback after an actual query. -/
theorem run_cached (input : Value Symbol Guard) (heap : State Symbol Guard) (coherent : Coherent heap)
    (available : Available heap input) (memos : Memos) (valid : SourceEndpointMemo.Valid heap memos) :
    (SourceEndpointMemo.run input memos).2.descendants input.referenceOf =
      some (input, SourceEndpointReachability.reaches source input) := by
  obtain ⟨original, answer, found⟩ := run_present input memos
  have checked := SourceEndpointMemoCorrect.run_checked input heap coherent available memos valid
  obtain ⟨identity, originalAvailable, actual⟩ := checked.valid.descendants _ original answer found
  have same := InternedFreshProbeKeys.resident_reference_injective heap coherent original input
    originalAvailable.resident available.resident identity
  subst original
  simpa only [actual] using found

/-- The next identical query is an exact hit and changes neither memo family. -/
theorem warm_self (input : Value Symbol Guard) (heap : State Symbol Guard) (coherent : Coherent heap)
    (available : Available heap input) (memos : Memos) (valid : SourceEndpointMemo.Valid heap memos) :
    SourceEndpointMemo.run input (SourceEndpointMemo.run input memos).2 =
      (SourceEndpointReachability.reaches source input, (SourceEndpointMemo.run input memos).2) := by
  rw [SourceEndpointMemo.run.eq_def, run_cached input heap coherent available memos valid]

/-- Original cold source construction derives valid descendant queries and stable exact warm hits. -/
theorem source_checked [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard) :
    ∃ value heap, InternedFreshOrdinaryConstruction.build expression [] empty = .done value heap ∧
      SourceEndpointMemoCorrect.Checked heap SourceEndpointMemo.empty
        (SourceEndpointReachability.reaches source value) (SourceEndpointMemo.run value SourceEndpointMemo.empty) ∧
      SourceEndpointMemo.run value (SourceEndpointMemo.run value SourceEndpointMemo.empty).2 =
        (SourceEndpointReachability.reaches source value, (SourceEndpointMemo.run value SourceEndpointMemo.empty).2) := by
  obtain ⟨value, heap, done⟩ := InternedFreshOrdinaryClosedCompletion.closed_complete expression
  let node := InternedFreshOrdinaryGateRank.fromCompleted expression value heap done
  have coherent := node.context.normal.facts.coherent
  have available := node.available
  have valid := empty_valid heap
  exact ⟨value, heap, done, SourceEndpointMemoCorrect.run_checked value heap coherent available SourceEndpointMemo.empty valid,
    warm_self value heap coherent available SourceEndpointMemo.empty valid⟩

end MicroCFTA.SourceEndpointMemoSource
