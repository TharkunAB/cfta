import MicroCFTA.MergedFreshOrdinaryColdReplay
import MicroCFTA.InternedFreshOrdinaryStatefulGateCompletion

/-!
# Coherent source outer-unfold memo execution

Memo entries use actual canonical references and complete immutable inputs.
A saved result replays without constructor-cache effects. Misses execute
actual repaired unfolding and install a coherent result. Cache growth keeps
every earlier saved result valid.
-/
namespace MicroCFTA.InternedFreshOrdinaryUnfoldMemo
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedConstruction (Outcome)
open InternedFreshOrdinaryGateRank (Node step)
open InternedBinderProtocol (NodeRef)

/-- The source memo keeps each queried record and its complete unfolding result. -/
abbrev Memo (Symbol Guard : Type) := NodeRef → Option (Value Symbol Guard × Value Symbol Guard)

/-- Every memo entry has exact canonical identity, provenance, and effect-free unfolding readback. -/
def Correct [DecidableEq (EdgeKey Symbol Guard)] (state : State Symbol Guard) (memo : Memo Symbol Guard) : Prop :=
  ∀ key input output, memo key = some (input, output) → input.referenceOf = key ∧
    Available state input ∧ Available state output ∧
    InternedFreshOrdinaryStoredSubstitution.unfold input state = .done output state

/-- No source unfolding result is saved in the initial memo. -/
def empty : Memo Symbol Guard := fun _ => none

/-- The empty source memo is coherent in every constructor cache. -/
theorem empty_correct [DecidableEq (EdgeKey Symbol Guard)] (state : State Symbol Guard) : Correct state (empty (Symbol := Symbol) (Guard := Guard)) := by
  intro key input output found
  cases found

/-- A miss saves the queried complete source record under its canonical reference. -/
def insert (memo : Memo Symbol Guard) (input output : Value Symbol Guard) : Memo Symbol Guard :=
  fun key => if key = input.referenceOf then some (input, output) else memo key

/-- Source memo execution returns a saved result or performs one actual repaired unfolding. -/
def run [DecidableEq (EdgeKey Symbol Guard)] (input : Value Symbol Guard) (memo : Memo Symbol Guard)
    (state : State Symbol Guard) : Outcome Symbol Guard (Value Symbol Guard × Memo Symbol Guard) :=
  match memo input.referenceOf with
  | some (_, output) => .done (output, memo) state
  | none => (InternedFreshOrdinaryStoredSubstitution.unfold input state).bind fun output after =>
      .done (output, insert memo input output) after

/-- Actual constructor and reservation growth preserve every complete saved unfolding. -/
theorem grows [DecidableEq (EdgeKey Symbol Guard)] (before after : State Symbol Guard)
    (valid : Valid before) (growth : Grows before after)
    (history : Extends before.nodes.issued after.nodes.issued) (memo : Memo Symbol Guard)
    (correct : Correct before memo) : Correct after memo := by
  intro key input output found
  obtain ⟨identity, inputAvailable, outputAvailable, actual⟩ := correct key input output found
  exact ⟨identity, inputAvailable.grows before after growth history, outputAvailable.grows before after growth history,
    InternedFreshOrdinaryStoredSubstitution.unfold_replay input before after output before valid actual growth⟩

/-- Every actual hit or miss completes with exact constructor readback and a coherent returned memo. -/
theorem run_complete [DecidableEq (EdgeKey Symbol Guard)] (node : Node Symbol Guard)
    (memo : Memo Symbol Guard) (correct : Correct node.state memo) :
    ∃ after : Node Symbol Guard, ∃ saved : Memo Symbol Guard,
      run node.value memo node.state = .done (after.value, saved) after.state ∧
      InternedFreshOrdinaryStoredSubstitution.unfold node.value node.state = .done after.value after.state ∧
      Correct after.state saved ∧ Grows node.state after.state ∧
      Extends node.state.nodes.issued after.state.nodes.issued := by
  cases found : memo node.value.referenceOf with
  | some pair =>
      rcases pair with ⟨input, output⟩
      obtain ⟨identity, inputAvailable, outputAvailable, actual⟩ := correct _ input output found
      have same := InternedFreshProbeKeys.resident_reference_injective node.state node.context.normal.facts.coherent input node.value
        inputAvailable.resident node.available.resident identity
      subst input
      let after : Node Symbol Guard := { node with value := output, available := outputAvailable }
      exact ⟨after, memo, by simp [run, found, after], actual, correct, grows_refl _, extends_refl _⟩
  | none =>
      let after := (step node).result
      have actual : InternedFreshOrdinaryStoredSubstitution.unfold node.value node.state = .done after.value after.state :=
        (step node).actual
      have growth := InternedFreshOrdinaryStatefulGateCompletion.step_growth node
      have old := grows node.state after.state node.context.normal.facts.coherent.valid growth.1 growth.2 memo correct
      have saved : Correct after.state (insert memo node.value after.value) := by
        intro key input output selected
        dsimp only [insert] at selected
        split at selected
        · rename_i same
          have fields : node.value = input ∧ after.value = output := by simpa only [Option.some.injEq, Prod.mk.injEq] using selected
          rcases fields with ⟨rfl, rfl⟩
          exact ⟨same.symm, node.available.grows node.state after.state growth.1 growth.2, after.available,
            InternedFreshOrdinaryStoredSubstitution.unfold_replay node.value node.state after.state after.value after.state
              node.context.normal.facts.coherent.valid actual (grows_refl _)⟩
        · exact old key input output selected
      exact ⟨after, insert memo node.value after.value, by simp only [run, found, actual, Outcome.bind],
        actual, saved, growth.1, growth.2⟩

end MicroCFTA.InternedFreshOrdinaryUnfoldMemo
