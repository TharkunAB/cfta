import MicroCFTA.SourceCurrentConjunctionTuplePullOutcomeMemos
import MicroCFTA.SourceCurrentConjunctionTuplePullTotalEffects

/-!
# Ordered global memos for every total sampling outcome

Each finite observation records the literal cursor steps it reaches.
A failed final exposure retains the bundle from its completed calls.
Total sampling derives its own finite observation. Neither a successful
sample nor a future heap, receipt, or memo bundle is required.
-/
namespace MicroCFTA.SourceCurrentConjunctionTuplePullTotalOutcomeMemos
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceCurrentConjunctionRowsAllocation (Ready Effects)
open SourceCurrentConjunctionRowsWorker (Outcome)
open SourceCurrentConjunctionTuplePull (Cursor)
open SourceCurrentConjunctionTuplePullEffects (Inputs)
open SourceCurrentConjunctionTuplePullDriveEffects (Collected)
open SourceCurrentConjunctionTuplePullAdmission (Status advance drive)
open SourceCurrentConjunctionTuplePullOutcomeMemos (StepReads)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Edge" => EdgeValue Symbol Guard
local notation "Physical" => SourceCurrentConjunctionRowsWorker.Physical Symbol FullSyntax.Formula
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Valid" => EndpointMemoGateTrace.Valid
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

/-- Observation receipts keep every reached step and stop at its literal terminal outcome. -/
inductive DriveReads (h budget : Nat) : Nat → Cursor Symbol FullSyntax.Formula → List (List Edge) →
    Physical → Memos → Memos → Prop where
  | zero : DriveReads h budget 0 cursor collected before memos memos
  | failed {steps cursor collected before after fault memos saved}
      (actual : advance h budget cursor collected before = .failed fault after)
      (calls : StepReads h cursor before memos saved) :
      DriveReads h budget (steps + 1) cursor collected before memos saved
  | running {steps cursor collected before middle next sampled memos middleMemo saved}
      (actual : advance h budget cursor collected before = .done (.running next sampled) middle)
      (calls : StepReads h cursor before memos middleMemo)
      (tail : DriveReads h budget steps next sampled middle middleMemo saved) :
      DriveReads h budget (steps + 1) cursor collected before memos saved
  | fit {steps cursor collected before after sampled memos saved}
      (actual : advance h budget cursor collected before = .done (.fit sampled) after)
      (calls : StepReads h cursor before memos saved) :
      DriveReads h budget (steps + 1) cursor collected before memos saved
  | overflow {steps cursor collected before after sampled next memos saved}
      (actual : advance h budget cursor collected before = .done (.overflow sampled next) after)
      (calls : StepReads h cursor before memos saved) :
      DriveReads h budget (steps + 1) cursor collected before memos saved

/-- A total sample keeps the exact finite observation of its actual outcome. -/
def SampleReads (h budget : Nat) (nodes : List Node) (before : Physical) (memos saved : Memos) : Prop :=
  ∃ steps, drive steps h budget (SourceCurrentConjunctionTuplePull.start nodes) [] before =
      SourceCurrentConjunctionTuplePullTotal.observe
        (SourceCurrentConjunctionTuplePullTotal.sample h budget nodes before) ∧
    DriveReads h budget steps (SourceCurrentConjunctionTuplePull.start nodes) [] before memos saved

/-- One observation step retains its source cursor calls at every actual endpoint. -/
theorem advance_memos (h budget : Nat) (cursor : Cursor Symbol FullSyntax.Formula)
    (collected : List (List Edge)) (before : Physical) (ready : Ready before)
    (inputs : Inputs before.heap cursor) (memos : Memos) (valid : Valid before.heap memos) :
    ∃ saved, StepReads h cursor before memos saved ∧ Valid (advance h budget cursor collected before).state.heap saved ∧
      Extends memos.unfolding saved.unfolding ∧ saved.query = memos.query := by
  obtain ⟨saved, reads, coherent, retained, same⟩ :=
    SourceCurrentConjunctionTuplePullOutcomeMemos.step_memos h cursor before ready inputs memos valid
  refine ⟨saved, reads, ?_, retained, same⟩
  cases observed : SourceCurrentConjunctionTuplePull.step h cursor before with
  | failed fault after => simpa only [advance, observed, Outcome.bind, Outcome.state] using coherent
  | done event after =>
      cases event with
      | more next | ended => simpa only [advance, observed, Outcome.bind, Outcome.state] using coherent
      | yield tuple next =>
          simp only [advance, observed, Outcome.bind]
          split <;> simpa only [observed, Outcome.state] using coherent

/-- Finite observation derives ordered memo bundles through successful and failed prefixes. -/
theorem drive_memos (steps h budget : Nat) (cursor : Cursor Symbol FullSyntax.Formula)
    (collected : List (List Edge)) (before : Physical) (ready : Ready before)
    (inputs : Inputs before.heap cursor) (resident : Collected before.heap collected)
    (memos : Memos) (valid : Valid before.heap memos) :
    ∃ saved, DriveReads h budget steps cursor collected before memos saved ∧
      Valid (drive steps h budget cursor collected before).state.heap saved ∧
      Extends memos.unfolding saved.unfolding ∧ saved.query = memos.query := by
  induction steps generalizing cursor collected before memos with
  | zero => exact ⟨memos, .zero, valid, extends_refl _, rfl⟩
  | succ steps ih =>
      obtain ⟨middleMemo, first, coherent, retained, same⟩ :=
        advance_memos h budget cursor collected before ready inputs memos valid
      have effects := SourceCurrentConjunctionTuplePullDriveEffects.advance_effects
        h budget cursor collected before ready inputs resident
      cases observed : advance h budget cursor collected before with
      | failed fault after =>
          exact ⟨middleMemo, .failed observed first,
            by simpa only [drive, observed, Outcome.bind, Outcome.state] using coherent, retained, same⟩
      | done status after =>
          have kept : Effects before after := by simpa only [observed, Outcome.state] using effects.1
          have current : Valid after.heap middleMemo := by simpa only [observed, Outcome.state] using coherent
          have supported := effects.2 status after observed
          cases status with
          | running next sampled =>
              obtain ⟨saved, later, finalValid, finalRetained, finalSame⟩ :=
                ih next sampled after kept.ready supported.1 supported.2 middleMemo current
              exact ⟨saved, .running observed first later,
                by simpa only [drive, observed, Outcome.bind] using finalValid,
                extends_trans retained finalRetained, finalSame.trans same⟩
          | fit sampled =>
              exact ⟨middleMemo, .fit observed first,
                by simpa only [drive, observed, Outcome.bind, Outcome.state] using current, retained, same⟩
          | overflow sampled next =>
              exact ⟨middleMemo, .overflow observed first,
                by simpa only [drive, observed, Outcome.bind, Outcome.state] using current, retained, same⟩

/-- Current original inputs derive the actual total sample's memo bundle on every outcome. -/
theorem sample_memos (h budget : Nat) (nodes : List Node) (before : Physical) (ready : Ready before)
    (available : Values before.heap nodes) (memos : Memos) (valid : Valid before.heap memos) :
    ∃ saved, SampleReads h budget nodes before memos saved ∧
      Valid (SourceCurrentConjunctionTuplePullTotal.sample h budget nodes before).state.heap saved ∧
      Extends memos.unfolding saved.unfolding ∧ saved.query = memos.query := by
  obtain ⟨steps, eventual⟩ := SourceCurrentConjunctionTuplePullTotal.sample_observation h budget nodes before
  have observed := eventual 0
  simp only [Nat.add_zero, SourceCurrentConjunctionTuplePullAdmission.sample] at observed
  obtain ⟨saved, reads, coherent, retained, same⟩ := drive_memos steps h budget
    (SourceCurrentConjunctionTuplePull.start nodes) [] before ready
    (SourceCurrentConjunctionTuplePullEffects.start_inputs before.heap nodes available)
    (by intro tuple member; cases member) memos valid
  refine ⟨saved, ⟨steps, observed, reads⟩, ?_, retained, same⟩
  simpa only [observed, SourceCurrentConjunctionTuplePullTotal.observe_state] using coherent

end MicroCFTA.SourceCurrentConjunctionTuplePullTotalOutcomeMemos
