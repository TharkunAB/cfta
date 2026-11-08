import MicroCFTA.SourceCurrentConjunctionTuplePullAdmission
import MicroCFTA.SourceCurrentConjunctionTuplePullEffects

set_option autoImplicit false

/-!
Finite cursor driving retains full physical effects and clean probes.
Overflow retains the unforced continuation. Faults retain their actual
reached state. The finite observation allowance is not a runtime bound.
No equality fold or requirement row runs in this sampler.
-/
namespace MicroCFTA.SourceCurrentConjunctionTuplePullDriveEffects
open InternedConstructorTemplates
open InternedNestedProvenance (Values Edges)
open SourceCurrentConjunctionRowsWorker (Physical Outcome)
open SourceCurrentConjunctionRowsAllocation (Ready Effects)
open SourceCurrentConjunctionTuplePull (Cursor Event step start)
open SourceCurrentConjunctionTuplePullAdmission (Status advance drive sample)
open SourceCurrentConjunctionTuplePullEffects (Inputs EventInputs)
variable {Symbol Formula : Type}
local notation "Guard" => SourceSymbolicIndex.Constraint Formula
local notation "Node" => Value Symbol Guard
local notation "Edge" => EdgeValue Symbol Guard
local notation "Heap" => InternedFreshOrdinaryProbeHeap.Heap

/-- Collected raw tuples contain resident edges at the actual current heap. -/
def Collected (heap : InternedConstructorTemplates.State Symbol Guard) (tuples : List (List Edge)) : Prop :=
  ∀ tuple ∈ tuples, Edges heap tuple

/-- Every returned status retains its resident sample and any suspended cursor. -/
def StatusInputs (heap : InternedConstructorTemplates.State Symbol Guard) : Status Symbol Formula → Prop
  | .running cursor tuples | .overflow tuples cursor => Inputs heap cursor ∧ Collected heap tuples
  | .fit tuples => Collected heap tuples

private theorem collected_keeps {before after : InternedConstructorTemplates.State Symbol Guard}
    (kept : SourceEqualityRequiredCache.Keeps before after) {tuples : List (List Edge)}
    (resident : Collected before tuples) : Collected after tuples := by
  intro tuple member edge present
  exact InternedEdgeResidency.edge_grows before after kept.growth edge (resident tuple member edge present)

variable [DecidableEq Symbol]
  [DecidableEq (EdgeKey Symbol (SourceSymbolicIndex.Constraint Formula))]

/-- One sample transition preserves full effects and the actual returned status. -/
theorem advance_effects (h budget : Nat) (cursor : Cursor Symbol Formula) (collected : List (List Edge))
    (before : Physical Symbol Formula) (ready : Ready before) (inputs : Inputs before.heap cursor)
    (resident : Collected before.heap collected) :
    Effects before (advance h budget cursor collected before).state ∧
      ∀ status after, advance h budget cursor collected before = .done status after →
        StatusInputs after.heap status := by
  have first := SourceCurrentConjunctionTuplePullEffects.step_effects h cursor before ready inputs
  cases observed : step h cursor before with
  | failed fault after =>
      simp only [advance, observed, Outcome.bind, Outcome.state]
      exact ⟨by simpa only [observed, Outcome.state] using first.1,
        by intro status final same; cases same⟩
  | done event after =>
      have kept : Effects before after := by simpa only [observed, Outcome.state] using first.1
      have supported := first.2 event after observed
      have oldRows := collected_keeps kept.keeps resident
      cases event with
      | more next =>
          simp only [advance, observed, Outcome.bind, Outcome.state]
          exact ⟨kept, by intro status final same; cases same; exact ⟨supported, oldRows⟩⟩
      | ended =>
          simp only [advance, observed, Outcome.bind, Outcome.state]
          exact ⟨kept, by intro status final same; cases same; exact oldRows⟩
      | yield tuple next =>
          have sampled : Collected after.heap (collected ++ [tuple]) := by
            intro row member
            rcases List.mem_append.mp member with old | added
            · exact oldRows row old
            · simpa only [List.mem_singleton.mp added] using supported.1
          simp only [advance, observed, Outcome.bind]
          split <;> exact ⟨kept, by intro status final same; cases same; exact ⟨supported.2, sampled⟩⟩

/-- Every finite drive preserves effects at success, suspension, overflow, and faults. -/
theorem drive_effects (steps h budget : Nat) (cursor : Cursor Symbol Formula)
    (collected : List (List Edge)) (before : Physical Symbol Formula) (ready : Ready before)
    (inputs : Inputs before.heap cursor) (resident : Collected before.heap collected) :
    Effects before (drive steps h budget cursor collected before).state ∧
      ∀ status after, drive steps h budget cursor collected before = .done status after →
        StatusInputs after.heap status := by
  induction steps generalizing cursor collected before with
  | zero =>
      exact ⟨Effects.refl before ready,
        by intro status final same; cases same; exact ⟨inputs, resident⟩⟩
  | succ steps ih =>
      have first := advance_effects h budget cursor collected before ready inputs resident
      cases observed : advance h budget cursor collected before with
      | failed fault after =>
          simp only [drive, observed, Outcome.bind, Outcome.state]
          exact ⟨by simpa only [observed, Outcome.state] using first.1,
            by intro status final same; cases same⟩
      | done status after =>
          have kept : Effects before after := by simpa only [observed, Outcome.state] using first.1
          have supported := first.2 status after observed
          cases status with
          | running next sampled =>
              have later := ih next sampled after kept.ready supported.1 supported.2
              simp only [drive, observed, Outcome.bind]
              exact ⟨kept.trans later.1, later.2⟩
          | fit sampled =>
              simp only [drive, observed, Outcome.bind, Outcome.state]
              exact ⟨kept, by intro result final same; cases same; exact supported⟩
          | overflow sampled next =>
              simp only [drive, observed, Outcome.bind, Outcome.state]
              exact ⟨kept, by intro result final same; cases same; exact supported⟩

/-- The actual initial sampler derives all cursor and collected-row premises. -/
theorem sample_effects (steps h budget : Nat) (nodes : List Node) (before : Physical Symbol Formula)
    (ready : Ready before) (available : Values before.heap nodes) :
    Effects before (sample steps h budget nodes before).state ∧
      ∀ status after, sample steps h budget nodes before = .done status after →
        StatusInputs after.heap status :=
  drive_effects steps h budget (start nodes) [] before ready
    (SourceCurrentConjunctionTuplePullEffects.start_inputs before.heap nodes available)
    (by intro tuple member; cases member)

/-- One sample transition retains clean stored probes on every outcome. -/
theorem advance_probes (h budget : Nat) (cursor : Cursor Symbol Formula) (collected : List (List Edge))
    (before : Physical Symbol Formula) (ready : Ready before) (probes : Heap before.heap)
    (inputs : Inputs before.heap cursor) :
    Heap (advance h budget cursor collected before).state.heap := by
  have clean := SourceCurrentConjunctionTuplePullEffects.step_probes h cursor before ready probes inputs
  cases observed : step h cursor before with
  | failed fault after => simpa only [advance, observed, Outcome.bind, Outcome.state] using clean
  | done event after =>
      cases event with
      | more next | ended => simpa only [advance, observed, Outcome.bind, Outcome.state] using clean
      | yield tuple next =>
          simp only [advance, observed, Outcome.bind]
          split <;> simpa only [Outcome.state, observed] using clean

/-- Finite driving retains clean stored probes through every completed prefix. -/
theorem drive_probes (steps h budget : Nat) (cursor : Cursor Symbol Formula)
    (collected : List (List Edge)) (before : Physical Symbol Formula) (ready : Ready before)
    (probes : Heap before.heap) (inputs : Inputs before.heap cursor)
    (resident : Collected before.heap collected) :
    Heap (drive steps h budget cursor collected before).state.heap := by
  induction steps generalizing cursor collected before with
  | zero => exact probes
  | succ steps ih =>
      have clean := advance_probes h budget cursor collected before ready probes inputs
      have first := advance_effects h budget cursor collected before ready inputs resident
      cases observed : advance h budget cursor collected before with
      | failed fault after => simpa only [drive, observed, Outcome.bind, Outcome.state] using clean
      | done status after =>
          have kept : Effects before after := by simpa only [observed, Outcome.state] using first.1
          have reached : Heap after.heap := by simpa only [observed, Outcome.state] using clean
          have supported := first.2 status after observed
          cases status with
          | running next sampled =>
              simpa only [drive, observed, Outcome.bind] using
                ih next sampled after kept.ready reached supported.1 supported.2
          | fit sampled | overflow sampled next =>
              simpa only [drive, observed, Outcome.bind, Outcome.state] using reached

/-- Actual startup needs no pre-exposed row list or future read supplier. -/
theorem sample_probes (steps h budget : Nat) (nodes : List Node) (before : Physical Symbol Formula)
    (ready : Ready before) (probes : Heap before.heap) (available : Values before.heap nodes) :
    Heap (sample steps h budget nodes before).state.heap :=
  drive_probes steps h budget (start nodes) [] before ready probes
    (SourceCurrentConjunctionTuplePullEffects.start_inputs before.heap nodes available)
    (by intro tuple member; cases member)

end MicroCFTA.SourceCurrentConjunctionTuplePullDriveEffects
