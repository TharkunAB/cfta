import MicroCFTA.SourceEqualityPartialMemoReuse

/-!
# Scoped soundness of actual result-memo requests

Checks follow the original request selected by demand. A completed hit uses
the current cell proof. A new completion uses the actual body receipt and
retains the same running request. Body effects are not replayed at a hit.
-/
namespace MicroCFTA.SourceEqualityPartialMemoRequestProofs
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open SourceObservations SourceSymbolicIndex SourceEqualityClassFoldGraph SourceEqualityNativeScoped
open SourceEqualityPartialMemoWorker SourceEqualityPartialMemoFrame SourceEqualityPartialMemoSound
open SourceEqualityPartialKeyTransport SourceEqualityPartialGraphLaws SourceEqualityPartialScope
local notation "Symbol" => Label FullSyntax.Formula
local notation "Guard" => Constraint FullSyntax.Formula
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}

/-- Check only a body that demand actually starts, at its exact full running state. -/
def Checked (check : Nat → Request → SourceEqualityPartialMemoWorker.State width → Prop)
    (candidate : Request) (before : SourceEqualityPartialMemoWorker.State width) : Prop :=
  let prepared := prepare candidate before
  let published := FlatMemoThunk.lookupOrInsert prepared.1 candidate prepared.2.memo
  let demanded := FlatMemoThunk.demand published.1 published.2
  match demanded.1 with
  | .evaluate original => check published.1 original { prepared.2 with memo := demanded.2 }
  | _ => True

variable (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (ambient : InternedGuardedLanguage.Env Symbol)
local notation "holds" => acceptsConstraint formulas solver

/-- Actual body soundness and structural frames derive sound request completion, including ready hits. -/
theorem verified
    (body : Nat → Request → SourceEqualityPartialMemoWorker.State width → Result width (Value Symbol Guard))
    (check : Nat → Request → SourceEqualityPartialMemoWorker.State width → Prop)
    (bodiesFrame : ∀ handle original state, Valid (stateTables state) → Framed state (body handle original state))
    (bodies : ∀ handle original state result after, check handle original state → Sound holds ambient state →
      state.memo.cells handle = some ⟨original, .evaluating⟩ →
      body handle original state = .done (.ok result) after → Scope state.native →
        Sound holds ambient after ∧ NodeLaw formulas solver ambient original.inherited original.value state.native result after.native)
    (candidate : Request) (before : SourceEqualityPartialMemoWorker.State width) (result : Value Symbol Guard)
    (after : SourceEqualityPartialMemoWorker.State width)
    (plan : Checked check candidate before) (sound : Sound holds ambient before)
    (scope : Scope before.native) (available : Available before.native.machine.heap candidate.value)
    (closed : candidate.value.free = []) (wellFormed : SourceEqualityDescend.WellFormed candidate.inherited)
    (done : request body candidate before = .done (.ok result) after) :
    Sound holds ambient after ∧ NodeLaw formulas solver ambient candidate.inherited candidate.value before.native result after.native := by
  let prepared := prepare candidate before
  let published := FlatMemoThunk.lookupOrInsert prepared.1 candidate prepared.2.memo
  let demanded := FlatMemoThunk.demand published.1 published.2
  let running : SourceEqualityPartialMemoWorker.State width := { prepared.2 with memo := demanded.2 }
  have preparation := prepare_sound holds ambient candidate before sound
  have publication := lookup_sound holds ambient prepared.1 candidate prepared.2 preparation available closed wellFormed
    (prepare_key candidate before sound.valid)
  have demand := demand_sound holds ambient published.1 { prepared.2 with memo := published.2 } publication
  have linkedKey : running.memo.table prepared.1 = some published.1 :=
    (demand_frame published.1 ⟨prepared.2.constraints, published.2⟩ publication.valid).published _ _
      (FlatMemoThunk.lookup_stored prepared.1 candidate prepared.2.memo)
  have candidateKey := prepare_key candidate before sound.valid
  change ((match demanded.1 with
    | .absent => .incomplete (.absent prepared.1 published.1 running)
    | .busy => .incomplete (.busy prepared.1 published.1 running)
    | .ready value => .done (.ok value) running
    | .evaluate original => finish published.1 (body published.1 original running)) : Result width (Value Symbol Guard)) = .done (.ok result) after at done
  change (match demanded.1 with | .evaluate original => check published.1 original running | _ => True) at plan
  cases observed : demanded.1 with
  | absent | busy => simp only [observed] at done; cases done
  | ready value =>
      have actual : FlatMemoThunk.demand published.1 published.2 = (.ready value, demanded.2) := Prod.ext observed rfl
      obtain ⟨original, originalCell, unchanged⟩ := FlatMemoThunk.demand_ready_original published.1 published.2 value demanded.2 actual
      have returned : running.memo.cells published.1 = some ⟨original, .returned value⟩ := by
        simpa only [running, unchanged] using originalCell
      have good := demand.cells published.1 ⟨original, .returned value⟩ returned
      obtain ⟨cell, stored, linked⟩ := demand.valid.2.linked prepared.1 published.1 linkedKey
      have same := Option.some.inj (stored.symm.trans returned)
      subst cell
      have semantic := cached_identity_meaning holds ambient before.native.machine.heap
        scope.native.semantic.ready.semantic.1.normal.facts.coherent running.constraints demand.valid.1
        original.inherited candidate.inherited prepared.1.1 original.value candidate.value value good.2.2.1 wellFormed
        linked.1 candidateKey.1 good.1 available (linked.2.trans candidateKey.2.symm) good.2.2.2.2.2
      simp only [observed, Result.done.injEq, Except.ok.injEq] at done
      rcases done with ⟨rfl, rfl⟩
      exact ⟨demand, fun _ _ _ => ⟨scope, SourceEqualityRequiredCache.pure_keeps _ scope.native.semantic.ready,
        good.2.2.2.1, good.2.2.2.2.1, semantic⟩⟩
  | evaluate original =>
      have actual : FlatMemoThunk.demand published.1 published.2 = (.evaluate original, demanded.2) := Prod.ext observed rfl
      have started := (FlatMemoThunk.demand_evaluate published.1 published.2 demanded.2 original actual).2
      have good := demand.cells published.1 ⟨original, .evaluating⟩ started
      obtain ⟨cell, stored, linked⟩ := demand.valid.2.linked prepared.1 published.1 linkedKey
      have same := Option.some.inj (stored.symm.trans started)
      subst cell
      simp only [observed] at plan done
      cases completed : body published.1 original running with
      | incomplete observation => simp only [completed, finish] at done; cases done
      | done answer middle =>
          cases answer with
          | error message => simp only [completed, finish] at done; cases done
          | ok value =>
              have verified := bodies published.1 original running value middle plan demand started completed scope
              have native := verified.2 scope good.1 good.2.1
              have frame := bodiesFrame published.1 original running demand.valid
              rw [completed] at frame
              have nowRunning := frame.running published.1 original started
              have final := finish_sound holds ambient published.1 original value middle verified.1 nowRunning
                native.2.2.1 native.2.2.2.1 native.2.2.2.2
              have semantic := cached_identity_meaning holds ambient before.native.machine.heap
                scope.native.semantic.ready.semantic.1.normal.facts.coherent running.constraints demand.valid.1
                original.inherited candidate.inherited prepared.1.1 original.value candidate.value value good.2.2.1 wellFormed
                linked.1 candidateKey.1 good.1 available (linked.2.trans candidateKey.2.symm) native.2.2.2.2
              simp only [completed, finish, Result.done.injEq, Except.ok.injEq] at done
              rcases done with ⟨rfl, rfl⟩
              exact ⟨final, fun _ _ _ => ⟨native.1, native.2.1, native.2.2.1, native.2.2.2.1, semantic⟩⟩

end MicroCFTA.SourceEqualityPartialMemoRequestProofs
