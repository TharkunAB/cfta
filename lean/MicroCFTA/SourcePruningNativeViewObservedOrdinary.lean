import MicroCFTA.SourcePruningNativeView
import MicroCFTA.MergedFreshOrdinaryColdReplay

/-!
# Ordinary results at actual successful narrowing points

Original cache resources produce an ordinary result at one sufficient bound.
Cold replay identifies that result with the actual successful observation.
-/
namespace MicroCFTA.SourcePruningNativeView
open InternedConstructorTemplates InternedProbeProvenance
local notation "Symbol" => SourcePruningTemplates.Symbol
variable {Guard Key : Type}

private theorem narrowAt_done_moreFuel
    [DecidableEq (EdgeKey Symbol Guard)]
    (fits : Key → Symbol → Bool) (admits : Key → Value Symbol Guard → Bool)
    (fuel extra : Nat) (key : Key) (value : Value Symbol Guard)
    (before : State Symbol Guard) (result : Value Symbol Guard) (after : State Symbol Guard)
    (observed : narrowAt fits admits fuel key value before = .done result after) :
    narrowAt fits admits (fuel + extra) key value before = .done result after := by
  unfold narrowAt at observed ⊢
  cases read : MergedFreshOrdinaryExposure.nodeEdges fuel value before with
  | done rows middle =>
      have stable := MergedFreshOrdinaryColdReplay.nodeEdges_stable fuel extra value before
        (by simp only [read, MergedSourceExposure.Finished])
      rw [read] at stable
      simpa only [read, stable] using observed
  | unresolved name middle =>
      simp only [read] at observed
      cases observed
  | pending pendingKey middle =>
      simp only [read] at observed
      cases observed
  | exhausted middle =>
      simp only [read] at observed
      cases observed

/-- Original cache resources derive an ordinary result at any actual successful narrowing point. -/
theorem narrowAt_done_ordinary
    [DecidableEq (EdgeKey Symbol Guard)]
    (fits : Key → Symbol → Bool) (admits : Key → Value Symbol Guard → Bool)
    (fuel : Nat) (key : Key) (value : Value Symbol Guard)
    (before : State Symbol Guard) (result : Value Symbol Guard) (after : State Symbol Guard)
    (ready : SourceEqualityRequiredCache.Ready before)
    (available : Available before value) (closed : value.free = [])
    (observed : narrowAt fits admits fuel key value before = .done result after) :
    SourceEqualityRequiredCache.Ordinary result := by
  obtain ⟨bound, _rows, _middle, ownResult, ownAfter, _exposed, _built, _running, _kept,
      _available, _closed, ordinary, _resultRows, _secondRead, _emptyIff, _rowsEmptyIff, stable⟩ :=
    narrowAt_complete fits admits key value before ready available closed
  have actualAtSum := narrowAt_done_moreFuel fits admits fuel bound key value before result after observed
  have ownAtSum : narrowAt fits admits (fuel + bound) key value before = .done ownResult ownAfter := by
    simpa only [Nat.add_comm] using stable fuel
  have resultSame : result = ownResult :=
    (MergedSourceComparison.Result.done.inj (actualAtSum.symm.trans ownAtSum)).1
  rw [resultSame]
  exact ordinary

end MicroCFTA.SourcePruningNativeView
