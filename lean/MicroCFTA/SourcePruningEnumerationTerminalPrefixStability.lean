import MicroCFTA.SourcePruningEnumerationTerminalPrefixUnique

/-!
# Stable successful terminal-prefix observations

A successful raw singleton keeps all fields at every larger representative bound.
The proof uses no cache or semantic invariant.
-/
namespace MicroCFTA.SourcePruningEnumerationTerminalPrefix
open EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationExecution

attribute [local instance] terminalPrefixMonadList terminalPrefixLawfulMonadList
local notation "Symbol" => SourcePruningTemplates.Symbol
variable {EnumGuard : Type}

private theorem point_scan_exact (fuel : Nat) (items : List Suspended)
    (before after : State Symbol EnumGuard) (recorded : List Nat)
    (observed : Success (items.mapM fun sc => representative fuel sc.var) before recorded after) :
    ExceptT.run ((items.mapM fun sc => representative fuel sc.var) before) = [.ok (recorded, after)] := by
  induction items generalizing before after recorded with
  | nil =>
      obtain ⟨valueSame, stateSame⟩ := (success_pure [] recorded before after).mp observed
      rw [valueSame, stateSame]
      rfl
  | cons sc items ih =>
      rw [List.mapM_cons] at observed ⊢
      obtain ⟨root, middle, head, continued⟩ := (success_bind _ _ _ _ _).mp observed
      obtain ⟨tail, last, tailRun, finalPure⟩ := (success_bind _ _ _ _ _).mp continued
      obtain ⟨valueSame, stateSame⟩ := (success_pure (root :: tail) recorded last after).mp finalPure
      obtain ⟨found, lookup, rootSame, middleSame⟩ :=
        (representative_success fuel sc.var before middle root).mp head
      rw [bind_single _ _ before middle root
        (by simpa only [← rootSame, ← middleSame] using representative_exact fuel sc.var before found lookup)]
      rw [bind_single _ _ middle last tail (ih middle last tail tailRun)]
      rw [valueSame, stateSame]
      rfl

private theorem point_unions_exact (fuel anchor : Nat) (items : List Suspended)
    (before after : State Symbol EnumGuard)
    (observed : Success (items.forM fun sc => unionVariables fuel anchor sc.var) before () after) :
    ExceptT.run ((items.forM fun sc => unionVariables fuel anchor sc.var) before) = [.ok ((), after)] := by
  induction items generalizing before after with
  | nil =>
      obtain ⟨_valueSame, stateSame⟩ := (success_pure () () before after).mp observed
      rw [stateSame]
      rfl
  | cons sc items ih =>
      change Success (unionVariables fuel anchor sc.var >>= fun _ =>
        items.forM fun sc => unionVariables fuel anchor sc.var) before () after at observed
      obtain ⟨ignored, middle, head, continued⟩ := (success_bind _ _ _ _ _).mp observed
      cases ignored
      obtain ⟨forest, lookup, middleSame⟩ := (unionVariables_success fuel anchor sc.var before middle).mp head
      change ExceptT.run ((unionVariables fuel anchor sc.var >>= fun _ =>
        items.forM fun sc => unionVariables fuel anchor sc.var) before) = [.ok ((), after)]
      rw [bind_single _ _ before middle ()
        (by simpa only [← middleSame] using union_exact fuel anchor sc.var before forest lookup)]
      exact ih middle after continued

private theorem point_run_exact (fuel : Nat) (first : Suspended) (rest : List Suspended)
    (waiting : EnumerationWaitingIndex.Waiting) (before after : State Symbol EnumGuard)
    (result : List Nat × Nat × EnumerationWaitingIndex.Waiting)
    (observed : Success (run fuel first rest waiting) before result after) :
    ExceptT.run (run fuel first rest waiting before) = [.ok (result, after)] := by
  unfold run at observed ⊢
  obtain ⟨recorded, scanned, scanning, continued⟩ := (success_bind _ _ _ _ _).mp observed
  obtain ⟨ignored, united, unions, continued⟩ := (success_bind _ _ _ _ _).mp continued
  cases ignored
  obtain ⟨winner, joined, resolution, returned⟩ := (success_bind _ _ _ _ _).mp continued
  obtain ⟨valueSame, stateSame⟩ := (success_pure _ result joined after).mp returned
  rw [bind_single _ _ before scanned recorded (point_scan_exact fuel (first :: rest) before scanned recorded scanning)]
  rw [bind_single _ _ scanned united () (point_unions_exact fuel first.var rest scanned united unions)]
  obtain ⟨found, lookup, winnerSame, joinedSame⟩ :=
    (representative_success fuel first.var united joined winner).mp resolution
  rw [bind_single _ _ united joined winner
    (by simpa only [← winnerSame, ← joinedSame] using representative_exact fuel first.var united found lookup)]
  rw [valueSame, stateSame]
  rfl

private theorem point_run_retains (fuel extra : Nat) (first : Suspended) (rest : List Suspended)
    (waiting : EnumerationWaitingIndex.Waiting) :
    Retains (run (EnumGuard := EnumGuard) fuel first rest waiting)
      (run (fuel + extra) first rest waiting) := by
  unfold run
  apply retains_bind _ _ _ _ (retains_mapM _ _
    (fun sc => representative_moreFuel fuel extra sc.var) (first :: rest))
  intro recorded
  apply retains_bind _ _ _ _ (retains_forM _ _
    (fun sc => unionVariables_moreFuel fuel extra first.var sc.var) rest)
  intro _
  exact retains_bind _ _ _ _ (representative_moreFuel fuel extra first.var) (fun _ => retains_refl _)

/-- A successful prefix singleton is identical at every larger representative bound. -/
theorem run_singleton_stable
    {fuel largerFuel : Nat} {first : Suspended} {rest : List Suspended}
    {waiting : EnumerationWaitingIndex.Waiting} {before after : State Symbol EnumGuard}
    {recorded : List Nat} {winner : Nat} {moved : EnumerationWaitingIndex.Waiting}
    (observed : ExceptT.run (run fuel first rest waiting before) =
      [.ok ((recorded, winner, moved), after)])
    (enough : fuel ≤ largerFuel) :
    ExceptT.run (run largerFuel first rest waiting before) =
      [.ok ((recorded, winner, moved), after)] := by
  have successful : Success (run fuel first rest waiting) before (recorded, winner, moved) after := by
    simp only [Success, observed, List.mem_singleton]
  have retained := point_run_retains fuel (largerFuel - fuel) first rest waiting
    before (recorded, winner, moved) after successful
  have sameFuel : fuel + (largerFuel - fuel) = largerFuel := by omega
  rw [sameFuel] at retained
  exact point_run_exact largerFuel first rest waiting before after (recorded, winner, moved) retained

end MicroCFTA.SourcePruningEnumerationTerminalPrefix
