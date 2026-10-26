import MicroCFTA.SourcePruningEnumerationTerminalPrefix

/-!
# Exact terminal-prefix observations

Successful observations at different representative bounds return the same
recorded roots, winner, waiting index and core state.
The comparison uses no state invariant or completion premise.
-/
namespace MicroCFTA.SourcePruningEnumerationTerminalPrefix
open EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationExecution

attribute [local instance] terminalPrefixMonadList terminalPrefixLawfulMonadList

local notation "Symbol" => SourcePruningTemplates.Symbol
variable {EnumGuard : Type}

private theorem scan_exact (fuel : Nat) (items : List Suspended)
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

private theorem unions_exact (fuel anchor : Nat) (items : List Suspended)
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

private theorem run_exact (fuel : Nat) (first : Suspended) (rest : List Suspended)
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
  rw [bind_single _ _ before scanned recorded (scan_exact fuel (first :: rest) before scanned recorded scanning)]
  rw [bind_single _ _ scanned united () (unions_exact fuel first.var rest scanned united unions)]
  obtain ⟨found, lookup, winnerSame, joinedSame⟩ :=
    (representative_success fuel first.var united joined winner).mp resolution
  rw [bind_single _ _ united joined winner
    (by simpa only [← winnerSame, ← joinedSame] using representative_exact fuel first.var united found lookup)]
  rw [valueSame, stateSame]
  rfl

private theorem run_moreFuel (fuel extra : Nat) (first : Suspended) (rest : List Suspended)
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

/-- Successful bounds identify every returned terminal-prefix field. -/
theorem run_unique (first : Suspended) (rest : List Suspended)
    (waiting : EnumerationWaitingIndex.Waiting) (before : State Symbol EnumGuard)
    {fuel otherFuel : Nat} {recorded otherRecorded : List Nat} {winner otherWinner : Nat}
    {moved otherMoved : EnumerationWaitingIndex.Waiting} {joined otherJoined : State Symbol EnumGuard}
    (one : ExceptT.run (run fuel first rest waiting before) = [.ok ((recorded, winner, moved), joined)])
    (two : ExceptT.run (run otherFuel first rest waiting before) =
      [.ok ((otherRecorded, otherWinner, otherMoved), otherJoined)]) :
    recorded = otherRecorded ∧ winner = otherWinner ∧ moved = otherMoved ∧ joined = otherJoined := by
  have firstSuccess : Success (run fuel first rest waiting) before (recorded, winner, moved) joined := by
    simp only [Success, one, List.mem_singleton]
  have secondSuccess : Success (run otherFuel first rest waiting) before
      (otherRecorded, otherWinner, otherMoved) otherJoined := by
    simp only [Success, two, List.mem_singleton]
  have firstMore := run_moreFuel fuel (max fuel otherFuel - fuel) first rest waiting
    before (recorded, winner, moved) joined firstSuccess
  have secondMore := run_moreFuel otherFuel (max fuel otherFuel - otherFuel) first rest waiting
    before (otherRecorded, otherWinner, otherMoved) otherJoined secondSuccess
  have firstFuel : fuel + (max fuel otherFuel - fuel) = max fuel otherFuel := by omega
  have secondFuel : otherFuel + (max fuel otherFuel - otherFuel) = max fuel otherFuel := by omega
  rw [firstFuel] at firstMore
  rw [secondFuel] at secondMore
  have firstExact := run_exact _ first rest waiting before joined (recorded, winner, moved) firstMore
  have secondExact := run_exact _ first rest waiting before otherJoined
    (otherRecorded, otherWinner, otherMoved) secondMore
  have pairSame := Except.ok.inj (List.cons.inj (firstExact.symm.trans secondExact)).1
  obtain ⟨resultSame, joinedSame⟩ := Prod.mk.inj pairSame
  obtain ⟨recordedSame, remainingSame⟩ := Prod.mk.inj resultSame
  obtain ⟨winnerSame, movedSame⟩ := Prod.mk.inj remainingSame
  exact ⟨recordedSame, winnerSame, movedSame, joinedSame⟩

end MicroCFTA.SourcePruningEnumerationTerminalPrefix
