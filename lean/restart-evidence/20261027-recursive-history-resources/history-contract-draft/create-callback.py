from pathlib import Path
repo=Path('/home/tritlo/Code/mcfta/lean/MicroCFTA');base=Path('/tmp/mcfta-recursive-history-resources-20261027/history-contract-draft')
old=(repo/'SourcePruningEnumerationFiniteCallbackResources.lean').read_text();a=old.index('theorem callback_finite_complete_resources\n');z=old.index(' := by',a)
contract=old[a:z].replace('theorem callback_finite_complete_resources\n','theorem callback_finite_complete_resources_with_history\n',1).replace('(recursive : Complete (bits := bits)','(recursive : CompleteWithHistory (bits := bits)',1)
contract+=''' ∧
      RecursiveCallbackAdmission formulas solver inventory caller memos result.2
        (EnumerationExpandableIndex.frame after before) uv fragment recursiveFuel seed ceiling ∧
      (∀ extra, result.1 = false → ∀ output ∈ SourcePruningEnumerationHookInvocation.hookOutputs outcome,
        ResourceHistory holeKey fits admits graph templates checkEmpty edgesOf stop order formulas solver
          (fuel + extra) recursiveFuel inventory caller memos result.2
          (EnumerationExpandableIndex.frame after before) seed ceiling
          (SourcePruningEnumerationRestart.decision stop order result.2
            (EnumerationExpandableIndex.frame after before)) output)'''
preamble=old[old.index('namespace MicroCFTA.SourcePruningEnumerationRecursive'):old.index('/-- The original callback packet')]
source='''import MicroCFTA.SourcePruningEnumerationFiniteHistoryContract
import MicroCFTA.SourcePruningEnumerationFiniteCallbackResources

/-!
# Actual finite callback composition with admitted output histories

The original recording producer supplies its actual updated metadata and core.
A false callback applies the stronger smaller-depth contract at that frame.
One common work bound covers recording, recursion and every output history.
No successful future callback or recursive outcome is an admission premise.
-/
'''+preamble+'''/-- Retain the full callback result and derive admitted histories at its actual false restart. -/
'''+contract+''' := by
  obtain ⟨callbackFuel, result, after, returned, stable, frame, types, holes, typing, callback⟩ :=
    callback_complete formulas solver inventory graph templates metadata uv fragment caller memos before packet allocated
  have massAfter : suspendedBound (EnumerationExpandableIndex.frame after before).core ≤ ceiling := by
    change suspendedBound after ≤ ceiling
    rw [SourcePruningEnumerationPrefixAdmission.suspendedBound_values before.core after frame.values]
    exact mass
  have returnedAdmission : RecursiveCallbackAdmission formulas solver inventory caller memos result.2
      (EnumerationExpandableIndex.frame after before) uv fragment recursiveFuel seed ceiling := by
    refine ⟨returned, ?_, bounded, known, massAfter, reserved⟩
    change FragmentBound after.counter fragment
    rw [frame.counter]
    exact allocated
  by_cases rejected : result.1 = true
  · have resources : OutcomeResources (Typing := Typing) formulas solver caller seed (.complete [] caller memos.query) := by
      refine ⟨caller, inventory, memos, Post.refl packet.context, bounded, known, rfl, rfl, ?_⟩
      intro output member
      exact False.elim (List.not_mem_nil member)
    have growth := SourcePruningEnumerationFiniteReservation.final_ge recursiveFuel seed ceiling
    refine ⟨callbackFuel, result, after, .complete [] caller memos.query,
      returned, stable, frame, types, holes, typing, callback, ?_, resources.mono growth.1 growth.2,
      returnedAdmission, ?_⟩
    · intro extra
      rw [(callback extra).2.2
        (resume holeKey fits admits graph templates checkEmpty edgesOf stop order (callbackFuel + extra) recursiveFuel)
        stop order, ite_eq_left rejected]
    · intro _extra _false output member
      exact False.elim (List.not_mem_nil member)
  · obtain ⟨resumeFuel, outcome, running, resources, histories⟩ := recursive
      inventory caller memos (EnumerationExpandableIndex.frame after before) result.2 seed ceiling
      returned bounded known selectionMembers selectionLength massAfter reserved
    refine ⟨callbackFuel + resumeFuel, result, after, outcome,
      returned, stable, frame, types, holes, typing, ?_, ?_, resources, returnedAdmission, ?_⟩
    · intro extra
      have actual := callback (resumeFuel + extra)
      rw [← Nat.add_assoc] at actual
      exact actual
    · intro extra
      have actual := callback (resumeFuel + extra)
      rw [← Nat.add_assoc] at actual
      rw [actual.2.2
        (resume holeKey fits admits graph templates checkEmpty edgesOf stop order
          (callbackFuel + resumeFuel + extra) recursiveFuel) stop order, ite_eq_right rejected]
      have observed := running (callbackFuel + extra)
      have common : resumeFuel + (callbackFuel + extra) = callbackFuel + resumeFuel + extra := by omega
      rw [common] at observed
      exact observed
    · intro extra _false output member
      have observed := histories (callbackFuel + extra) output member
      have common : resumeFuel + (callbackFuel + extra) = callbackFuel + resumeFuel + extra := by omega
      rw [common] at observed
      exact observed

end MicroCFTA.SourcePruningEnumerationRecursive
'''
p=base/'SourcePruningEnumerationFiniteCallbackHistory.lean';assert not p.exists();p.write_text(source);(base/'revisions/v1'/p.name).write_text(source)
print(p);print(len(source.splitlines()),len(source.encode()))
