from pathlib import Path
import re,hashlib
repo=Path('/home/tritlo/Code/mcfta/lean/MicroCFTA');out=Path('/tmp/mcfta-flat-recursive-20261027/finite-callback-draft')
old=(repo/'SourcePruningEnumerationFiniteCallbackResources.lean').read_text()
s=old[:old.index(' := by',old.index('theorem callback_finite_complete_resources'))]
s=s.replace('import MicroCFTA.SourcePruningEnumerationFiniteContract','import MicroCFTA.SourceFlatPruningFiniteContract\nimport MicroCFTA.SourceFlatPruningContinuation')
s=s.replace('namespace MicroCFTA.SourcePruningEnumerationRecursive','namespace MicroCFTA.SourceFlatPruningRecursive')
s=s.replace('open SourcePruningRecordTypes','open SourcePruningRecordTypes\nopen SourcePruningEnumerationRecursive (Packet callback_complete OutcomeResources)')
s=s.replace('  (Output (bits + 2) Typing) (Failure (bits + 2) Typing) (bits + 2)','  (SourcePruningEnumerationRecursive.Output (bits + 2) Typing)\n  (SourcePruningEnumerationRecursive.Failure (bits + 2) Typing) (bits + 2)')
s=s.replace('local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint','local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint\nlocal notation "FlatCached" => EnumerationFlatCached.Cached Symbol Constraint')
s=re.sub(r'(?<![\w.])continueWith\b','SourcePruningEnumerationRecursive.continueWith',s)
s=re.sub(r'(?<![\w.])resume\b','SourcePruningEnumerationRecursive.resume',s)
s=s.replace('# A concrete fragment callback at a finite recursive depth','# Actual flat fragment callbacks at finite recursive depth')
s=s.replace('The callback retains every stored bucket. The returned packet uses the\nsame original mass ceiling. One common work bound covers recording and\nthe recursive driver supplied by the smaller-depth contract.','The original callback producer runs before the flat input is quantified.\nThe returned packet retains the original mass ceiling. One common work\nbound covers recording and the related smaller-depth recursive driver.')
s=s.replace('/-- The original callback packet and finite-depth contract derive the actual hook and its resources. -/','/-- Original callback resources derive both actual hooks at one uniform finite-depth bound. -/')
s+=''' ∧
      (∀ (flat : FlatCached), EnumerationFlatCached.Related flat before →
        ∀ extra, ∃ flatOutcome,
          SourceFlatPruningRecursive.continueWith
            (SourceFlatPruningRecursive.resume holeKey fits admits graph templates checkEmpty edgesOf
              stop order (fuel + extra) recursiveFuel)
            graph templates stop order (fuel + extra) metadata uv fragment caller memos.query flat = flatOutcome ∧
          SourceFlatPruningRecursive.ResultRelated flatOutcome outcome) := by
  obtain ⟨callbackFuel, result, after, returned, stable, frame, types, holes, typing, callback⟩ :=
    callback_complete formulas solver inventory graph templates metadata uv fragment caller memos before
      packet allocated
  by_cases rejected : result.1 = true
  · have resources : OutcomeResources (Typing := Typing) formulas solver caller seed (.complete [] caller memos.query) := by
      refine ⟨caller, inventory, memos, Post.refl packet.context, bounded, known, rfl, rfl, ?_⟩
      intro output member
      exact False.elim (List.not_mem_nil member)
    have growth := SourcePruningEnumerationFiniteReservation.final_ge recursiveFuel seed ceiling
    refine ⟨callbackFuel, result, after, .complete [] caller memos.query,
      returned, stable, frame, types, holes, typing, callback, ?_, resources.mono growth.1 growth.2, ?_⟩
    · intro extra
      rw [(callback extra).2.2
        (SourcePruningEnumerationRecursive.resume holeKey fits admits graph templates checkEmpty edgesOf
          stop order (callbackFuel + extra) recursiveFuel) stop order, ite_eq_left rejected]
    · intro flat related extra
      obtain ⟨flatAfter, actual, _cores⟩ := SourceFlatPruningOracle.recordTypes_replays graph templates
        (callbackFuel + extra) metadata uv (.inl fragment) flat.core before.core result after related.core
          (callback extra).1
      refine ⟨.complete [] caller memos.query, ?_, ?_⟩
      · change SourceFlatPruningContinuation.continueWith SourceFlatPruningRecursive.Failure.callback
          (SourceFlatPruningRecursive.resume holeKey fits admits graph templates checkEmpty edgesOf stop order
            (callbackFuel + extra) recursiveFuel) graph templates stop order (callbackFuel + extra)
          metadata uv fragment caller memos.query flat = .complete [] caller memos.query
        rw [SourceFlatPruningContinuation.continueWith_exact SourceFlatPruningRecursive.Failure.callback
          (SourceFlatPruningRecursive.resume holeKey fits admits graph templates checkEmpty edgesOf stop order
            (callbackFuel + extra) recursiveFuel) graph templates stop order (callbackFuel + extra)
          metadata uv fragment caller memos.query flat result flatAfter actual, ite_eq_left rejected]
      · exact ⟨.nil, rfl, rfl⟩
  · have massAfter : suspendedBound (EnumerationExpandableIndex.frame after before).core ≤ ceiling := by
      change suspendedBound after ≤ ceiling
      rw [SourcePruningEnumerationPrefixAdmission.suspendedBound_values before.core after frame.values]
      exact mass
    obtain ⟨resumeFuel, outcome, running, resources, flatRunning⟩ := recursive
      inventory caller memos (EnumerationExpandableIndex.frame after before) result.2 seed ceiling
      returned bounded known selectionMembers selectionLength massAfter reserved
    refine ⟨callbackFuel + resumeFuel, result, after, outcome,
      returned, stable, frame, types, holes, typing, ?_, ?_, resources, ?_⟩
    · intro extra
      have actual := callback (resumeFuel + extra)
      rw [← Nat.add_assoc] at actual
      exact actual
    · intro extra
      have actual := callback (resumeFuel + extra)
      rw [← Nat.add_assoc] at actual
      rw [actual.2.2
        (SourcePruningEnumerationRecursive.resume holeKey fits admits graph templates checkEmpty edgesOf
          stop order (callbackFuel + resumeFuel + extra) recursiveFuel) stop order, ite_eq_right rejected]
      have observed := running (callbackFuel + extra)
      have common : resumeFuel + (callbackFuel + extra) = callbackFuel + resumeFuel + extra := by omega
      rw [common] at observed
      exact observed
    · intro flat related extra
      have success := (callback (resumeFuel + extra)).1
      rw [← Nat.add_assoc] at success
      obtain ⟨flatAfter, actual, cores⟩ := SourceFlatPruningOracle.recordTypes_replays graph templates
        (callbackFuel + resumeFuel + extra) metadata uv (.inl fragment) flat.core before.core result after
        related.core success
      have caches := EnumerationFlatCached.frame_related related cores
      obtain ⟨flatOutcome, resumed, compared⟩ :=
        flatRunning (EnumerationFlatCached.frame flatAfter flat) caches (callbackFuel + extra)
      have common : resumeFuel + (callbackFuel + extra) = callbackFuel + resumeFuel + extra := by omega
      rw [common] at resumed
      refine ⟨flatOutcome, ?_, compared⟩
      change SourceFlatPruningContinuation.continueWith SourceFlatPruningRecursive.Failure.callback
        (SourceFlatPruningRecursive.resume holeKey fits admits graph templates checkEmpty edgesOf stop order
          (callbackFuel + resumeFuel + extra) recursiveFuel) graph templates stop order
          (callbackFuel + resumeFuel + extra) metadata uv fragment caller memos.query flat = flatOutcome
      rw [SourceFlatPruningContinuation.continueWith_exact SourceFlatPruningRecursive.Failure.callback
        (SourceFlatPruningRecursive.resume holeKey fits admits graph templates checkEmpty edgesOf stop order
          (callbackFuel + resumeFuel + extra) recursiveFuel) graph templates stop order
          (callbackFuel + resumeFuel + extra) metadata uv fragment caller memos.query flat result flatAfter actual,
        ite_eq_right rejected]
      exact resumed

end MicroCFTA.SourceFlatPruningRecursive
'''
p=out/'SourceFlatPruningRecursiveCallbackResources.lean';assert not p.exists();p.write_text(s)
# Check old declaration prefix, changing only the induction contract namespace and qualifying old endpoints.
def head(t):a=t.index('theorem callback_finite_complete_resources');return t[a:t.index(' := by',a)]
def norm(t):
 for pre in ['SourcePruningEnumerationRecursive.','SourceFlatPruningRecursive.']:t=t.replace(pre,'')
 return re.sub(r'\s+','',t)
assert norm(head(s)).startswith(norm(head(old)))
print(p,len(p.read_bytes()),len(s.splitlines()),hashlib.sha256(p.read_bytes()).hexdigest())
