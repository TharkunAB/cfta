from pathlib import Path
import hashlib,re
repo=Path('/home/tritlo/Code/mcfta/lean/MicroCFTA');out=Path('/tmp/mcfta-flat-recursive-20261027/finite-head-draft')
old=(repo/'SourcePruningEnumerationFiniteHeadResources.lean').read_text()
s=old.replace('import MicroCFTA.SourcePruningEnumerationFiniteReceiptResources','import MicroCFTA.SourceFlatPruningRecursiveReceiptResources\nimport MicroCFTA.SourceFlatPruningNativeHeadResources').replace('namespace MicroCFTA.SourcePruningEnumerationNativeHookResources','namespace MicroCFTA.SourceFlatPruningNativeHookResources').replace('end MicroCFTA.SourcePruningEnumerationNativeHookResources','end MicroCFTA.SourceFlatPruningNativeHookResources')
s=s.replace('(Packet Output Failure continueWith resume Complete OutcomeResources)','(Packet Output Failure continueWith resume OutcomeResources)\nopen SourceFlatPruningRecursive (Complete)')
s=s.replace('local notation "Receipt" => SourcePruningEnumerationSelectedEdge.Result','local notation "Receipt" => SourcePruningEnumerationSelectedEdge.Result\nlocal notation "FlatReceipt" => SourceFlatPruningSelectedEdge.Result\nlocal notation "FlatCached" => EnumerationFlatCached.Cached Symbol Constraint')
s=s.replace('# An actual edge followed by a finite recursive callback','# Actual flat edges followed by finite recursive callbacks')
s=s.replace('/-- The original packet and finite reservation derive an actual edge and its recursive callback. -/','/-- Original resources couple the actual edge and its finite-depth callback at one work bound. -/')
flatHook='''
          (∀ extra (flatReceipt : FlatReceipt (bits + 2)),
            SourceFlatPruningSelectedEdge.ResultRelated flatReceipt receipt →
            match (generalizing := false) flatReceipt with
            | .complete fragment actual saved after =>
                ∃ flatOutcome,
                  SourceFlatPruningRecursive.continueWith
                    (SourceFlatPruningRecursive.resume holeKey fits admits graph templates checkEmpty edgesOf
                      stop order (bound + extra) recursiveFuel)
                    graph templates stop order (bound + extra) metadata uv fragment actual saved after = flatOutcome ∧
                  SourceFlatPruningRecursive.ResultRelated flatOutcome outcome
            | _ => SourceFlatPruningRecursive.ResultRelated
                (.complete [] middleCaller middleMemos.query) outcome)'''
flatHead='''
      (∀ (flat : FlatCached), EnumerationFlatCached.Related flat before →
        ∀ extra, ∃ flatReceipt,
          SourceFlatPruningCapturedEdge.run checkEmpty (bound + extra) (bound + extra) (bound + extra)
            uv scs edge caller flat memos.query = some flatReceipt ∧
          SourceFlatPruningSelectedEdge.ResultRelated flatReceipt receipt)'''
s=s.replace('          match outcome with','          (match outcome with',1)
needle='          | .stopped _ _ _ => True) := by'
assert s.count(needle)==1
s=s.replace(needle,'          | .stopped _ _ _ => True) ∧'+flatHook+') ∧'+flatHead+' := by')
s=s.replace('headRun, headPost, headQueries, admitted, headPending, history, shape, headFits, headKnown, cacheBounds⟩ :=','headRun, headPost, headQueries, admitted, headPending, history, shape, headFits, headKnown, cacheBounds, headFlat⟩ :=')
s=s.replace('SourcePruningEnumerationNativeBranchCompletion.head_complete_cache_bounds seed','SourceFlatPruningNativeHeadResources.head_complete_cache_bounds seed')
# Add the exact diagonal flat head family before splitting the retained original head shape.
needle='  rcases shape with advanced | unsupported'
helper='''  have flatHeadAt (flat : FlatCached) (related : EnumerationFlatCached.Related flat before)
      (w : Nat) (large : headBound ≤ w) :
      ∃ flatReceipt,
        SourceFlatPruningCapturedEdge.run checkEmpty w w w uv scs edge caller flat memos.query = some flatReceipt ∧
        SourceFlatPruningSelectedEdge.ResultRelated flatReceipt receipt := by
    have nl : n ≤ w := by dsimp [headBound] at large; omega
    have pl : p ≤ w := by dsimp [headBound] at large; omega
    have hl : h ≤ w := by dsimp [headBound] at large; omega
    obtain ⟨flatReceipt, actual, compared⟩ := headFlat flat related (w - n) w w pl hl
    rw [Nat.add_sub_of_le nl] at actual
    exact ⟨flatReceipt, actual, compared⟩
'''
assert s.count(needle)==1;s=s.replace(needle,helper+needle)
s=s.replace('obtain ⟨callbackFuel, outcome, callbackRun, resources⟩ := receipt_finite_complete_resources','obtain ⟨callbackFuel, outcome, callbackRun, resources, flatCallbackRun⟩ := receipt_finite_complete_resources')
s=s.replace('.inr ⟨outcome, advancedQuery, ?_, fullResources, ?_⟩⟩','.inr ⟨outcome, advancedQuery, ?_, fullResources, ?_, ?_⟩, ?_⟩')
needle='''          exact ⟨next, final, post, query, captured, returnedFits, returnedKnown⟩
  · exact ⟨headBound, receipt, middleCaller, saved, middleMemos, middleInventory,
      fun extra => headAt (headBound + extra) (by omega), headPost, headQueries,
      admitted, receiptPending, history, cacheBounds, boundedHead, knownHead, .inl unsupported⟩'''
replacement='''          exact ⟨next, final, post, query, captured, returnedFits, returnedKnown⟩
    · intro extra flatReceipt compared
      have actual := flatCallbackRun (headBound + extra) flatReceipt compared
      have common : callbackFuel + (headBound + extra) = headBound + callbackFuel + extra := by omega
      rw [common] at actual
      exact actual
    · intro flat related extra
      exact flatHeadAt flat related (headBound + callbackFuel + extra) (by omega)
  · refine ⟨headBound, receipt, middleCaller, saved, middleMemos, middleInventory,
      fun extra => headAt (headBound + extra) (by omega), headPost, headQueries,
      admitted, receiptPending, history, cacheBounds, boundedHead, knownHead, .inl unsupported, ?_⟩
    intro flat related extra
    exact flatHeadAt flat related (headBound + extra) (by omega)'''
assert s.count(needle)==1;s=s.replace(needle,replacement)
p=out/'SourceFlatPruningRecursiveHeadResources.lean';assert not p.exists();p.write_text(s)
# Recover the entire original output by projecting just the two added families.
def header(t):a=t.index('theorem head_finite_complete_resources');return t[a:t.index(' := by',a)]
a=header(s);restored=a.replace(' ∧'+flatHead,'').replace(' ∧'+flatHook,'').replace('          (match outcome with','          match outcome with').replace('          | .stopped _ _ _ => True))','          | .stopped _ _ _ => True)')
norm=lambda t:re.sub(r'\s+','',t)
assert norm(restored)==norm(header(old))
print(p,len(p.read_bytes()),len(s.splitlines()),hashlib.sha256(p.read_bytes()).hexdigest())
