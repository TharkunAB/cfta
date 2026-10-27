from pathlib import Path
import hashlib,re
repo=Path('/home/tritlo/Code/mcfta/lean/MicroCFTA');out=Path('/tmp/mcfta-flat-recursive-20261027/finite-sibling-draft')
old=(repo/'SourcePruningEnumerationFiniteSiblingResources.lean').read_text()
s=old.replace('import MicroCFTA.SourcePruningEnumerationContinuationHead','import MicroCFTA.SourcePruningEnumerationContinuationHead\nimport MicroCFTA.SourceFlatPruningRecursiveHeadResources\nimport MicroCFTA.SourceFlatPruningContinuationHead\nimport MicroCFTA.SourceFlatPruningRecursiveBase')
s=s.replace('namespace MicroCFTA.SourcePruningEnumerationNativeFiniteSiblingResources','namespace MicroCFTA.SourceFlatPruningNativeFiniteSiblingResources').replace('end MicroCFTA.SourcePruningEnumerationNativeFiniteSiblingResources','end MicroCFTA.SourceFlatPruningNativeFiniteSiblingResources')
s=s.replace('open SourcePruningEnumerationFiniteReservation (stage ScanReserved)','open SourcePruningEnumerationFiniteReservation (stage ScanReserved)\nopen SourcePruningEnumerationNativeFiniteSiblingResources (ReceiptAt OutputAt StoppedAt)')
s=s.replace('SourcePruningEnumerationRecursive.Complete','SourceFlatPruningRecursive.Complete')
s=s.replace('local notation "Receipt" => SourcePruningEnumerationSelectedEdge.Result','local notation "Receipt" => SourcePruningEnumerationSelectedEdge.Result\nlocal notation "FlatReceipt" => SourceFlatPruningSelectedEdge.Result\nlocal notation "FlatCached" => EnumerationFlatCached.Cached Symbol Constraint\nlocal notation "FlatOutput" => SourceFlatPruningRecursive.Output\nlocal notation "FlatFailure" => SourceFlatPruningRecursive.Failure')
a=s.index('/-- The original sibling schedule')
helpers='''universe u v

private theorem ordered_append {Left : Type u} {Right : Type v} {relation : Left → Right → Prop}
    {first last : List Left} {before after : List Right}
    (head : SourceFlatPruningNativeBranches.OrderedRelated relation first before)
    (tail : SourceFlatPruningNativeBranches.OrderedRelated relation last after) :
    SourceFlatPruningNativeBranches.OrderedRelated relation (first ++ last) (before ++ after) := by
  induction head with
  | nil => exact tail
  | cons related _ ih => exact .cons related ih

private theorem continued_hook
    (hook : Fragments.Fragment Symbol → Caller (bits + 2) → SourceEndpointMemo.Memos → FlatCached →
      SourceFlatPruningNativeContinuations.HookResult (FlatOutput (bits + 2) Typing)
        (FlatFailure (bits + 2) Typing) (bits + 2))
    (receipt : Receipt (bits + 2)) (flatReceipt : FlatReceipt (bits + 2))
    (middleCaller hookCaller : Caller (bits + 2)) (middleQueries hookQueries : SourceEndpointMemo.Memos)
    (headOutputs : List (Output (bits + 2) Typing))
    (advanced : advance receipt = some (middleCaller, middleQueries))
    (compared : SourceFlatPruningSelectedEdge.ResultRelated flatReceipt receipt)
    (observed : match (generalizing := false) flatReceipt with
      | .complete fragment actual saved after =>
          ∃ flatOutcome, hook fragment actual saved after = flatOutcome ∧
            SourceFlatPruningRecursive.ResultRelated flatOutcome (.complete headOutputs hookCaller hookQueries)
      | _ => SourceFlatPruningRecursive.ResultRelated
          (.complete [] middleCaller middleQueries) (.complete headOutputs hookCaller hookQueries)) :
    ∃ flatOutputs,
      SourceFlatPruningNativeBranches.OrderedRelated SourceFlatPruningRecursive.OutputRelated flatOutputs headOutputs ∧
      match (generalizing := false) flatReceipt with
      | .complete fragment actual saved after =>
          hook fragment actual saved after = .complete flatOutputs hookCaller hookQueries
      | _ => SourceFlatPruningNativeBranches.advance flatReceipt = some (hookCaller, hookQueries) ∧
          flatOutputs = [] := by
  cases flatReceipt with
  | complete fragment actual saved after =>
      obtain ⟨flatOutcome, actualHook, relatedHook⟩ := observed
      cases flatOutcome with
      | stopped _ _ _ => cases relatedHook
      | complete flatOutputs returned savedQueries =>
          obtain ⟨outputsRelated, callerSame, querySame⟩ := relatedHook
          subst returned
          subst savedQueries
          exact ⟨flatOutputs, outputsRelated, actualHook⟩
  | unhandled | rejected _ _ _ | stopped _ _ _ =>
      obtain ⟨outputsRelated, callerSame, querySame⟩ := observed
      have actualAdvance := SourceFlatPruningRecursive.advance_related _ receipt compared
      refine ⟨[], outputsRelated, ?_, rfl⟩
      rw [actualAdvance, advanced, callerSame, querySame]

'''
s=s[:a]+helpers+s[a:]
family='''
      (∀ (flat : FlatCached), EnumerationFlatCached.Related flat before →
        ∀ extra, ∃ flatFold,
          SourceFlatPruningNativeContinuations.run
            (SourceFlatPruningRecursive.continueWith
              (SourceFlatPruningRecursive.resume holeKey fits admits graph templates checkEmpty edgesOf
                stop order (bound + extra) recursiveFuel)
              graph templates stop order (bound + extra) metadata uv)
            checkEmpty (bound + extra) (bound + extra) (bound + extra)
            uv scs flat selectedEdges caller memos.query = flatFold ∧
          SourceFlatPruningNativeContinuations.ResultRelated SourceFlatPruningRecursive.OutputRelated
            SourceFlatPruningRecursive.FailureRelated flatFold result)'''
needle='          StoppedAt recursiveFuel formulas solver caller before uv seed scs capturedMass inherited processed.length outputs current) := by'
assert s.count(needle)==1;s=s.replace(needle,needle[:-len(' := by')]+' ∧'+family+' := by')
s=s.replace('fun _ => rfl, Post.refl packet.context, packet, bounded, known, Nat.le_refl _, ?_, ?_, .inl rfl⟩','fun _ => rfl, Post.refl packet.context, packet, bounded, known, Nat.le_refl _, ?_, ?_, .inl rfl, ?_⟩')
needle='''      · intro output member
        cases member
  | cons edge rest ih =>'''
replacement='''      · intro output member
        cases member
      · intro flat _related extra
        exact ⟨.complete [] [] caller memos.query, rfl, .nil, .nil, rfl, rfl⟩
  | cons edge rest ih =>'''
assert s.count(needle)==1;s=s.replace(needle,replacement)
s=s.replace('headRun, headPost, headQueries, admitted, pending, history, cacheBounds, headFits, headKnown, shape⟩ :=','headRun, headPost, headQueries, admitted, pending, history, cacheBounds, headFits, headKnown, shape, headFlat⟩ :=')
s=s.replace('SourcePruningEnumerationNativeHookResources.head_finite_complete_resources','SourceFlatPruningNativeHookResources.head_finite_complete_resources')
s=s.replace('⟨outcome, advanced, callbackRun, resources, captured⟩','⟨outcome, advanced, callbackRun, resources, captured, flatCallbackRun⟩')
s=s.replace('by simp, ?_, ?_, .inr ⟨_, rfl, .inl rfl, .inl rfl⟩⟩','by simp, ?_, ?_, .inr ⟨_, rfl, .inl rfl, .inl rfl⟩, ?_⟩')
needle='''        · intro output member
          cases member
      · have receiptCertificate'''
replacement='''        · intro output member
          cases member
        · intro flat related extra
          obtain ⟨flatReceipt, actualHead, compared⟩ := headFlat flat related extra
          have same : flatReceipt = .unhandled := by
            cases flatReceipt <;> simp only [SourceFlatPruningSelectedEdge.ResultRelated] at compared
            rfl
          subst flatReceipt
          refine ⟨.stopped [] [] (.edge (some .unhandled)), ?_, .nil, .nil, trivial⟩
          simp only [SourceFlatPruningNativeContinuations.run, actualHead,
            SourceFlatPruningNativeBranches.advance]
      · have receiptCertificate'''
assert s.count(needle)==1;s=s.replace(needle,replacement)
s=s.replace('tailRun, tailPost, tailCaptured, tailFits, tailKnown, tailLength, tailReceipts, tailOutputs, tailShape⟩ :=','tailRun, tailPost, tailCaptured, tailFits, tailKnown, tailLength, tailReceipts, tailOutputs, tailShape, tailFlat⟩ :=')
s=s.replace('              ?_, ?_, ?_⟩','              ?_, ?_, ?_, ?_⟩',1)
needle='''                  certificate.prepend hookPost headOutputs⟩
        | stopped headOutputs reason reached =>'''
flatContinued='''                  certificate.prepend hookPost headOutputs⟩
            · intro flat related extra
              let w := bound + extra
              have hl : headBound ≤ w := by dsimp [w, bound]; omega
              have tl : tailBound ≤ w := by dsimp [w, bound]; omega
              obtain ⟨flatReceipt, actualHead, comparedHead⟩ := headFlat flat related (w - headBound)
              rw [Nat.add_sub_of_le hl] at actualHead
              have actualHook := flatCallbackRun (w - headBound) flatReceipt comparedHead
              rw [Nat.add_sub_of_le hl] at actualHook
              obtain ⟨flatHeadOutputs, headOutputsRelated, flatContinued⟩ := continued_hook
                (SourceFlatPruningRecursive.continueWith
                  (SourceFlatPruningRecursive.resume holeKey fits admits graph templates checkEmpty edgesOf
                    stop order w recursiveFuel) graph templates stop order w metadata uv)
                receipt flatReceipt middleCaller hookCaller middleMemos.query hookQueries headOutputs
                advanced comparedHead actualHook
              obtain ⟨flatTail, actualTail, comparedTail⟩ := tailFlat flat related (w - tailBound)
              rw [Nat.add_sub_of_le tl, hookQuery] at actualTail
              let flatResult : SourceFlatPruningNativeContinuations.Result
                  (FlatOutput (bits + 2) Typing) (FlatFailure (bits + 2) Typing) (bits + 2) :=
                match (generalizing := false) flatTail with
                | .complete receipts later actual queries =>
                    .complete (flatReceipt :: receipts) (flatHeadOutputs ++ later) actual queries
                | .stopped receipts later current =>
                    .stopped (flatReceipt :: receipts) (flatHeadOutputs ++ later) current
              refine ⟨flatResult, ?_, ?_⟩
              · have running := SourceFlatPruningNativeContinuations.continued_head
                  (SourceFlatPruningRecursive.continueWith
                    (SourceFlatPruningRecursive.resume holeKey fits admits graph templates checkEmpty edgesOf
                      stop order w recursiveFuel) graph templates stop order w metadata uv)
                  checkEmpty w w w uv scs flat edge rest caller hookCaller memos.query hookQueries
                  flatReceipt flatHeadOutputs actualHead (by cases flatReceipt <;> exact flatContinued)
                rw [actualTail] at running
                cases flatTail <;> exact running
              · cases flatTail <;> cases tailResult <;>
                  simp only [SourceFlatPruningNativeContinuations.ResultRelated] at comparedTail <;> try contradiction
                case complete.complete flatProcessed flatOutputs flatCaller flatQueries
                    oldProcessed oldOutputs oldCaller oldQueries =>
                  obtain ⟨receipts, outputsRelated, callerSame, queriesSame⟩ := comparedTail
                  exact ⟨.cons comparedHead receipts, ordered_append headOutputsRelated outputsRelated,
                    callerSame, queriesSame⟩
                case stopped.stopped flatProcessed flatOutputs flatCurrent oldProcessed oldOutputs oldCurrent =>
                  obtain ⟨receipts, outputsRelated, current⟩ := comparedTail
                  exact ⟨.cons comparedHead receipts, ordered_append headOutputsRelated outputsRelated, current⟩
        | stopped headOutputs reason reached =>'''
assert s.count(needle)==1;s=s.replace(needle,flatContinued)
# Stop branch retains its entire existing output/certificate and appends actual flat stopping fold.
s=s.replace('              returnedFits.mono laterGrowth.1, ?_, by simp, ?_, ?_, ?_⟩','              returnedFits.mono laterGrowth.1, ?_, by simp, ?_, ?_, ?_, ?_⟩')
needle='''                receiptCertificate, currentResources⟩⟩

end MicroCFTA.SourceFlatPruningNativeFiniteSiblingResources'''
stopFlat='''                receiptCertificate, currentResources⟩⟩
            · intro flat related extra
              obtain ⟨flatReceipt, actualHead, comparedHead⟩ := headFlat flat related extra
              cases flatReceipt with
              | unhandled | rejected _ _ _ | stopped _ _ _ => cases comparedHead
              | complete flatFragment flatCaller flatQueries flatAfter =>
                  have retainedCompared := comparedHead
                  obtain ⟨rfl, rfl, rfl, _caches⟩ := comparedHead
                  obtain ⟨flatOutcome, actualHook, comparedHook⟩ :=
                    flatCallbackRun extra (.complete fragment actual queries flatAfter) retainedCompared
                  cases flatOutcome with
                  | complete _ _ _ => cases comparedHook
                  | stopped flatOutputs flatReason flatReached =>
                      obtain ⟨outputsRelated, reasonRelated, reachedSame⟩ := comparedHook
                      subst flatReached
                      refine ⟨.stopped [] flatOutputs
                        (.continuation (.complete fragment actual queries flatAfter) flatReason reached),
                        ?_, .nil, outputsRelated, retainedCompared, reasonRelated, rfl⟩
                      exact SourceFlatPruningNativeContinuations.stopped_hook
                        (SourceFlatPruningRecursive.continueWith
                          (SourceFlatPruningRecursive.resume holeKey fits admits graph templates checkEmpty edgesOf
                            stop order (headBound + extra) recursiveFuel)
                          graph templates stop order (headBound + extra) metadata uv)
                        checkEmpty (headBound + extra) (headBound + extra) (headBound + extra)
                        uv scs flat edge rest caller actual memos.query queries fragment flatAfter
                        flatOutputs flatReason reached actualHead actualHook

end MicroCFTA.SourceFlatPruningNativeFiniteSiblingResources'''
assert s.count(needle)==1;s=s.replace(needle,stopFlat)
# Add the original full finish wrapper, followed by the same final flat scan family.
finish=(repo/'SourcePruningEnumerationFiniteSiblingFinishResources.lean').read_text()
a=finish.index('/-- Retain the complete sibling result');finish=finish[a:finish.rindex('end MicroCFTA.SourcePruningEnumerationNativeFiniteSiblingResources')]
finish=finish.replace('SourcePruningEnumerationRecursive.Complete','SourceFlatPruningRecursive.Complete')
needle='        (SourcePruningEnumerationRecursive.finish uv result) := by'
assert finish.count(needle)==1;finish=finish.replace(needle,'        (SourcePruningEnumerationRecursive.finish uv result) ∧'+family+' := by')
finish=finish.replace('observed, post, captured, afterFits, afterKnown, processedLength, receipts, outputCertificates, shape⟩ :=','observed, post, captured, afterFits, afterKnown, processedLength, receipts, outputCertificates, shape, flatRunning⟩ :=')
finish=finish.replace('receipts, outputCertificates, shape, finished⟩','receipts, outputCertificates, shape, finished, flatRunning⟩')
s=s.replace('\nend MicroCFTA.SourceFlatPruningNativeFiniteSiblingResources','\n'+finish+'\nend MicroCFTA.SourceFlatPruningNativeFiniteSiblingResources')
p=out/'SourceFlatPruningRecursiveSiblingResources.lean';assert not p.exists();p.write_text(s)
# Entire old theorem prefixes are retained except the intentional stronger Complete name.
def header(t,name):a=t.index('theorem '+name);return t[a:t.index(' := by',a)]
def norm(t):return re.sub(r'\s+','',t.replace('SourcePruningEnumerationRecursive.Complete','SourceFlatPruningRecursive.Complete'))
assert norm(header(s,'alternatives_finite_complete_resources')).startswith(norm(header(old,'alternatives_finite_complete_resources')))
oldFinish=(repo/'SourcePruningEnumerationFiniteSiblingFinishResources.lean').read_text()
assert norm(header(s,'alternatives_finite_finish_resources')).startswith(norm(header(oldFinish,'alternatives_finite_finish_resources')))
print(p,len(p.read_bytes()),len(s.splitlines()),hashlib.sha256(p.read_bytes()).hexdigest())
