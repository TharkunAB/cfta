from pathlib import Path
import hashlib
repo=Path('/home/tritlo/Code/mcfta/lean/MicroCFTA')
out=Path('/tmp/mcfta-recursive-admission-20261027/ordinary-receipts-draft')
old=(repo/'SourcePruningEnumerationFiniteOrdinaryResources.lean').read_text()
context=old[old.index('namespace MicroCFTA.'):old.index('/-- Original ordinary inputs')].replace('local notation "Memos" => EndpointMemoGateTrace.Memos','local notation "Memos" => EndpointMemoGateTrace.Memos\nlocal notation "Queries" => SourceEndpointMemo.Memos\nlocal notation "Fragment" => Fragments.Fragment Symbol')
head=old[old.index('theorem ordinary_finite_complete_resources'):old.index(' := by',old.index('theorem ordinary_finite_complete_resources'))]
head=head.replace('theorem ordinary_finite_complete_resources','theorem ordinary_finite_complete_resources_with_invocations',1)
rich='''    (∀ extra (fragment : Fragment) (reached : Caller (bits + 2)) (saved : Queries) (after : Cached),
      SourcePruningEnumerationHookInvocation.OrdinaryInvocation
        (continueWith (resume holeKey fits admits graph templates checkEmpty edgesOf stop order
          (bound + extra) recursiveFuel) graph templates stop order (bound + extra) metadata uv)
        checkEmpty (bound + extra) (bound + extra) (bound + extra) (bound + extra) (bound + extra)
        uv edgesOf caller before memos.query fragment reached saved after →
      ∃ edge ∈ edgesOf (.node parentEntry storedEdges depth free),
        ∃ (headSeed : Seed) (headInventory : Inventory) (headCaller : Caller (bits + 2))
          (headMemos : Memos) (headBound : Nat) (returnedInventory : Inventory) (returnedMemos : Memos),
          Post formulas solver headInventory caller headCaller headMemos ∧
          SourcePruningEnumerationCapturedEdge.run checkEmpty
            (bound + extra) (bound + extra) (bound + extra) (bound + extra) (bound + extra)
            uv scs edge headCaller entered headMemos.query = some (.complete fragment reached saved after) ∧
          SourcePruningEnumerationNativeHookResources.CompletedHeadReceipt headSeed inherited formulas solver
            headInventory headCaller headMemos metadata entered checkEmpty uv scs edge headBound
            fragment reached saved after returnedInventory returnedMemos)'''
head=head+' ∧\n'+rich
proof=''' := by
  obtain ⟨ordinaryBound, entered, processed, outputs, afterCaller, next, final, result,
    entryRun, stable, counter, values, sameFlags, sameWaiting, enteredPacket,
    ordinaryRun, scanRun, post, captured, returnedFits, returnedKnown, processedLength,
    receipts, outputCertificates, shape, finished⟩ :=
    ordinary_finite_complete_resources holeKey fits admits graph templates checkEmpty edgesOf stop order metadata recursiveFuel
      seed formulas solver recursive inventory caller memos before uv handle scs parentEntry storedEdges depth free
      packet ready stored decoded selected incoming nonterminal bounded known selectionMembers selectionLength
      capturedMass inherited initialMass inheritedLength reserved
  have enteredStored : entered.core.values[uv]? = some (.unenumerated (some handle) scs) := by
    simpa only [values] using stored
  have enteredRoot : IsRoot entered.core.representatives uv :=
    (enteredPacket.safe.2 uv (.unenumerated (some handle) scs) enteredStored).mp (by intro impossible; cases impossible)
  have enteredReady : EnumerationDriver.Ready uv entered.core := by
    refine ⟨enteredPacket.safe, ?_, enteredRoot, ?_⟩
    · simpa only [counter] using ready.inside
    · intro node bucket current sc member sameClass
      have previous : before.core.values[uv]? = some (.unenumerated (some node) bucket) := by
        simpa only [values] using current
      exact ready.avoids node bucket previous sc member ((stable.classes uv sc.var).mp sameClass)
  have enteredIncoming : EnumerationReferences.IncomingAvoid uv entered.core :=
    EnumerationReferences.incoming_read uv before.core entered.core stable incoming
  have enteredMass : suspendedBound entered.core ≤ capturedMass := by
    rw [SourcePruningEnumerationPrefixAdmission.suspendedBound_values before.core entered.core values]
    exact initialMass
  have framed : EnumerationExpandableIndex.frame entered.core before = entered := by
    cases entered with
    | mk core expandable waiting =>
        simp only [EnumerationExpandableIndex.frame] at *
        congr 1
        · exact sameFlags.symm
        · exact sameWaiting.symm
  obtain ⟨receiptBound, rich⟩ :=
    SourcePruningEnumerationNativeFiniteSiblingResources.alternatives_finite_invocation_receipts
      holeKey fits admits graph templates checkEmpty edgesOf stop order metadata recursiveFuel
      seed formulas solver recursive inventory caller memos entered uv handle scs parentEntry storedEdges
      (edgesOf (.node parentEntry storedEdges depth free)) depth free enteredPacket enteredReady enteredStored decoded
      selected enteredIncoming bounded known selectionMembers selectionLength capturedMass inherited enteredMass inheritedLength reserved
  have entryAt (extra : Nat) : ExceptT.run (SourcePruningEnumerationEntry.enter caller.checked.native.machine.heap
      (ordinaryBound + receiptBound + extra) uv before.core) =
      [.ok ((uv, handle, scs, .node parentEntry storedEdges depth free), entered.core)] := by
    simpa only [Nat.add_assoc] using entryRun (receiptBound + extra)
  refine ⟨ordinaryBound + receiptBound, entered, processed, outputs, afterCaller, next, final, result,
    entryAt, stable, counter, values, sameFlags, sameWaiting, enteredPacket, ?_, ?_, post, captured,
    returnedFits, returnedKnown, processedLength, receipts, outputCertificates, shape, finished, ?_⟩
  · intro extra
    simpa only [Nat.add_assoc] using ordinaryRun (receiptBound + extra)
  · intro extra
    simpa only [Nat.add_assoc] using scanRun (receiptBound + extra)
  · intro extra fragment reached saved after ordinaryInvocation
    obtain ⟨target, readHandle, bucket, entry, rows, readDepth, references, readCore,
      observedEntry, _actualNonterminal, invocation⟩ := ordinaryInvocation
    have same := observedEntry.symm.trans (entryAt extra)
    simp only [List.cons.injEq, Except.ok.injEq, Prod.mk.injEq, Value.node.injEq,
      true_and, and_true] at same
    obtain ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl⟩ := same
    rw [framed] at invocation
    have actual := rich (ordinaryBound + extra) fragment reached saved after
    have common : receiptBound + (ordinaryBound + extra) = ordinaryBound + receiptBound + extra := by omega
    rw [common] at actual
    exact actual invocation

'''
recursive='''    (recursive : SourcePruningEnumerationRecursive.Complete (bits := bits) holeKey fits admits graph templates
      checkEmpty edgesOf stop order formulas solver recursiveFuel) '''
assert head.count(recursive)==1
finitehead=head.replace('theorem ordinary_finite_complete_resources_with_invocations','theorem ordinary_finite_complete_invocation_resources',1).replace(recursive,'    ')
finite='''/-- Original finite resources retain the full ordinary packet and each actual hook receipt. -/
'''+finitehead+''' := by
  exact ordinary_finite_complete_resources_with_invocations holeKey fits admits graph templates checkEmpty edgesOf stop order
    metadata recursiveFuel seed formulas solver
    (SourcePruningEnumerationRecursive.finite_complete holeKey fits admits graph templates checkEmpty edgesOf stop order
      formulas solver recursiveFuel)
    inventory caller memos before uv handle scs parentEntry storedEdges depth free packet ready stored decoded selected incoming
    nonterminal bounded known selectionMembers selectionLength capturedMass inherited initialMass inheritedLength reserved

'''
text='''import MicroCFTA.SourcePruningEnumerationFiniteOrdinaryResources
import MicroCFTA.SourcePruningEnumerationInvocationReceipts
import MicroCFTA.SourcePruningEnumerationOrdinaryInvocation
import MicroCFTA.SourcePruningEnumerationFiniteResources

/-!
# Rich actual hook receipts after ordinary entry

The original ordinary producer supplies one entered cache and its full packet.
The actual entry row identifies that cache on every ordinary invocation path.
Each head retains the actual caller and full memo state after earlier hooks.
-/
'''+context+'''/-- Keep the entire ordinary resource packet and add rich receipts at actual hook inputs. -/
'''+head+proof+finite+'end MicroCFTA.SourcePruningEnumerationNativeOrdinaryContinuations\n'
p=out/'SourcePruningEnumerationOrdinaryInvocationResources.lean';assert not p.exists();p.write_text(text);(out/'revisions/001-initial.lean').write_bytes(p.read_bytes())
print(str(p));print('lines',len(text.splitlines()),'bytes',p.stat().st_size,'SHA256',hashlib.sha256(p.read_bytes()).hexdigest())
