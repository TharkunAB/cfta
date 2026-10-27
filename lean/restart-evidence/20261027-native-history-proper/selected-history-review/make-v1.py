from pathlib import Path
import hashlib,json
R=Path('/home/tritlo/Code/mcfta/lean/MicroCFTA');O=Path('/tmp/mcfta-native-history-proper-20261027/selected-history-review');D=O/'drafts/v1'
def declaration(file,name):
 s=(R/file).read_text();a=s.index('theorem '+name);b=s.index(' := by',a);return s[a:b]
def wrap_decl(file,name,new,observer):
 s=declaration(file,name).replace('theorem '+name,'theorem '+new,1)
 assert '      (∀ er' in s;s=s.replace('      (∀ er','      ((∀ er',1)
 return s+') ∧\n      ('+observer+') := by\n'
sel=(R/'SourcePruningEnumerationSelectedEdgeProper.lean').read_text();start=sel.index('namespace MicroCFTA.');end=sel.index('/-- Actual child descents')
prolog=sel[start:end];prolog=prolog.replace('variable {width : Nat}','variable {width : Nat}\nvariable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]')
sh=declaration('SourcePruningEnumerationSelectedEdgeProper.lean','complete_proper');sh=sh[:sh.index('    {r n p h k : Nat}')].replace('theorem complete_proper','theorem observed_cache_proper',1)
sh+='''    {r n p h k : Nat} {result : Result width}
    (observed : run checkEmpty r n p h k scs edge caller before memos.query = result) :
    match result with
    | .complete _ _ _ after | .rejected _ _ after => ProperState after.core
    | .stopped _ _ (some after) => ProperState after.core
    | _ => True := by
'''
a=sel.index('  obtain ⟨_action');b=sel.index('  simp only [run, ownRun] at completed',a);prefix=sel[a:b]
sp=prefix+'''  simp only [run, ownRun] at observed
  rw [readback] at observed
  cases childrenRun : SourcePruningEnumerationChildTraversal.run checkEmpty r n p h k
      inputs caller own memos.query with
  | stopped fragments observation candidate =>
      rw [childrenRun] at observed
      cases observed
      exact SourcePruningEnumerationChildTraversal.observed_cache_proper
        ownProperState inputsProper childrenRun
  | complete fragments reachedCaller saved reached =>
      rw [childrenRun] at observed
      cases observed
      exact finish_proper residual (.node edge.entry.key.symbol fragments) reached
        (SourcePruningEnumerationChildTraversal.complete_proper ownProperState inputsProper childrenRun)

'''
wrapper=wrap_decl('SourcePruningEnumerationSelectedEdgeResources.lean','complete_with_fragments_resources','complete_with_fragments_resources_proper','ProperState before.core → ValidSuspended scs → ProperState after.core')
wp='''  obtain ⟨r, n, p, h, k, afterCaller, after, savedQueries, final, next, afterRoots, result, packet⟩ :=
    complete_with_fragments_resources seed formulas solver inventory caller before checkEmpty
      parentEntry edges depth free edge scs roots memos initial parentAvailable parentClosed selected
      safe realized paths counts flags bounded pending allowed tries residual projected fits reserved known
  refine ⟨r, n, p, h, k, afterCaller, after, savedQueries, final, next, afterRoots, result, packet, ?_⟩
  intro proper inherited
  rcases packet with ⟨running, _post, _querySame, _growth, _afterPaths, _storage, _afterRealized,
    _afterCounts, _afterFlags, _origin, _retained, _protects, _pendingHistory, _incomingHistory,
    shape, _returnedFits, _returnedKnown⟩
  have actual : run checkEmpty r n p h k scs edge caller before memos.query = result := by
    simpa only [Nat.add_zero] using running 0 0 p h 0 (Nat.le_refl _) (Nat.le_refl _)
  have resultProper := observed_cache_proper caller before checkEmpty parentEntry edges depth free
    edge scs roots memos initial parentAvailable parentClosed selected safe realized paths counts flags
    bounded pending allowed tries residual projected proper inherited actual
  rcases shape with ⟨fragment, completed, _rest⟩ | ⟨fragments, outer, waiting, stopped⟩
  · simpa only [completed] using resultProper
  · simpa only [stopped] using resultProper

end MicroCFTA.SourcePruningEnumerationSelectedEdge
'''
seltext='''import MicroCFTA.SourcePruningEnumerationSelectedEdgeProper
import MicroCFTA.SourcePruningEnumerationTraversalEndpointProper
import MicroCFTA.SourcePruningEnumerationSelectedEdgeResources

/-!
# Proper storage at actual selected-edge endpoints

The own prefix supplies the actual child inputs and cache.
A stopped child retains its actual optional cache.
The complete original resource packet precedes the new proper-state observer.
-/
'''+prolog+'''/-- Actual complete and attached stopped results preserve proper pending paths. -/
'''+sh+sp+'''variable {bits : Nat}
open SourcePruningEnumerationIncomingReservation (Seed advance Reserved)
open SourceCurrentConstrainedCapGeneratedQueryResources (Fits)
local notation "Heap" => SourceEqualityAnnotationHeap.Heap

/-- Keep every original resource field and derive proper storage at its returned cache. -/
'''+wrapper+wp
(D/'SourcePruningEnumerationSelectedEdgeEndpointProper.lean').write_text(seltext)
cap=(R/'SourcePruningEnumerationCapturedEdgeProper.lean').read_text();a=cap.index('namespace MicroCFTA.');b=cap.index('/-- Actual captured-slot completion');cprolog=cap[a:b]
ch=declaration('SourcePruningEnumerationCapturedEdgeProper.lean','complete_proper');ch=ch[:ch.index('    {r n p h k : Nat}')].replace('theorem complete_proper','theorem observed_cache_proper',1)
ch+='''    {r n p h k : Nat} {result : Result width}
    (observed : run checkEmpty r n p h k uv scs edge caller before memos.query = some result) :
    match result with
    | .complete _ _ _ after | .rejected _ _ after => ProperState after.core
    | .stopped _ _ (some after) => ProperState after.core
    | _ => True := by
'''
a=cap.index('  obtain ⟨value, lookup');b=cap.index('  unfold run at completed',a);cp=cap[a:b]
cp+='''  unfold run at observed
  cases selectedRun : SourcePruningEnumerationSelectedEdge.run checkEmpty r n p h k
      scs edge caller before memos.query with
  | unhandled =>
      rw [selectedRun] at observed
      cases Option.some.inj observed
      trivial
  | rejected reachedCaller saved reached =>
      rw [selectedRun] at observed
      cases Option.some.inj observed
      exact SourcePruningEnumerationSelectedEdge.observed_cache_proper caller before checkEmpty
        parentEntry edges depth free edge scs roots memos initial available closed selected ready.safe
        realized paths counts flags bounded pending allowed tries residual projected proper inherited selectedRun
  | stopped fragments observation candidate =>
      rw [selectedRun] at observed
      cases Option.some.inj observed
      exact SourcePruningEnumerationSelectedEdge.observed_cache_proper caller before checkEmpty
        parentEntry edges depth free edge scs roots memos initial available closed selected ready.safe
        realized paths counts flags bounded pending allowed tries residual projected proper inherited selectedRun
  | complete fragment reachedCaller saved reached =>
      rw [selectedRun] at observed
      simp only [Option.map_eq_some_iff] at observed
      obtain ⟨finished, finishRun, fields⟩ := observed
      cases fields
      exact SourcePruningEnumerationFinalize.run_proper reachedCaller.checked.native.machine.heap k uv
        fragment reached finished
        (SourcePruningEnumerationSelectedEdge.complete_proper caller before checkEmpty parentEntry edges depth free
          edge scs roots memos initial available closed selected ready.safe realized paths counts flags bounded
          pending allowed tries residual projected proper inherited selectedRun) finishRun

'''
cwrap=wrap_decl('SourcePruningEnumerationCapturedEdgeResources.lean','complete_with_history_resources','complete_with_history_resources_proper','ProperState before.core → ProperState after.core')
cwp='''  obtain ⟨r, n, p, h, k, afterCaller, after, savedQueries, final, next, afterRoots, result, packet⟩ :=
    complete_with_history_resources seed formulas solver inventory caller before checkEmpty uv handle scs
      parentEntry edges depth free edge roots memos initial ready stored decoded realized selected paths counts
      flags pending allowed tries residual projected fits reserved known
  refine ⟨r, n, p, h, k, afterCaller, after, savedQueries, final, next, afterRoots, result, packet, ?_⟩
  intro proper
  rcases packet with ⟨running, _post, _querySame, _growth, _afterPaths, _storage, _afterRealized,
    _afterCounts, _afterFlags, _origin, _retained, _protects, _pendingHistory,
    shape, _returnedFits, _returnedKnown⟩
  have actual : run checkEmpty r n p h k uv scs edge caller before memos.query = some result := by
    simpa only [Nat.add_zero] using running 0 0 p h 0 (Nat.le_refl _) (Nat.le_refl _)
  have resultProper := observed_cache_proper formulas solver inventory caller before checkEmpty uv handle
    scs parentEntry edges depth free edge roots memos initial ready stored decoded realized selected paths
    counts flags pending allowed tries residual projected proper actual
  rcases shape with ⟨fragment, completed, _rest⟩ | ⟨fragments, outer, waiting, stopped⟩
  · simpa only [completed] using resultProper
  · simpa only [stopped] using resultProper

end MicroCFTA.SourcePruningEnumerationCapturedEdge
'''
captext='''import MicroCFTA.SourcePruningEnumerationCapturedEdgeProper
import MicroCFTA.SourcePruningEnumerationSelectedEdgeEndpointProper
import MicroCFTA.SourcePruningEnumerationCapturedEdgeResources

/-!
# Proper storage at actual captured-edge endpoints

The stored pending bucket supplies inherited validity.
A stopped result retains the actual cache without a finalizer write.
A complete result preserves proper storage through its same finalizer.
The complete original resource packet remains before the new observer.
-/
'''+cprolog+'''/-- Actual complete and attached stopped captured results preserve proper pending paths. -/
'''+ch+cp+'''variable {bits : Nat}
open SourcePruningEnumerationIncomingReservation (Seed advance Reserved)
open SourceCurrentConstrainedCapGeneratedQueryResources (Fits)
local notation "Heap" => SourceEqualityAnnotationHeap.Heap

/-- Keep every original captured resource field and derive proper storage at its actual cache. -/
'''+cwrap+cwp
(D/'SourcePruningEnumerationCapturedEdgeEndpointProper.lean').write_text(captext)
for f in D.glob('*.lean'):
 b=f.read_bytes();print(f,len(b.splitlines()),len(b),hashlib.sha256(b).hexdigest())
