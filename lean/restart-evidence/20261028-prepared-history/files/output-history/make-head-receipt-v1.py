from pathlib import Path
import hashlib,json,difflib
repo=Path('/home/tritlo/Code/mcfta/lean/MicroCFTA');own=Path('/tmp/mcfta-prepared-history-20261028/output-history')
old=(repo/'SourcePruningEnumerationHeadAdmission.lean').read_text();s=old.replace('import MicroCFTA.SourcePruningEnumerationFiniteHeadResources','import MicroCFTA.SourcePruningEnumerationPreparedFiniteHeadResources',1)
a=s.index('/-!');z=s.index('-/',a)+2;s=s[:a]+'''/-!
# Resource admission at an actual completed prepared head

The original stored handle and the actual prepared ordinary parent remain
separate. Both source indexes stay in the completed-head certificate.
One original prepared head producer supplies every old result field.
Each actual completion adds its own full input and returned resource receipt.
No source-to-prepared language equivalence is inferred from these inputs.
-/'''+s[z:]
s=s.replace('namespace MicroCFTA.SourcePruningEnumerationNativeHookResources','namespace MicroCFTA.SourcePruningEnumerationPreparedNativeHookResources').replace('end MicroCFTA.SourcePruningEnumerationNativeHookResources','end MicroCFTA.SourcePruningEnumerationPreparedNativeHookResources')
s=s.replace('open SourcePruningEnumerationRecursive (Packet Output Failure continueWith resume Complete OutcomeResources)','open SourcePruningEnumerationRecursive (Packet Output)\nopen SourcePruningEnumerationPreparedRecursive (Failure continueWith resume Complete OutcomeResources)')
s=s.replace('SourcePruningEnumerationFiniteReservation.step','SourcePruningEnumerationPreparedReservation.step').replace('SourcePruningEnumerationFiniteReservation.HeadReserved','SourcePruningEnumerationPreparedReservation.HeadReserved')
old_head='''    (uv : Nat) (scs : List Suspended) (edge : EdgeValue Symbol Constraint) : Prop where'''
new_head='''    (uv handle : Nat) (scs : List Suspended)
    (parentEntry : Cache.Interned InternedBinderProtocol.NodeKey)
    (storedEdges : List (EdgeValue Symbol Constraint)) (depth : Nat)
    (free : List InternedBinderProtocol.Reference) (edge : EdgeValue Symbol Constraint) : Prop where'''
assert old_head in s;s=s.replace(old_head,new_head,1)
a=s.index('  /-- The stored ordinary parent contains this exact edge. -/');z=s.index('  /-- The same input seed reserves',a)
s=s[:a]+'''  /-- The original captured slot retains its own stored handle and bucket. -/
  stored : before.core.values[uv]? = some (.unenumerated (some handle) scs)
  /-- The separately indexed prepared parent is available at this actual caller. -/
  parentAvailable : Available caller.checked.native.machine.heap (.node parentEntry storedEdges depth free)
  /-- The separately indexed prepared parent is closed. -/
  parentClosed : free = []
  /-- This actual prepared parent contains the selected edge. -/
  selected : edge ∈ storedEdges
'''+s[z:]
old_sig='''    (checkEmpty : Bool) (uv : Nat) (scs : List Suspended) (edge : EdgeValue Symbol Constraint)
    (bound : Nat)'''
new_sig='''    (checkEmpty : Bool) (uv handle : Nat) (scs : List Suspended)
    (parentEntry : Cache.Interned InternedBinderProtocol.NodeKey)
    (storedEdges : List (EdgeValue Symbol Constraint)) (depth : Nat)
    (free : List InternedBinderProtocol.Reference) (edge : EdgeValue Symbol Constraint)
    (bound : Nat)'''
assert old_sig in s;s=s.replace(old_sig,new_sig,1)
s=s.replace('  admission : HeadAdmission seed formulas solver inventory caller memos metadata before uv scs edge','  admission : HeadAdmission seed formulas solver inventory caller memos metadata before\n    uv handle scs parentEntry storedEdges depth free edge',1)
a=s.index('  /-- The reached caller fits');s=s[:a]+'''  /-- The same completed receipt retains its actual cache admission. -/
  admitted : Admitted uv (.complete fragment reached saved after)
  /-- The same completed receipt retains its pending references. -/
  pending : Pending (.complete fragment reached saved after)
  /-- The same completed receipt retains its fragment and dependency history. -/
  history : FragmentHistory before.core (.complete fragment reached saved after)
  /-- The same completed receipt retains its original allocation bounds. -/
  cacheBounds : HeadCacheBounds before scs (scalar seed.2) (guardWidth seed.1)
    (.complete fragment reached saved after)
'''+s[a:]
old_decoded='''    (decoded : lookupNode caller.checked.native.machine.heap handle = some (.node parentEntry storedEdges depth free))'''
new_decoded='''    (parentAvailable : Available caller.checked.native.machine.heap (.node parentEntry storedEdges depth free))
    (parentClosed : free = [])'''
assert old_decoded in s;s=s.replace(old_decoded,new_decoded,1)
s=s.replace('CompletedHeadReceipt seed inherited formulas solver inventory caller memos metadata before checkEmpty uv scs edge\n          bound', 'CompletedHeadReceipt seed inherited formulas solver inventory caller memos metadata before checkEmpty\n          uv handle scs parentEntry storedEdges depth free edge bound',1)
s=s.replace('packet ready stored decoded selected incoming bounded known selectionMembers selectionLength','packet ready stored parentAvailable parentClosed selected incoming bounded known selectionMembers selectionLength',1)
a=s.index('  have inputAdmission : HeadAdmission');z=s.index('  intro fragment reached queries after completed',a)
s=s[:a]+'''  have inputAdmission : HeadAdmission seed formulas solver inventory caller memos metadata before
      uv handle scs parentEntry storedEdges depth free edge := by
    obtain ⟨children, own⟩ := SourcePruningEnumerationRecursiveReservation.edge_shape_from_packet
      seed formulas solver inventory caller memos metadata before packet bounded known
      parentEntry storedEdges depth free parentAvailable edge selected
    have costBound := SourcePruningEnumerationRecursiveReservation.edge_cost_le seed inherited scs
      before.core.counter edge children own inheritedLength
    exact ⟨packet, ready, incoming, bounded, known, stored, parentAvailable, parentClosed,
      selected, reserved.edge costBound⟩
'''+s[z:]
old_refine='''  refine ⟨inputAdmission, actualPost, endpoint.2.symm,
    SourcePruningEnumerationRecursive.captured_post packet actualPost, afterPacket,
    ?_, ?_, supported.1, supported.2, actualRunning⟩'''
new_refine='''  refine ⟨inputAdmission, actualPost, endpoint.2.symm,
    SourcePruningEnumerationRecursive.captured_post packet actualPost, afterPacket,
    ?_, ?_, ?_, ?_, ?_, ?_, supported.1, supported.2, actualRunning⟩
  · simpa only [completed] using admitted
  · simpa only [completed] using pending
  · simpa only [completed] using history
  · simpa only [completed] using cacheBounds'''
assert old_refine in s;s=s.replace(old_refine,new_refine,1)
assert 'decoded' not in s
path=own/'drafts/head-receipt-v1/SourcePruningEnumerationPreparedHeadAdmission.lean';path.parent.mkdir();path.write_text(s)
(path.parent/'old-head-admission-to-prepared.diff').write_text(''.join(difflib.unified_diff(old.splitlines(keepends=True),s.splitlines(keepends=True),fromfile='old-HeadAdmission',tofile=path.name)))
b=path.read_bytes();status={'status':'UNTESTED','path':str(path),'bytes':len(b),'lines':b.count(b'\n'),'sha256':hashlib.sha256(b).hexdigest(),'runtime_definitions_added':0,'public_structures':['PreparedNativeHookResources.HeadAdmission','PreparedNativeHookResources.CompletedHeadReceipt'],'public_theorem':'PreparedNativeHookResources.head_finite_complete_resources_with_receipt','producer_calls':1,'source_parent_indices':'Original uv/handle/scs and actual prepared parentEntry/rows/depth/free/edge are separate explicit indexes','scope':'Entire original prepared finite head admission/result retained, then actual completed receipt with all original resource fields. No model/prepared-equivalence premise or conclusion.'};(own/'head-receipt-status-v1.json').write_text(json.dumps(status,indent=2)+'\n');print(json.dumps(status,indent=2))
