from pathlib import Path
import hashlib
import json

root = Path('/home/tritlo/Code/mcfta')
packet = root / 'lean/restart-evidence/20261116-real-opaque-terminal-expanded-birth-draft'
source = root / 'lean/MicroCFTA/SourcePruningEnumerationSharedEagerReservation.lean'
assert hashlib.sha256(source.read_bytes()).hexdigest() == 'd4dba9e0a86c4b5fe8d69e379aebe4614da5bb99d8d1d1bfe7c87e4544fe94e6'
text = source.read_text()
start = text.index('private theorem real_actual_opaque_terminal_held_history_at_any_budget')
proof = text[text.index(' := by', start):text.index('\n\n\nend ActualOpaqueTerminalHeldHistory', start)]
proof = proof.replace('''  have inputAvoids : Avoids before.core.representatives held scs := by
    intro sc member same
    exact isolated.incoming (.unenumerated (some handle) scs)
      (List.mem_of_getElem? stored) sc member same
''', '')
proof = proof.replace('''      exact actual_finalized_pending_child_held_fragment_history formulas solver caller reached metadata
        before middle finished scs fragment saved uv handle held heldHandle workFuel packet.safe pendingInputs
        isolated inputAvoids stored actual different finalized''',
    '''      exact actual_finalized_pending_child_expanded_birth_history formulas solver inventory caller reached
        memos metadata before middle finished uv handle workFuel scs fragment saved
        packet ready stored actual finalized''')
proof = proof.replace('''      have reachedRead := SourcePruningEnumerationNodes.lookupNode_keeps
        caller.checked.native.machine.heap reached.checked.native.machine.heap post.effects.keeps
        heldHandle heldValue decodedHeld
''', '')
proof = proof.replace('real_callback_held_fragment_history_of_depth_induction', 'real_callback_expanded_birth_history_of_depth_induction')
proof = proof.replace('''        selectionMembers selectionLength actualMass reserved.2 workFuel
        held heldHandle heldValue retained.isolated reachedRead boundary''',
    '''        selectionMembers selectionLength actualMass reserved.2 workFuel''')
proof = proof.replace('EnumerationDischargeHistory.HeldFragmentHistory.trans held heldHandle', 'ExpandedBirthHistory.trans')
proof = proof.replace('EnumerationDischargeHistory.HeldFragmentHistory held heldHandle', 'ExpandedBirthHistory')
tail = proof.index('  have resources := real_actual_opaque_terminal_resources_at_any_budget')
proof = proof[:tail] + '  exact histories\n'
assert all(token not in proof for token in ['heldHandle', 'decodedHeld', 'retained.isolated', 'workerIH'])
transport = ''' := by
  constructor
  · intro slot fragment stored
    have afterStored : after.values[slot]? = some (.enumerated fragment) := by
      rw [stable.values]
      exact stored
    exact ⟨congrArg (fun values => values[slot]?) stable.values,
      (enumerated_root after stable.safe slot fragment afterStored).2, stable.classes slot⟩
  · intro slot fragment stored
    exact Or.inl (by simpa only [stable.values] using stored)
'''
preamble = '''namespace MicroCFTA.SourcePruningEnumerationSharedEagerReservation
open EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationDependencies EnumerationReferences
open InternedConstructorTemplates InternedProbeProvenance
open SourcePruningEnumerationSharedSelectedContinuations
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentConstrainedCapGeneratedQueryResources (Fits)
open SourcePruningEnumerationSharedIncomingReservation (Seed advance)
open SourcePruningEnumerationRecursive (Packet)
open SourcePruningEnumerationSharedPreparedRecursive (Output Failure finish emitted)
open SourcePruningEnumerationSharedPreparedRecursiveChildPolicy (runEagerWithNarrow resumeWithNarrow)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Fragment" => Fragments.Fragment Symbol
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Metadata" => SourcePruningRecordTypes.Metadata
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Core" => EnumerationState.State Symbol Constraint
local notation "Heap" => SourceEqualityAnnotationHeap.Heap
set_option autoImplicit false
set_option maxHeartbeats 2000000
'''
context = '''
variable {Typing Key : Type} {bits : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
attribute [local irreducible] eagerReserved eagerFinal
attribute [local irreducible] SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.resumeWithNarrow
  SourcePruningEnumerationSharedPreparedRecursive.continueWith

'''
header = (packet / 'PRIVATE-HEADER.lean.txt').read_bytes()
assert hashlib.sha256(header).hexdigest() == '5437e2ebcbc2019eeb5e97862fc0433dca6bf938ae077e21c7c29cdb93dc8122'
transport_header = (packet / 'TRANSPORT-HEADER.lean.txt').read_bytes()
assert hashlib.sha256(transport_header).hexdigest() == '741a67add330c509f4f890eca661b69558125999e5380593a2d2aecdc2c0aae6'
(packet / 'PREAMBLE.lean.txt').write_text(preamble)
(packet / 'PROOF.lean.txt').write_text(proof)
(packet / 'TRANSPORT-PROOF.lean.txt').write_text(transport)
raw = preamble.encode() + b'\n' + transport_header + transport.encode() + context.encode() + header + proof.encode()
raw += b'\nend MicroCFTA.SourcePruningEnumerationSharedEagerReservation\n'
assert not (packet / 'APPEND.lean.txt').exists()
(packet / 'APPEND.lean.txt').write_bytes(raw)
(packet / 'PROBES.lean.txt').write_text(''.join('#check @MicroCFTA.SourcePruningEnumerationSharedEagerReservation.' + name + '\n#print axioms MicroCFTA.SourcePruningEnumerationSharedEagerReservation.' + name + '\n' for name in ['expanded_birth_history_of_renderStable', 'real_actual_opaque_terminal_expanded_birth_at_any_budget']))
(packet / 'NOTES.md').write_text('Status: UNCOMPILED. The actual opaque child/finalizer and callback prove strong birth history. The supplied numeric budgets and complete/stopped emissions are unchanged. The local resource IH is removed because the E proof does not use it. The genuine smaller-depth E IH remains. Rendering transport requires only its actual RenderStable receipt, which supplies Safe after. No future cut, model, or completion supplier is introduced.\n')
(packet / 'MANIFEST.sha256').write_text(''.join(hashlib.sha256(p.read_bytes()).hexdigest() + '  ' + p.name + '\n' for p in sorted(packet.iterdir()) if p.is_file() and p.name != 'MANIFEST.sha256'))
print(json.dumps({'append_sha256': hashlib.sha256(raw).hexdigest(), 'lines': len(raw.splitlines()), 'reports': 2}))
