from pathlib import Path
import hashlib
import json

root = Path('/home/tritlo/Code/mcfta')
source = root / 'lean/MicroCFTA/SourcePruningEnumerationPrefixHeldHistoryAtOriginalBudget.lean'
assert hashlib.sha256(source.read_bytes()).hexdigest() == '5803fed477359f4129cded2294e58b0792c5081a3d08ff39184b0bee961ddb5f'
text = source.read_text()
packet = root / 'lean/restart-evidence/20261116-prefix-expanded-birth-history-draft'
header = (packet / 'PUBLIC-HEADER.lean.txt').read_text()
assert hashlib.sha256(header.encode()).hexdigest() == 'af0c882022c5db64f5ef15ccc737163dc354863f9ced2d1dbdc60eaead8b977b'
preamble = text[:text.index('private theorem frame_history')]
preamble = preamble.replace('import MicroCFTA.SourcePruningEnumerationPrefixIsolatedAtOriginalBudget\nimport MicroCFTA.SourcePruningEnumerationOpaqueSuffixIsolation',
    'import MicroCFTA.SourcePruningEnumerationPrefixHeldHistoryAtOriginalBudget\nimport MicroCFTA.EnumerationExpandedBirthHistory')
helpers = '''private theorem frame_birth_history
    {Guard : Type} (before after : EnumerationState.State Symbol Guard)
    (roots : ∀ (slot : Nat) (fragment : Fragments.Fragment Symbol), before.values[slot]? = some (.enumerated fragment) →
      IsRoot before.representatives slot)
    (frame : Frame before after) : ExpandedBirthHistory before after := by
  constructor
  · intro slot fragment stored
    refine ⟨congrArg (fun values => values[slot]?) frame.values, ?_, ?_⟩
    · obtain ⟨size, path⟩ := roots slot fragment stored
      exact ⟨size, (frame.reaches slot slot size).mpr path⟩
    · intro other
      exact SourcePruningEnumerationNativeLanguage.frame_sameClass before after frame slot other
  · intro slot fragment stored
    exact Or.inl (by simpa only [frame.values] using stored)

private theorem pending_write_birth_history
    {Guard : Type} (uv : Nat) (oldNode newNode : Option Nat)
    (oldScs newScs : List Suspended) (before after : EnumerationState.State Symbol Guard)
    (roots : ∀ (slot : Nat) (fragment : Fragments.Fragment Symbol), before.values[slot]? = some (.enumerated fragment) →
      IsRoot before.representatives slot)
    (stored : before.values[uv]? = some (.unenumerated oldNode oldScs))
    (written : Success (setValue uv (.unenumerated newNode newScs)) before () after) :
    ExpandedBirthHistory before after := by
  have origin := setValue_origin uv (.unenumerated newNode newScs) before after
    (by intro fragment impossible; cases impossible) written
  obtain rfl := (EnumerationDriver.modify_success _ before after).mp written
  refine ⟨?_, fun slot fragment expanded => Or.inl (origin slot fragment expanded)⟩
  intro slot fragment expanded
  have other : uv ≠ slot := by
    intro same
    subst slot
    cases Option.some.inj (stored.symm.trans expanded)
  exact ⟨by simp only [List.getElem?_set_ne other], roots slot fragment expanded, fun _ => Iff.rfl⟩

'''
check = text[text.index('private theorem check_repeated_history'):text.index('variable [DecidableEq (EdgeKey Symbol Constraint)]')]
check = check.replace('check_repeated_history', 'check_repeated_birth_history')
check = check.replace('(held heldHandle fuel uv handle : Nat)', '(fuel uv handle : Nat)')
check = check.replace('    (isolated : IsolatedPending held heldHandle before)\n', '')
check = check.replace('(ready : EnumerationDriver.Ready uv before) (different : uv ≠ held)', '(ready : EnumerationDriver.Ready uv before)')
check = check.replace('HeldFragmentHistory held heldHandle before after', 'ExpandedBirthHistory before after')
check = check.replace('HeldFragmentHistory.of_frame held heldHandle before after ready.safe isolated',
    'frame_birth_history before after\n        (fun slot fragment stored => (enumerated_root before ready.safe slot fragment stored).2)')
check = check.replace('HeldFragmentHistory.of_frame held heldHandle before resolved ready.safe isolated frame',
    'frame_birth_history before resolved\n              (fun slot fragment stored => (enumerated_root before ready.safe slot fragment stored).2) frame')
check = check.replace('''pending_write_history held heldHandle uv (some handle) (some handle)
                scs [] resolved cleared first.isolated
                (fun slot fragment expanded => (enumerated_root resolved resolvedSafe slot fragment expanded).2)
                different resolvedStored (Or.inl rfl) written''',
    '''pending_write_birth_history uv (some handle) (some handle)
                scs [] resolved cleared
                (fun slot fragment expanded => (enumerated_root resolved resolvedSafe slot fragment expanded).2)
                resolvedStored written''')
check = check.replace('HeldFragmentHistory.trans held heldHandle', 'ExpandedBirthHistory.trans')
prepared = text[text.index('variable [DecidableEq (EdgeKey Symbol Constraint)]'):text.index('/-- Every retained prefix core')]
prepared = prepared.replace('prepared_action_history', 'prepared_action_birth_history')
prepared = prepared.replace('(held heldHandle nativeFuel representativeFuel uv oldHandle : Nat)', '(nativeFuel representativeFuel uv oldHandle : Nat)')
prepared = prepared.replace('    (isolated : IsolatedPending held heldHandle checked)\n', '')
prepared = prepared.replace('    (different : uv ≠ held)\n', '')
prepared = prepared.replace('HeldFragmentHistory held heldHandle checked after', 'ExpandedBirthHistory checked after')
prepared = prepared.replace('frame_history held heldHandle checked after isolated roots', 'frame_birth_history checked after roots')
prepared = prepared.replace('frame_history held heldHandle checked resolved isolated roots frame', 'frame_birth_history checked resolved roots frame')
prepared = prepared.replace('''pending_write_history held heldHandle uv (some oldHandle) (some newHandle)
          scs scs resolved after first.isolated (frame_expanded_roots checked resolved roots frame)
          different resolvedStored (Or.inr rfl) writing''',
    '''pending_write_birth_history uv (some oldHandle) (some newHandle)
          scs scs resolved after (frame_expanded_roots checked resolved roots frame)
          resolvedStored writing''')
prepared = prepared.replace('HeldFragmentHistory.trans held heldHandle', 'ExpandedBirthHistory.trans')
start = text.index('theorem prefix_held_fragment_history_at_original_budget')
proof = text[text.index(' := by', start):]
proof = proof.replace('''  have different := packet_restart_ne formulas solver inventory caller memos metadata before
    held heldHandle uv value stop order packet isolated decoded boundary chosen
  refine ⟨different, ?_⟩
''', '')
proof = proof.replace('HeldFragmentHistory.of_frame held heldHandle before.core readAfter ready.safe isolated readFrame',
    'frame_birth_history before.core readAfter\n      (fun slot fragment stored => (enumerated_root before.core ready.safe slot fragment stored).2) readFrame')
proof = proof.replace('''check_repeated_history caller.checked.native.machine.heap
        held heldHandle workFuel uv oldHandle scs readAfter checked repeated readHistory.isolated
        readReady different readStored checkSuccess''',
    '''check_repeated_birth_history caller.checked.native.machine.heap
        workFuel uv oldHandle scs readAfter checked repeated
        readReady readStored checkSuccess''')
proof = proof.replace('''prepared_action_history holeKey fits admits metadata
                          held heldHandle workFuel workFuel uv oldHandle scs oldValue narrowedValue
                          caller.checked.native.machine.heap heap action checked observed checkedHistory.isolated
                          (wholeFrame.total ready.safe.1.total) checkedRoot checkedRoots different checkedStored''',
    '''prepared_action_birth_history holeKey fits admits metadata
                          workFuel workFuel uv oldHandle scs oldValue narrowedValue
                          caller.checked.native.machine.heap heap action checked observed
                          (wholeFrame.total ready.safe.1.total) checkedRoot checkedRoots checkedStored''')
proof = proof.replace('HeldFragmentHistory.trans held heldHandle', 'ExpandedBirthHistory.trans')
proof = proof.replace('HeldFragmentHistory held heldHandle', 'ExpandedBirthHistory')
raw = preamble + helpers + check + prepared + '/-- Every retained prefix core preserves all original expanded classes and fragment origins. -/\n' + header.rstrip('\n') + proof
assert 'heldHandle' not in raw
assert raw.count('theorem prefix_expanded_birth_history_at_original_budget') == 1
module = packet / 'SourcePruningEnumerationPrefixExpandedBirthHistory.lean'
assert not module.exists()
module.write_text(raw)
(packet / 'PROBES.lean.txt').write_text('#check @MicroCFTA.SourcePruningEnumerationSelectedStep.prefix_expanded_birth_history_at_original_budget\n#print axioms MicroCFTA.SourcePruningEnumerationSelectedStep.prefix_expanded_birth_history_at_original_budget\n')
(packet / 'NOTES.md').write_text('Status: UNCOMPILED. This normal module follows the actual runPrefix, representative, repeated check, pending write and configured preparation paths. Every original supplied workFuel is unchanged. No held-class, boundary or future-history premise is added. Its immutable original header was frozen before proof adaptation. The whole-worker birth proof remains open.\n')
(packet / 'MANIFEST.sha256').write_text(''.join(hashlib.sha256(p.read_bytes()).hexdigest() + '  ' + p.name + '\n' for p in sorted(packet.iterdir()) if p.is_file() and p.name != 'MANIFEST.sha256'))
print(json.dumps({'module': str(module), 'lines': len(raw.splitlines()), 'sha256': hashlib.sha256(raw.encode()).hexdigest()}))
