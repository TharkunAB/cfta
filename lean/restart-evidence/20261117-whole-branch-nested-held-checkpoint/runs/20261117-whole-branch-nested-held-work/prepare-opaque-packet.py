from pathlib import Path
import hashlib
import json

root = Path('/home/tritlo/Code/mcfta')
base = root / 'lean/restart-evidence'
packet = base / '20261117-whole-event-held-opaque-handler-draft'
packet.mkdir()
owner = root / 'lean/MicroCFTA/SourcePruningEnumerationSharedEagerReservation.lean'
source = owner.read_text()
old = source[source.index('private theorem real_outer_held_prepared_opaque\n'):]
old = old[:old.index('\nend MicroCFTA.SourcePruningEnumerationSharedEagerReservation')]
body = old[old.index('\n := by\n'):]
needle = '  subst target preparedHandle preparedScs\n'
assert body.count(needle) == 1
body = body.replace(needle, '''  have entryData :=
    SourcePruningEnumerationPreparationEntryInvariants.successful_preparation_entry_invariants
      workFuel workFuel uv target preparedHandle preparedScs caller before entered decoded value heap
      canonical packet.safe.1.total preparation
  subst target preparedHandle preparedScs
  have initialFacts : CanonicalTotal before.core := ⟨canonical, packet.safe.1.total⟩
  have entryFacts : CanonicalTotal entered := ⟨entryData.2.1, entryData.1⟩
  have bucketValid : ValidSuspended scs := entryData.2.2.1
''')
body = body[:body.index('  have tailPast :')]
body += '''  have finishedFacts : CanonicalTotal finished.core :=
    ⟨whole_event_canonical_opaque_complete checkEmpty workFuel workFuel workFuel workFuel workFuel
      uv scs value preparedCaller completedCaller cached finished memos.query saved fragment
      entryFacts.1 bucketValid completed,
    whole_event_forward_total cached.core finished.core entryFacts.2
      (whole_event_alias_opaque_complete checkEmpty workFuel workFuel workFuel workFuel workFuel
        uv scs value preparedCaller completedCaller cached finished memos.query saved fragment completed)⟩
  have callbackFacts := whole_event_callback_invariants graph templates workFuel uv metadata callbackMetadata
    fragment finished callbackCore finishedFacts recorded
  have tailFacts : ∃ tailEvents,
      JointOutputLedgerAt holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel
        recursiveDepth callbackMetadata completedCaller saved
        (EnumerationExpandableIndex.frame callbackCore finished)
        (SourcePruningEnumerationRestart.decision stop order callbackMetadata
          (EnumerationExpandableIndex.frame callbackCore finished)) index output tailEvents ∧
        EntriesHeld held heldHandle anchor tailEvents := by
    have atFinal := outerIH next completedCaller final (EnumerationExpandableIndex.frame callbackCore finished)
      callbackMetadata callbackSeed (ceiling + ceiling) callbackPacket callbackFacts.1 fitted alphabet
      selectionMembers selectionLength callbackMass callbackReserved workFuel held heldHandle heldValue anchor
      callbackPast completedHeldRead boundary
      (SourcePruningEnumerationRestart.decision stop order callbackMetadata
        (EnumerationExpandableIndex.frame callbackCore finished))
      index output rfl (by simpa only [query] using tail)
    simpa only [query] using atFinal
  obtain ⟨tailEvents, tailLedger, tailHeld⟩ := tailFacts
  let events : List (Operation Typing (bits + 2)) :=
    .prepare uv caller before uv handle scs decoded entered value heap ::
      .opaque uv scs value preparedCaller cached memos.query fragment completedCaller saved finished ::
      .recordTypes metadata uv fragment finished callbackMetadata callbackCore :: tailEvents
  have joint : JointPreparedLedgerAt holeKey fits admits graph templates checkEmpty edgesOf stop order
      workFuel recursiveDepth metadata uv caller memos.query before index output events :=
    .opaque preparation mode completed recorded initialFacts entryFacts bucketValid finishedFacts callbackFacts tailLedger
  refine ⟨events, joint, ?_⟩
  intro event member
  simp only [events, List.mem_cons] at member
  rcases member with same | same | same | tailMember
  · subst event
    exact past
  · subst event
    exact enteredPast
  · subst event
    exact finishedPast
  · exact tailHeld event tailMember
'''
header = (base / '20261117-whole-event-held-history-core-draft/OPAQUE-HEADER.lean.txt').read_text()
preamble = (base / '20261117-whole-event-held-history-core-draft/PREAMBLE.lean.txt').read_text()
preamble += '\nopen SourcePruningEnumerationSharedSelectedContinuations InternedProbeProvenance\n\n'
note = '''/- Note [One actual opaque operation]
The actual preparation supplies the entered Packet and canonical facts.
The completed operation supplies the final Packet and held history.
The callback supplies the same continuation cache and reservation.
The depth induction constructs one tail ledger with its entry protection.
The result uses that tail once and keeps every original operation endpoint.
-/

'''
append = preamble + note + header.rstrip() + body + '\nend MicroCFTA.SourcePruningEnumerationSharedEagerReservation\n'
files = {
    'OPAQUE-HEADER.lean.txt': header,
    'APPEND.lean.txt': append,
    'PROBES.lean.txt': '#check @MicroCFTA.SourcePruningEnumerationSharedEagerReservation.real_whole_event_held_prepared_opaque\n#print axioms MicroCFTA.SourcePruningEnumerationSharedEagerReservation.real_whole_event_held_prepared_opaque\n',
    'ORIGINAL-BODY.lean.txt': old,
}
for name, text in files.items():
    (packet / name).write_text(text)
sha = lambda data: hashlib.sha256(data).hexdigest()
(packet / 'source-pins.json').write_text(json.dumps({
    str(owner.relative_to(root)): sha(owner.read_bytes()),
    'lean/MicroCFTA/SourcePruningEnumerationWholeEventEntryProtection.lean':
        sha((root / 'lean/MicroCFTA/SourcePruningEnumerationWholeEventEntryProtection.lean').read_bytes())
}, indent=2) + '\n')
(packet / 'MANIFEST.sha256').write_text(''.join(
    sha(p.read_bytes()) + '  ' + p.name + '\n' for p in sorted(packet.iterdir()) if p.is_file()))
print(json.dumps({'packet': str(packet), 'append_sha256': sha(append.encode()),
                  'header_sha256': sha(header.encode()), 'lines': len(append.splitlines())}))
