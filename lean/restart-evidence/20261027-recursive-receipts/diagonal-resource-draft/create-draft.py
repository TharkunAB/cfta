from pathlib import Path
root=Path('/home/tritlo/Code/mcfta/lean/MicroCFTA')
out=Path('/tmp/mcfta-recursive-receipts-20261027/diagonal-resource-draft')
old=(root/'SourcePruningEnumerationCapturedEdgeDiagonalSoundness.lean').read_text()
resource=(root/'SourcePruningEnumerationCapturedEdgeResourceSoundness.lean').read_text()
context=old[old.index('namespace MicroCFTA.'):old.index('/-- Current source admission')].replace('variable {width : Nat}','variable {bits : Nat}')
start=resource.index('    (seed : SourcePruningEnumerationIncomingReservation.Seed)')
admission=resource[start:resource.index('    (canonical : Canonical before.core)',start)]
old_bridge=old[old.index('    {bound : Nat}',old.index('theorem stable_complete_of_diagonal')):old.index('/-- An actual diagonal completed family')]
old_bridge=old_bridge.replace('Caller width','Caller (bits + 2)')
old_bridge=old_bridge.replace('_pendingHistory, _shape⟩ :=','_pendingHistory, _shape, _returnedFits, _returnedKnown⟩ :=')
old_bridge=old_bridge.replace('    complete formulas solver','    complete_resources seed formulas solver')
old_bridge=old_bridge.replace('tries residual projected ranges','tries residual projected fits reserved known')
bridge='/-- Original resources identify independent completion bounds at the same actual diagonal endpoint. -/\ntheorem stable_complete_of_diagonal_resources\n'+admission+old_bridge
sound_head=resource[resource.index('    (seed : SourcePruningEnumerationIncomingReservation.Seed)'):resource.index(' := by',resource.index('theorem stable_complete_sound_current_resources'))]
old_observation=sound_head[sound_head.index('    {r n p h k : Nat}'):sound_head.index('    ∀ (ambient :')]
new_observation='''    {bound : Nat} {fragment : Fragment} {afterCaller : Caller (bits + 2)}
    {after : Cached} {savedQueries : Queries}
    (observed : ∀ extra,
      run checkEmpty (bound + extra) (bound + extra) (bound + extra) (bound + extra) (bound + extra)
        uv scs edge caller before memos.query = some (.complete fragment afterCaller savedQueries after)) :
'''
sound_head=sound_head.replace(old_observation,new_observation)
sound='''/-- Actual diagonal completion accepts the captured term under the existing current semantic gates. -/
theorem diagonal_complete_sound_current_resources
'''+sound_head+''' := by
  obtain ⟨r, n, p, h, k, running⟩ :=
    stable_complete_of_diagonal_resources seed formulas solver inventory caller before checkEmpty uv handle scs
      parentEntry edges depth free edge roots memos initial ready stored decoded realized selected
      paths counts flags pending allowed tries residual projected fits reserved known observed
  exact stable_complete_sound_current_resources seed formulas solver inventory caller before checkEmpty uv handle scs
    parentEntry edges depth free edge roots memos initial ready stored decoded realized selected
    paths counts flags pending allowed tries residual projected fits reserved known canonical nonterminal freshArity retained running

end MicroCFTA.SourcePruningEnumerationCapturedEdge
'''
text='''import MicroCFTA.SourcePruningEnumerationCapturedEdgeResourceSoundness

/-!
# Resource soundness from actual diagonal completion

Original input resources supply independent sufficient execution bounds.
An actual stable diagonal family identifies the same completed result.
The current semantic gates remain explicit.
-/
'''+context+bridge+sound
p=out/'SourcePruningEnumerationCapturedEdgeDiagonalResourceSoundness.lean';assert not p.exists();p.write_text(text)
(out/'revisions/001-initial.lean').write_bytes(p.read_bytes())
import hashlib
print(str(p));print('bytes',p.stat().st_size,'lines',len(text.splitlines()),'SHA256',hashlib.sha256(p.read_bytes()).hexdigest())
