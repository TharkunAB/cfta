import hashlib
import json
from pathlib import Path

plan = Path('/tmp/mcfta-group-admission-declaration-plan')
gate = Path('/tmp/mcfta-group-admission-root-declaration-gate.json')
assert json.loads(gate.read_bytes())['status'] == 'ACCEPTED_EXACT_DECLARATIONS_BEFORE_BODY'
owner = Path('/tmp/mcfta-group-admission-source-v1')
assert not owner.exists()
def fragment(name):
    return (plan / name).read_text().rstrip('\n')
source = fragment('context.lean.txt') + '\n\n' + fragment('public-header.lean.txt') + ' := by\n'
source += fragment('local-reversed.lean.txt') + ' := by\n'
source += '''    exact SourceCurrentPrependGrouping.iteration_reverse _ entries iteration
'''
source += fragment('fin-activation.txt') + '\n'
source += '''  · rw [start]
    exact ⟨current, admitted⟩
'''
source += fragment('successor-introduction.txt') + '\n'
source += fragment('obtain-packet.lean.txt') + '\n'
source += fragment('obtain-certificates.lean.txt') + '\n'
source += fragment('local-included.lean.txt') + ' := by\n'
source += '''      exact List.mem_map.mpr ⟨entries.get index, List.get_mem entries index, rfl⟩
'''
source += fragment('local-found.lean.txt') + ' := by\n'
source += '''      exact (reversed.lookup (entries.get index).1 (entries.get index).2.reverse).mp included
'''
source += fragment('local-contents.lean.txt') + ' := by\n'
source += '''      rw [SourceCurrentPrependGrouping.reverse_fromRows] at found
      exact ((SourceCurrentMergeGrouping.lookup_some
        (fun edge : Edge => edge.entry.key.symbol) (nodeEdges parent)
        (entries.get index).1 (entries.get index).2.reverse).mp found).2
    exact SourceCurrentOriginalRowClusterAdmission.completed_admitted inventory formulas solver
      bits parent member (entries.get index).1 initialDomains initialValid
      (states index.castSucc) sourceStable sourceGood sourceCurrent
      sourceSemantic sourceTrace sourceIdle sourceAdmitted room
      (fuels index) (kept index) (states index.succ)
      (by rw [← contents]; exact steps index)

end MicroCFTA.SourceCurrentOriginalRowGroupAdmission
'''
assert len(source.splitlines()) <= 180
owner.mkdir()
selected = owner / 'SourceCurrentOriginalRowGroupAdmission.lean'
selected.write_text(source)
(owner / 'root-declaration-gate.json').write_bytes(gate.read_bytes())
(owner / 'status.json').write_text(json.dumps(dict(status='SOURCE_ONLY_PENDING_COMPLETE_INDEPENDENT_BODY_REVIEW',
    lines=len(source.splitlines()), source_sha256=hashlib.sha256(selected.read_bytes()).hexdigest(),
    body_author='Root', headers_author='Guard', compiler_executed=False,
    default_limits=True, all_linters=True, whole_source_hard_stop=180), indent=2) + '\n')
pins = [dict(path=p.name, bytes=p.stat().st_size, sha256=hashlib.sha256(p.read_bytes()).hexdigest()) for p in sorted(owner.iterdir())]
(owner / 'pins.json').write_text(json.dumps(pins, indent=2) + '\n')
(owner / 'FROZEN.json').write_text(json.dumps(dict(status='FINAL_FROZEN_SOURCE_ONLY_V1',
    pins_sha256=hashlib.sha256((owner / 'pins.json').read_bytes()).hexdigest(), no_future_writes=True), indent=2) + '\n')
print((owner / 'status.json').read_text())
