import hashlib
import json
from pathlib import Path

plan = Path('/tmp/mcfta-rebuild-admission-declaration-plan')
gate = Path('/tmp/mcfta-rebuild-admission-root-declaration-gate.json')
assert json.loads(gate.read_bytes())['status'] == 'ACCEPTED_EXACT_DECLARATIONS_BEFORE_BODY'
owner = Path('/tmp/mcfta-rebuild-admission-source-v1')
assert not owner.exists()
def fragment(name):
    return (plan / name).read_text().rstrip('\n')
source = fragment('context.lean.txt') + '\n\n' + fragment('public-header.lean.txt') + ' := by\n'
source += fragment('body-prologue.txt') + '\n'
source += fragment('premise-introduction.txt') + '\n'
source += fragment('obtain-middle.lean.txt') + '\n'
source += '''    SourceCurrentOriginalRowGroupAdmission.groups_admitted inventory formulas solver
      bits (.node parentEntry parentRows parentDepth []) member entries iteration
      initialDomains initialValid before current admitted room fuels kept states start steps packets
      (Fin.last entries.length)
  exact ⟨⟨finalContextual, ⟨middleCurrent.covered.nodes, middleCurrent.covered.edges⟩,
    finalGrowth, finalHistory⟩, middleAdmitted⟩

end MicroCFTA.SourceCurrentOriginalRowRebuildAdmission
'''
assert len(source.splitlines()) <= 180
owner.mkdir()
selected = owner / 'SourceCurrentOriginalRowRebuildAdmission.lean'
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
