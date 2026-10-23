exec(compile(open('/tmp/mcfta-cluster-admission-root-common.py').read(), '/tmp/mcfta-cluster-admission-root-common.py', 'exec'))
import difflib
assert load(HERE / 'root-boundary-declaration-v2-gate.json')['body_authoring_authorized']
old_plan = HERE / 'boundary-declaration-plan'
new_plan = HERE / 'boundary-declaration-v2'
before = HERE / 'boundary-source-v1/SourceCurrentOriginalRowClusterAdmissionBoundary.lean'
owner = Path('/tmp/mcfta-cluster-admission-boundary-source-v2')
assert not owner.exists()
owner.mkdir()
old = before.read_text()
new = old
for name in ['context.lean.txt', 'local-parentAdmitted.lean.txt']:
    first = (old_plan / name).read_text().rstrip('\n')
    second = (new_plan / name).read_text().rstrip('\n')
    assert new.count(first) == 1
    new = new.replace(first, second)
assert new != old and len(new.splitlines()) == 199
path = owner / 'SourceCurrentOriginalRowClusterAdmissionBoundary.lean'
path.write_text(new)
(owner / 'repair.patch').write_text(''.join(difflib.unified_diff(old.splitlines(keepends=True), new.splitlines(keepends=True), fromfile='body-v1.lean', tofile='body-v2.lean')))
(owner / 'repair.md').write_text('The root accepted both exact declaration changes before this source revision. Only the PairInputs request constructor and parentAdmitted projection spelling change. Every tactic, proof call, premise, conclusion and induction remains unchanged. The original strict1 failure is retained. This source has no compiler acceptance yet.\n')
pins = [{'path': p.name, 'bytes': p.stat().st_size, 'sha256': sha(p)} for p in sorted(owner.iterdir())]
(owner / 'pins.json').write_text(json.dumps(pins, indent=2) + '\n')
(owner / 'FROZEN.json').write_text(json.dumps({'status': 'FROZEN_BODY_V2_PENDING_REVIEW', 'source_sha256': sha(path), 'pins_sha256': sha(owner / 'pins.json')}, indent=2) + '\n')
print(json.dumps({'source_sha256': sha(path), 'source_lines': 199, 'pins_sha256': sha(owner / 'pins.json'), 'frozen_sha256': sha(owner / 'FROZEN.json')}))
