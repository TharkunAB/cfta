exec(compile(open('/tmp/mcfta-cluster-admission-root-common.py').read(), '/tmp/mcfta-cluster-admission-root-common.py', 'exec'))
import difflib
owner = Path('/tmp/mcfta-cluster-admission-boundary-declaration-v3')
review = Path('/tmp/mcfta-cluster-admission-boundary-declaration-v3-audit')
checked_package(owner, 'c30768e97936a9c3221b6b07df8c990db9f5688fe41bb0ef8b3c585ce97cea44', '422bbd43a0a10f3be994b1a432aac0239649ea65701c04d0b30f5cc3aa22aed3')
checked_package(review, 'dfe74f4be9b76718ffd8bd8e5eccb07c8dd8812f6486415c7e217dc95b29b4ad', 'bf9dc599f17c8fc5b8e24565dce348d5b059c7c3cd43983cd0605862cb503206')
assert load(review / 'review.json')['status'] == 'CLEAR'
old_plan = HERE / 'boundary-declaration-v2'
assert [name for name in load(owner / 'contracts.json') if (owner / name).read_bytes() != (old_plan / name).read_bytes()] == ['context.lean.txt']
assert (owner / 'ih-schema.lean.txt').read_bytes() == (old_plan / 'ih-schema.lean.txt').read_bytes()
for name, digest in load(owner / 'contracts.json').items():
    assert sha(owner / name) == digest
archive(owner, 'boundary-declaration-v3')
archive(review, 'boundary-declaration-v3-audit')
gate = load(HERE / 'root-boundary-declaration-v2-gate.json')
gate.update({'contracts_sha256': sha(owner / 'contracts.json'), 'independent_review_sha256': sha(review / 'review.json'), 'previous_root_gate_sha256': sha(HERE / 'root-boundary-declaration-v2-gate.json'), 'declaration_repair': 'Use public Prod.fst and Prod.snd functions only in the PairInputs notation. All other contracts and IH are unchanged.', 'body_authoring_authorized': True, 'compiler_activation_authorized': False})
save('root-boundary-declaration-v3-gate.json', gate)
destination = Path('/tmp/mcfta-cluster-admission-boundary-source-v3')
assert not destination.exists()
destination.mkdir()
before = (HERE / 'boundary-source-v2/SourceCurrentOriginalRowClusterAdmissionBoundary.lean').read_text()
first = (old_plan / 'context.lean.txt').read_text().rstrip('\n')
second = (owner / 'context.lean.txt').read_text().rstrip('\n')
assert before.count(first) == 1
after = before.replace(first, second)
assert len(after.splitlines()) == 199
source = destination / 'SourceCurrentOriginalRowClusterAdmissionBoundary.lean'
source.write_text(after)
(destination / 'repair.patch').write_text(''.join(difflib.unified_diff(before.splitlines(keepends=True), after.splitlines(keepends=True), fromfile='body-v2.lean', tofile='body-v3.lean')))
(destination / 'repair.md').write_text('The exact declaration V3 gate precedes this revision. Only the notation projections change to public Prod.fst and Prod.snd. Every remaining source byte, proof step and IH is unchanged. Strict1 and strict2 failed inputs and logs remain. No V3 compiler result is claimed.\n')
pins = [{'path': p.name, 'bytes': p.stat().st_size, 'sha256': sha(p)} for p in sorted(destination.iterdir())]
(destination / 'pins.json').write_text(json.dumps(pins, indent=2) + '\n')
(destination / 'FROZEN.json').write_text(json.dumps({'status': 'FROZEN_BODY_V3_PENDING_REVIEW', 'source_sha256': sha(source), 'pins_sha256': sha(destination / 'pins.json')}, indent=2) + '\n')
print(json.dumps({'status': 'DECLARATION_ACCEPTED_BEFORE_BODY_REVISION', 'source_sha256': sha(source), 'lines': 199, 'pins_sha256': sha(destination / 'pins.json'), 'frozen_sha256': sha(destination / 'FROZEN.json')}))
