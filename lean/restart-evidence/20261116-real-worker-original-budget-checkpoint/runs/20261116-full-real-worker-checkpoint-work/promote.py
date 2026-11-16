from pathlib import Path
import gzip
import hashlib
import json

root = Path('/home/tritlo/Code/mcfta')
work = Path(__file__).parent
base = root / 'lean/restart-evidence'
run = base / '20261116-native-whole-real-nested-root-and-union-normal-check'
checks = json.loads((run / 'checks.json').read_text())
assert len(checks) == 3
assert all(c['exit'] == 0 and not c['nonstandard_axioms'] for c in checks)
assert checks[1]['total_axiom_reports'] == 1
assert checks[2]['total_axiom_reports'] == 136
sha = lambda data: hashlib.sha256(data).hexdigest()
pins = json.loads((run / 'source-pins.json').read_text())
for name, digest in pins.items():
    assert sha((root / name).read_bytes()) == digest, name
old_pins = json.loads(gzip.decompress((base / '20261116-real-task-flow-checkpoint/source-pins.json.gz').read_bytes()))
for name, digest in old_pins.items():
    if name.startswith('lean/MicroCFTA/'):
        assert sha((root / name).read_bytes()) == digest, name
owner = root / 'lean/MicroCFTA/SourcePruningEnumerationSharedEagerReservation.lean'
audit = root / 'lean/MicroCFTA/Audit.lean'
old_owner, old_audit = owner.read_bytes(), audit.read_bytes()
probes = (base / '20261116-real-worker-task-induction-checkpoint-work/WholeNestedRoot136Probes.lean.txt').read_bytes()
candidate = (run / 'candidate-0/MicroCFTA' / owner.name).read_bytes()
assert candidate.endswith(probes + b'\n')
new_owner = candidate[:-(len(probes) + 1)]
assert new_owner.count(old_owner) == 1
header = (base / '20261116-current-real-worker-full-resources-draft/PUBLIC-HEADER.lean.txt').read_bytes()
assert sha(header) == '549358aad6c1d3c04f55dbff2a5ab2a9cc61863082c0d955adbb0f293520b607'
assert new_owner.count(header) == 1
packet = base / '20261116-current-shared-incoming-union-normal-skipped-gate-repair'
module = root / 'lean/MicroCFTA/SourcePruningEnumerationSharedIncomingUnionNormal.lean'
raw = (packet / module.name).read_bytes()
assert sha(raw) == '646671cf186b2607543e1b28126b5ed612af9337d1584ce542c5e6b29d02aa6c'
assert not module.exists()
union_probes = (packet / 'PROBES.lean.txt').read_bytes()
public_probes = (base / '20261116-current-real-worker-full-resources-draft/PROBES-PUBLIC.lean.txt').read_bytes()
assert public_probes.count(b'#print axioms ') == 1
new_audit = b'import MicroCFTA.SourcePruningEnumerationSharedIncomingUnionNormal\n' + old_audit
new_audit += b'\n' + public_probes + b'\n' + union_probes
assert new_audit.count(old_audit) == 1
for name, data in [('BASE-OWNER.lean.txt', old_owner), ('BASE-AUDIT.lean.txt', old_audit),
                   ('ResourceProbes.lean.txt', probes), ('PUBLIC-HEADER.lean.txt', header)]:
    p = work / name
    assert not p.exists()
    p.write_bytes(data)
owner.write_bytes(new_owner)
module.write_bytes(raw)
audit.write_bytes(new_audit)
report = {'prior_checkpoint': '3329ad512b6af8c0f3da718224450e84d4cc7711',
          'private_run': run.name, 'owner_probes': 136, 'new_public_theorems': 2,
          'old_owner_and_audit_exact_blocks': True,
          'original_public_header_5493_exact': True,
          'original_algorithm_budgets_unchanged': True,
          'new_future_resource_or_model_provider': False,
          'whole_real_worker_resources_privately_checked': True,
          'all_emissions_before_stops_covered': True,
          'endpoint_resources_only_for_complete_returns': True,
          'joint_finite_completion_proved': False,
          'haskell_changed': False,
          'files': {str(p.relative_to(root)): sha(p.read_bytes()) for p in [owner, audit, module]}}
(work / 'PROMOTION.json').write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps(report))
