from pathlib import Path
import ast
import json
import re

work = Path(__file__).parent
root = work.parents[2]
base = work.parent
previous = base / '20261116-source-assignment-events-work'
specs = [
    ('SourcePruningEnumerationSharedChildNoneBuckets', '20261116-current-real-child-none-source-match-repair',
     '20261116-child-none-source-match-check', 'actual-child-none'),
    ('SourcePruningEnumerationRealEagerParkedRawBucketReceipt', '20261116-current-real-eager-parked-raw-bucket-observer-boundary-repair',
     '20261116-full-none-domain-origin-eager-parked-check', 'eager-parked-receipt'),
    ('SourceCurrentAllocatedNativeSourceIssuedDomainEnterOrigin', '20261116-current-source-issued-domain-empty-key-projection-repair',
     '20261116-issued-domain-empty-projection-check', 'issued-domain-origin'),
]
whole = root / 'lean/MicroCFTA/SourcePruningEnumerationSharedEagerNoneBucketsWhole.lean'
if whole.exists():
    promotion = json.loads((work / 'WHOLE-NONE-PROMOTION.json').read_text())
    specs.append((whole.stem, promotion['packet'], promotion['run'], 'full-worker-none'))
laws = []
for module, folder, checked, name in specs:
    item = next(c for c in json.loads((base / checked / 'checks.json').read_text()) if c['name'] == name)
    assert item['exit'] == 0 and not item['nonstandard_axioms'] and item['total_axiom_reports'] == 1
    assert (root / 'lean/MicroCFTA' / (module + '.lean')).read_bytes() == (base / folder / (module + '.lean')).read_bytes()
    probes = (base / folder / 'PROBES.lean.txt').read_text()
    extracted = [line.split()[2] for line in probes.splitlines() if line.startswith('#print axioms ')]
    assert len(extracted) == 1
    laws.extend(extracted)
(work / 'ResourceProbes.lean.txt').write_bytes((previous / 'ResourceProbes.lean.txt').read_bytes())
script = (previous / 'prepare-public-generated.py').read_text()
script = script[:script.index('\nfor record in json.loads(')]
script = script.replace('20261116-source-assignment-events-publication', '20261116-eager-history-invariants-publication')
script = script.replace('20261116-worker-invariants-checkpoint', '20261116-source-assignment-checkpoint')
script = script.replace('prefix=\'mcfta-source-assignment-publication-\'', 'prefix=\'mcfta-eager-history-publication-\'')
lines = script.splitlines(keepends=True)
for index, line in enumerate(lines):
    if line.startswith('changed='):
        lines[index] = "changed={'lean/MicroCFTA/Audit.lean'}\n"
    elif line.startswith('modules='):
        modules = ast.literal_eval(line.split('=', 1)[1])
        lines[index] = 'modules=' + repr(modules + [s[0] for s in specs]) + '\n'
    elif line.startswith('laws='):
        original = ast.literal_eval(line.split('=', 1)[1])
        lines[index] = 'laws=' + repr(original + laws) + '\n'
    elif line.startswith("text='import "):
        imports = ''.join('import MicroCFTA.' + s[0] + '\n' for s in specs)
        lines[index] = 'text=' + repr(imports) + '\ntext+=' + line[len('text='):]
script = ''.join(lines)
for old, new in [('assert unchanged==6151', 'assert unchanged==6155'),
                 ('484', str(484 + len(laws))), ('6156', str(6156 + len(specs))),
                 ('5156', str(5156 + len(specs))), ('==79', '==' + str(79 + len(laws))),
                 ("'independent_reports':79", "'independent_reports':" + str(79 + len(laws))),
                 ("'new_public_theorems':4", "'new_public_theorems':" + str(len(laws))),
                 ("'old_non_audit_sources_byte_exact':6151", "'old_non_audit_sources_byte_exact':6155"),
                 ('be7969ef9fea1e01cf3c8aeaf58e30b3ec92c70f', 'ac3fed1766f805c7f355db1bb010d42d32cbf2c6')]:
    assert old in script, old
    script = script.replace(old, new)
script = script.replace("'full_worker_none_buckets_proved':False", "'full_worker_none_buckets_proved':" + repr(whole.exists()))
script = script.replace("'actual_source_current_assignment_factory_proved':True,",
                        "'actual_source_current_assignment_factory_proved':True,'actual_child_none_buckets_proved':True,'actual_issued_domain_origin_proved':True,'actual_eager_parked_receipt_proved':True,")
(work / 'prepare-public-generated.py').write_text(script)
print(json.dumps({'new_modules': len(specs), 'new_public_laws': len(laws),
                  'source_files': 6156 + len(specs), 'expected_reports': 484 + len(laws),
                  'independent_reports': 79 + len(laws), 'full_worker_none_proved': whole.exists()}))
