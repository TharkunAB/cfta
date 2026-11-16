from pathlib import Path
import ast
import hashlib
import json

work = Path(__file__).parent
root = work.parents[2]
base = work.parent
specs = [
    ('SourcePruningEnumerationRecordTypesValues', '20261116-current-record-types-values-core-binders-repair',
     '20261116-whole-worker-repair-callback-and-prefix-check', 'callback-values', 5),
    ('SourcePruningEnumerationPreparationNoneBuckets', '20261116-current-real-preparation-none-buckets-draft',
     '20261116-worker-constructor-and-source-origins-check', 'preparation-none', 2),
    ('SourcePruningEnumerationSharedEagerUnionNormalWhole', '20261116-current-real-worker-union-normal-whole-success-reduction-repair',
     '20261116-worker-success-and-operands-check', 'whole-worker-U', 1),
    ('SourceCurrentAllocatedNativeSourceEmptyEnterOperands', '20261116-current-stored-dispatch-empty-enter-operands-case-transport-repair',
     '20261116-worker-success-and-operands-check', 'source-operands', 1),
    ('SourcePruningEnumerationRealPrefixNoneBuckets', '20261116-current-real-prefix-none-unit-match-repair',
     '20261116-prefix-unit-match-check', 'real-prefix-none', 1),
]
full = 'SourceCurrentAllocatedNativeSourceEnterFullOperands'
if (root / 'lean/MicroCFTA' / (full + '.lean')).exists():
    specs.append((full, '20261116-current-source-old-new-enter-full-operands-draft',
                  '20261116-source-enter-full-operands-check', 'source-full-operands', 1))
laws = []
for module, folder, checked, name, count in specs:
    checks = json.loads((base / checked / 'checks.json').read_text())
    item = next(c for c in checks if c['name'] == name)
    assert item['exit'] == 0 and not item['nonstandard_axioms']
    assert item['total_axiom_reports'] == count
    source = root / 'lean/MicroCFTA' / (module + '.lean')
    frozen = base / folder / (module + '.lean')
    assert source.read_bytes() == frozen.read_bytes(), module
    probes = (base / folder / 'PROBES.lean.txt').read_text()
    extracted = [line.split()[2] for line in probes.splitlines() if line.startswith('#print axioms ')]
    assert len(extracted) == count
    laws.extend(extracted)

script = (work / 'prepare-public.py').read_text()
script = script.replace('20261116-worker-cps-typed-reduction-check', '20261116-worker-success-and-operands-check')
script = script.replace('20261116-worker-origins-publication', '20261116-worker-invariants-publication')
script = script.replace('prefix=\'mcfta-real-worker-task-publication-\'', 'prefix=\'mcfta-native-worker-invariants-\'')
lines = script.splitlines(keepends=True)
for index, line in enumerate(lines):
    if line.startswith('modules='):
        modules = ast.literal_eval(line.split('=', 1)[1])
        lines[index] = 'modules=' + repr(modules + [s[0] for s in specs]) + '\n'
    elif line.startswith('laws='):
        original = ast.literal_eval(line.split('=', 1)[1])
        lines[index] = 'laws=' + repr(original + laws) + '\n'
    elif line.startswith("text='import "):
        imports = ''.join('import MicroCFTA.' + s[0] + '\n' for s in specs)
        lines[index] = 'text=' + repr(imports) + '\ntext+=' + line[len('text='):]
script = ''.join(lines)
for old, new in [('469', str(469 + len(laws))), ('6148', str(6148 + len(specs))),
                 ('5148', str(5148 + len(specs))), ('==64', '==' + str(64 + len(laws))),
                 ("'independent_reports':64", "'independent_reports':" + str(64 + len(laws))),
                 ("'new_public_theorems':27", "'new_public_theorems':" + str(27 + len(laws))),
                 ("'full_worker_union_normal_proved':False", "'full_worker_union_normal_proved':True"),
                 ('PUBLIC-API-COMPATIBILITY.json', 'FULL-INVARIANT-PUBLIC-API-COMPATIBILITY.json')]:
    assert old in script, old
    script = script.replace(old, new)
script = script.replace("'actual_empty_root_singleton_parent_proved':True,",
                        "'actual_empty_root_singleton_parent_proved':True,'actual_source_enter_closed_operands_proved':True,")
(work / 'prepare-invariant-publication-generated.py').write_text(script)
print(json.dumps({'additional_modules': len(specs), 'additional_reports': len(laws),
                  'expected_source_files': 6148 + len(specs), 'expected_audit_reports': 469 + len(laws),
                  'expected_independent_reports': 64 + len(laws)}))
