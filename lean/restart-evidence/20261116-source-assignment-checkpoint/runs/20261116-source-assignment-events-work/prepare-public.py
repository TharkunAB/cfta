from pathlib import Path
import ast
import hashlib
import json

work = Path(__file__).parent
root = work.parents[2]
base = work.parent
prior_work = base / '20261116-worker-origin-work'
specs = [
    ('SourceSynthesisCurrentRealDoneAssignment', '20261116-current-source-real-done-assignment-resource-projection-repair',
     '20261116-source-factory-resource-projection-check', 'source-factory', 1),
    ('SourceCurrentAllocatedNativeSourceCanonicalOldEntry', '20261116-current-source-canonical-old-entry-redundant-dsimp-repair',
     '20261116-source-factory-canonical-dsimp-strict-check', 'canonical-old-event', 1),
]
child = root / 'lean/MicroCFTA/SourcePruningEnumerationSharedChildNoneBuckets.lean'
if child.exists():
    child_promotion = json.loads((work / 'CHILD-PROMOTION.json').read_text())
    specs.append((child.stem, child_promotion['packet'], child_promotion['run'], 'actual-child-none', 1))
laws = [r['law'] for r in json.loads((work / 'OWNER-APPENDS.json').read_text())]
for module, folder, checked, name, count in specs:
    checks = json.loads((base / checked / 'checks.json').read_text())
    item = next(c for c in checks if c['name'] == name)
    assert item['exit'] == 0 and not item['nonstandard_axioms'] and item['total_axiom_reports'] == count
    assert (root / 'lean/MicroCFTA' / (module + '.lean')).read_bytes() == (base / folder / (module + '.lean')).read_bytes()
    probes = (base / folder / 'PROBES.lean.txt').read_text()
    extracted = [line.split()[2] for line in probes.splitlines() if line.startswith('#print axioms ')]
    assert len(extracted) == count
    laws.extend(extracted)
(work / 'ResourceProbes.lean.txt').write_bytes((prior_work / 'ResourceProbes.lean.txt').read_bytes())
script = (prior_work / 'prepare-invariant-publication-generated.py').read_text()
script = script.replace('20261116-worker-success-and-operands-check', '20261116-source-factory-resource-projection-check')
script = script.replace('20261116-worker-invariants-publication', '20261116-source-assignment-events-publication')
script = script.replace('20261116-shared-native-model-checkpoint', '20261116-worker-invariants-checkpoint')
script = script.replace('prefix=\'mcfta-native-worker-invariants-\'', 'prefix=\'mcfta-source-assignment-publication-\'')
changed = [r['owner'] for r in json.loads((work / 'OWNER-APPENDS.json').read_text())]
script = script.replace("changed={'lean/MicroCFTA/Audit.lean'}", "changed=" + repr(set(changed + ['lean/MicroCFTA/Audit.lean'])))
script = script.replace('assert unchanged==6137', 'assert unchanged==6151')
script = script.replace("assert (work/'BASE-OWNER.lean.txt').read_bytes() in owner.read_bytes()\n", '')
lines = script.splitlines(keepends=True)
for index, line in enumerate(lines):
    if line.startswith('modules='):
        modules = ast.literal_eval(line.split('=', 1)[1])
        lines[index] = 'modules=' + repr(modules + ['SourcePruningEnumerationPartialOutput'] + [s[0] for s in specs]) + '\n'
    elif line.startswith('laws='):
        original = ast.literal_eval(line.split('=', 1)[1])
        lines[index] = 'laws=' + repr(original + laws) + '\n'
    elif line.startswith("text='import "):
        imports = 'import MicroCFTA.SourcePruningEnumerationPartialOutput\n'
        imports += ''.join('import MicroCFTA.' + s[0] + '\n' for s in specs)
        lines[index] = 'text=' + repr(imports) + '\ntext+=' + line[len('text='):]
script = ''.join(lines)
for old, new in [('480', str(480 + len(laws))), ('6154', str(6154 + len(specs))),
                 ('5154', str(5154 + len(specs))), ('==75', '==' + str(75 + len(laws))),
                 ("'independent_reports':75", "'independent_reports':" + str(75 + len(laws))),
                 ("'new_public_theorems':38", "'new_public_theorems':" + str(len(laws))),
                 ("'old_non_audit_sources_byte_exact':6137", "'old_non_audit_sources_byte_exact':6151"),
                 ('1886de428b8c151e1ff335d09ffe41459239a448', 'be7969ef9fea1e01cf3c8aeaf58e30b3ec92c70f'),
                 ('FULL-INVARIANT-PUBLIC-API-COMPATIBILITY.json', 'PUBLIC-API-COMPATIBILITY.json')]:
    assert old in script, old
    script = script.replace(old, new)
script = script.replace("'actual_source_enter_closed_operands_proved':True,",
                        "'actual_source_enter_closed_operands_proved':True,'actual_source_current_assignment_factory_proved':True,'actual_canonical_old_entry_proved':True,'retained_core_obligations_guardsHold_proved':False,")
script += '''
for record in json.loads((work/'OWNER-APPENDS.json').read_text()):
    before=(work/('BASE-'+Path(record['owner']).name+'.txt')).read_bytes()
    assert hashlib.sha256(before).hexdigest()==record['owner_sha256']
    assert (root/record['owner']).read_bytes()==before+b'\\n'+(root/record['append']).read_bytes()
'''
(work / 'prepare-public-generated.py').write_text(script)
print(json.dumps({'new_modules': len(specs), 'new_reports': len(laws),
                  'expected_source_files': 6154 + len(specs), 'expected_reports': 480 + len(laws),
                  'independent_reports': 75 + len(laws)}))
