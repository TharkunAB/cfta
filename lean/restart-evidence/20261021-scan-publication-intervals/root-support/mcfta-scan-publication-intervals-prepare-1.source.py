import hashlib
import json
import shutil
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
def write(name, value):
    (HERE / name).write_text(json.dumps(value, indent=2) + '\n')
components = json.loads((HERE / 'components.json').read_text())
assert {item['path'] for item in components} == {'gate','conjunction','scope','independent-review','scope-review','scope-plan','scan-plan'}
config = [
    ('gate', 'gate-publication', 'SourceCurrentGatePublicationHistory',
     '45d8708558c1a35b9c9ddc1620724a7e8689afdaa486690b52840fdd3bce21ba'),
    ('conjunction', 'conjunction-history', 'SourceCurrentConjunctionPublicationHistory',
     '9890a1f02ff68e5edba49bfc3cbbbaef15013b6e6f811413ac10ca83bb0966a2'),
    ('scope', 'actual-scope', 'SourceCurrentAllocatedNativeActualScope',
     '924446496dd6d5fe0032bd703411d0dbdb5d5595e904d56516a2cb422e18f6da'),
]
sources, frozen, checks = {}, {}, {}
for tag, prefix, module, expected in config:
    selection = json.loads((HERE / tag / (prefix + '-selection.json')).read_text())
    name = 'lean/MicroCFTA/' + module + '.lean'
    digest = hashlib.sha256((ROOT / name).read_bytes()).hexdigest()
    assert digest == selection['source_sha256'] == expected
    sources[name] = {'sha256': digest}
    frozen[module] = digest
    checks[tag] = {'strict': tag + '-strict-1', 'public': tag + '/' + selection['selected_public']}
write('selected-sources.json', sources)
write('frozen-modules.json', frozen)
write('selected-checks.json', {**checks, 'audit': 'audit-1'})
previous = HERE / 'previous-publication-support'
previous.mkdir()
for pattern in ['mcfta-native-query-stores-publication.json', 'mcfta-native-query-stores-final-publication*',
                'mcfta-native-query-stores-final-push.log', 'mcfta-native-query-stores-final-remote.txt',
                'mcfta-native-query-stores-board-readback.json', 'mcfta-native-query-stores-seal-1.*',
                'mcfta-native-query-stores-support-*.json','mcfta-native-query-stores-support-*.log',
                'mcfta-native-query-stores-support-*.limits.json','mcfta-native-query-stores-support-*.peaks.txt',
                'mcfta-native-query-stores-support-*.source.py','mcfta-native-query-stores-support-*.usage.json']:
    found = [path for path in Path('/tmp').glob(pattern) if path.is_file()]
    assert found, pattern
    for source in found:
        shutil.copyfile(source, previous / source.name)
print(json.dumps({'status': 'PASS', 'components': len(components), 'new_modules':len(config)}))
