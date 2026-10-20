import hashlib
import json
import re
import subprocess
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]


def read(name):
    return json.loads((HERE / name).read_text())


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def write(name, data):
    (HERE / name).write_text(json.dumps(data, indent=2) + '\n')


def checked(stem, empty=False):
    receipt = read(stem + '.json')
    assert receipt['exit_code'] == 0, stem
    assert read(stem + '.limits.json') == {'memory.max': '4294967296',
        'memory.high': '4294967296', 'memory.swap.max': '0'}
    usage = read(stem + '.usage.json')
    assert usage['age_seconds'] <= 600 and usage['remaining_percent'] > 1
    wrapper = receipt['wrapper']
    assert wrapper[wrapper.index('--mem') + 1] == '4G'
    assert wrapper[wrapper.index('--time') + 1] == '5m'
    if 'source' in receipt:
        assert sha(HERE / receipt['source']) == receipt['sha256']
    if empty:
        assert not (HERE / (stem + '.log')).read_bytes(), stem
    return receipt


sources = read('selected-sources.json')
for name, entry in sources.items():
    assert sha(ROOT / name) == entry['sha256'], name
for stem, module in [('history-strict-5', 'SourceCurrentOuterParentHistory'),
                     ('outer-selection-strict-1', 'SourceCurrentOuterOwnerSelection')]:
    assert checked(stem, True)['sha256'] == sources['lean/MicroCFTA/' + module + '.lean']['sha256']
fixture = HERE / 'warm-fixture/warm-owner-selection-kernels.lean'
assert checked('fixture-strict-1', True)['sha256'] == sha(fixture)

public = [
    ('history-public-2', ['MicroCFTA.SourceCurrentOuterParentHistory.' + name
       for name in ['Written', 'Origins', 'initial', 'edge_call', 'reached']]),
    ('outer-selection-public-2', ['MicroCFTA.SourceCurrentOuterOwnerSelection.selected']),
]
for stem, heads in public:
    receipt = checked(stem)
    printer = (HERE / receipt['source']).read_text()
    log = (HERE / (stem + '.log')).read_text()
    for setting in ['pp.explicit true', 'pp.fullNames true', 'pp.proofs true',
                    'pp.proofs.threshold 254', 'pp.universes true', 'pp.deepTerms true',
                    'pp.maxSteps 10000000']:
        assert 'set_option ' + setting in printer, (stem, setting)
    assert '-Dlinter.all=true' in receipt['command']
    for head in heads:
        for directive in ['#check @', '#print ', '#print axioms ']:
            assert printer.count(directive + head + '\n') == 1, head
        assert head in log and ':=' in log
    assert not re.search(r'sorryAx|\b(?:warning|error)(?:\([^)]*\))?:|failed to pretty print|pp\.rawOnError|maximum recursion depth|maximum number of heartbeats|⋯|…|\.\.\.', log), stem
    reports = re.findall(r'depends on axioms:\s*\[([^\]]*)\]', log)
    assert len(reports) == len(heads), stem
    for report in reports:
        assert set(re.split(r',\s*', re.sub(r'\.\{[^}]*\}', '', report).strip())) == {'propext', 'Classical.choice', 'Quot.sound'}

for stem in ['owner-selection-canonical-3', 'audit-2']:
    checked(stem)
    log = (HERE / (stem + '.log')).read_text()
    assert 'Build completed successfully' in log and not re.search(r'^error', log, re.M)
    assert all('InternedFreshOrdinaryClosedCompletion.lean' in warning
               for warning in re.findall(r'^warning:.*$', log, re.M))
audit = (HERE / 'audit-2.log').read_text()
assert '3551 jobs' in audit and '74404 MicroCFTA theorems' in audit
for item in read('components.json'):
    for arguments in [[], ['--live']]:
        subprocess.run(['/usr/bin/python3', str(HERE / item['path'] / item['verifier']), *arguments],
                       cwd='/', check=True, stdout=subprocess.DEVNULL)

historical = read('historical-review-snapshots.json')
for stem in ['mcfta-outer-parent-history-review', 'mcfta-outer-parent-owner-selection-review',
             'mcfta-outer-parent-owner-final-revision-review', 'mcfta-warm-owner-selection-fixture-review',
             'mcfta-selected-copy-support-plan']:
    pins = read(stem + '-source-pins.json')
    for entry in pins['files']:
        path = ROOT / entry['path'] if entry.get('base', 'ROOT') == 'ROOT' else HERE / Path(entry['path']).name
        if sha(path) != entry['sha256']:
            assert stem in ['mcfta-outer-parent-history-review', 'mcfta-outer-parent-owner-selection-review']
            assert entry['path'] == 'lean/MicroCFTA/SourceCurrentOuterParentHistory.lean'
            assert sha(HERE / historical[entry['sha256']]) == entry['sha256']
    if 'fixture' in pins:
        for entry in pins['fixture']['files']:
            assert sha(HERE / 'warm-fixture' / entry['path']) == entry['sha256']
    if 'report' in pins:
        assert sha(HERE / pins['report']['path']) == pins['report']['sha256']

preserved = json.loads(subprocess.check_output(['/usr/bin/python3', str(HERE / 'verify-preservation.py')], text=True))
write('preservation-final.json', preserved)
unique = {}
for path in HERE.rglob('*.json'):
    if 'previous-publication-support' in path.parts:
        continue
    try:
        receipt = json.loads(path.read_text())
    except ValueError:
        continue
    if (isinstance(receipt, dict) and isinstance(receipt.get('command'), list)
            and receipt['command'] and Path(receipt['command'][0]).name in ['lean', 'lake']
            and 'wrapper' in receipt and isinstance(receipt.get('exit_code'), int)):
        unique.setdefault(json.dumps(receipt, sort_keys=True), []).append(str(path.relative_to(HERE)))
account = {'actual_lean_lake_jobs': len(unique),
           'nonzero_lean_jobs': sum(json.loads(key)['exit_code'] != 0 for key in unique),
           'copies_add_jobs': False,
           'commands': [{'receipts': values, 'exit_code': json.loads(key)['exit_code']}
                        for key, values in unique.items()]}
write('attempt-accounting.json', account)
report = {'status': 'PASS', 'proof': (HERE / 'proof-commit.txt').read_text().strip(),
    'goal_status': 'active', 'new_public_theorems': 8, 'new_public_definitions': 2,
    'constructed_consumers': 1, 'audit_jobs': 3551, 'audit_dependencies': 74404,
    'baseline_files': preserved['baseline_files'], 'unchanged_haskell_files': preserved['unchanged_haskell_files'],
    **{key: value for key, value in account.items() if key != 'commands'}, 'completion_claimed': False}
write('verification.json', report)
print(json.dumps(report))
