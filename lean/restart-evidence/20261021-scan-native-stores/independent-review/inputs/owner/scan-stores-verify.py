import argparse
import hashlib
import json
import re
from pathlib import Path

HERE = Path(__file__).resolve().parent
SOURCE = 'SourceCurrentScanNativeStores.lean'
HEAD = 'MicroCFTA.SourceCurrentScanNativeStores.scan'


def sha(data):
    return hashlib.sha256(data).hexdigest()


def check(base, item):
    data = (base / item['path']).read_bytes()
    assert len(data) == item['bytes'] and sha(data) == item['sha256'], item['path']


parser = argparse.ArgumentParser()
parser.add_argument('--root', type=Path, default=Path('/home/tritlo/Code/mcfta'))
parser.add_argument('--live', action='store_true')
args = parser.parse_args()
manifest = json.loads((HERE / 'scan-stores-manifest.json').read_text())
for item in manifest['files']:
    check(HERE, item)
for item in manifest['sources']:
    check(HERE / 'inputs/root', item)
    if args.live:
        check(args.root, item)
assert json.loads((HERE / 'scan-stores-source-pins.json').read_text())['files'] == manifest['sources']
selection = json.loads((HERE / 'scan-stores-selection.json').read_text())
assert selection['finalized'] and selection['public_heads'] == [HEAD]
assert selection['lean_jobs'] == 3 and selection['infrastructure_attempts'] == 0
assert selection['strict_jobs'] == 2 and selection['public_jobs'] == 1
assert selection['failed_checks'] == 1 and selection['warning_checks'] == 0
assert selection['canonical_jobs'] == selection['constructed_pairs'] == 0
assert selection['new_public_pairs'] == 1 and not selection['unselected_successes']
source = (HERE / SOURCE).read_text()
assert sha(source.encode()) == selection['source_sha256']
assert source == (HERE / (selection['selected_strict'] + '.source.lean')).read_text()
assert len(source.splitlines()) == 296
assert re.findall(r'^theorem (\w+)', source, re.M) == ['scan']
assert not re.search(r'^(?:def|inductive|structure|axiom) |\bsorry\b|\badmit\b|native_decide|trustCompiler', source, re.M)
assert source.count('SourceCurrentNativeCurrentStores.step actualStep') == 1
assert source.count('SourceCurrentAllocatedNativeActualScope.step actualStep') == 1
assert source.count('SourceCurrentNativeOpenRequestResults.node_result') == 1
assert '⟨IntersectionEmptyDomain.emptyDomain,_,_⟩' in source
assert 'obtain ⟨natural, rfl, supportedPath⟩ := supportedPath' in source
assert 'SourceCurrentConstrainedCapProjectionGuard.forest Plain' in source
assert 'SecondaryProjectionHeap.forest_heap' not in source
assert 'Memo.Correct' not in source and 'WordRanges' not in source and 'SeededRanges' not in source
assert 'Cap Plain' not in source
assert source.count('SourceCurrentGatePublicationHistory.primary') == 4
assert source.count('SourceCurrentGatePublicationHistory.secondary') == 3
assert source.count('SourceCurrentConjunctionPublicationHistory.call') == 1
ledger = json.loads((HERE / 'scan-stores-attempt-ledger.json').read_text())['attempts']
assert len(ledger) == 3 and all(item['lean_launched'] for item in ledger)
for item in ledger:
    stem = item['name']
    meta_path = HERE / (stem + '.json')
    log_path = HERE / (stem + '.log')
    meta = json.loads(meta_path.read_text())
    assert sha(meta_path.read_bytes()) == item['receipt_sha256']
    assert sha(log_path.read_bytes()) == item['log_sha256']
    assert meta['exit_code'] == item['exit_code']
    assert meta['wrapper'][meta['wrapper'].index('--mem') + 1] == '4G'
    assert meta['wrapper'][meta['wrapper'].index('--time') + 1] == '5m'
    assert '-Dlinter.all=true' in meta['command']
    assert meta['command'][0].endswith('leanprover--lean4---v4.34.1/bin/lean')
    assert sha((HERE / meta['source']).read_bytes()) == meta['sha256']
    assert json.loads((HERE / meta['limits']).read_text()) == {'memory.max': '4294967296', 'memory.high': '4294967296', 'memory.swap.max': '0'}
    usage = json.loads((HERE / (stem + '.usage.json')).read_text())
    assert usage['age_seconds'] < 120 and usage['remaining_percent'] > 1
assert not (HERE / (selection['selected_strict'] + '.log')).read_bytes()
failed = (HERE / 'scan-stores-direct-1.log').read_text()
assert 'Too many variable names provided at alternative' in failed
assert 'Application type mismatch' in failed
printer = (HERE / (selection['selected_public'] + '.source.lean')).read_text()
assert printer.startswith(source)
for option in ['linter.all true', 'pp.explicit true', 'pp.fullNames true', 'pp.proofs true', 'pp.proofs.threshold 254', 'pp.universes true', 'pp.deepTerms true', 'pp.maxSteps 10000000']:
    assert 'set_option ' + option in printer
for directive in ['#check @', '#print ', '#print axioms ']:
    assert printer.count(directive + HEAD + '\n') == 1
log = (HERE / (selection['selected_public'] + '.log')).read_text()
assert len(log.encode()) == selection['public_log_bytes'] == 1247088
assert not re.search(r'sorryAx|\b(?:warning|error)(?:\([^)]*\))?:|failed to pretty print|pp\.rawOnError|maximum recursion depth|maximum number of heartbeats|⋯|…|\.\.\.', log)
checked = log.split('@' + HEAD + ' : ', 1)[1].split('\ntheorem ' + HEAD + ' : ', 1)[0]
printed = log.split('theorem ' + HEAD + ' : ', 1)[1].split("'" + HEAD + "'", 1)[0]
typ, body = printed.split(':=', 1)
assert re.sub(r'\s+', '', checked) == re.sub(r'\s+', '', typ)
assert typ.strip() and body.strip() and '_private' not in typ
axioms = re.search(r"'" + re.escape(HEAD) + r"' depends on axioms:\s*\[([^\]]*)\]", log)
assert axioms
names = set(re.split(r',\s*', re.sub(r'\.\{[^}]*\}', '', axioms.group(1)).strip()))
assert names <= {'propext', 'Classical.choice', 'Quot.sound'}, names
print(json.dumps({'status': 'PASS', 'pins': len(manifest['files']) + len(manifest['sources']), 'lean_jobs': 3, 'infrastructure_attempts': 0, 'failed_checks': 1, 'new_public_pairs': 1, 'constructed_pairs': 0, 'canonical_jobs': 0, 'live': args.live}))
