import argparse
import hashlib
import json
import re
from pathlib import Path

HERE = Path(__file__).resolve().parent
SOURCE = 'SourceCurrentGatePublicationHistory.lean'
PREFIX = 'MicroCFTA.SourceCurrentGatePublicationHistory.'
HEADS = [PREFIX + name for name in ['primary', 'secondary']]


def sha(data):
    return hashlib.sha256(data).hexdigest()


def check(base, item):
    data = (base / item['path']).read_bytes()
    assert len(data) == item['bytes'] and sha(data) == item['sha256'], item['path']


parser = argparse.ArgumentParser()
parser.add_argument('--root', type=Path, default=Path('/home/tritlo/Code/mcfta'))
parser.add_argument('--live', action='store_true')
args = parser.parse_args()
manifest = json.loads((HERE / 'gate-publication-manifest.json').read_text())
for item in manifest['files']:
    check(HERE, item)
for item in manifest['sources']:
    check(HERE / 'inputs/root', item)
    if args.live:
        check(args.root, item)
assert json.loads((HERE / 'gate-publication-source-pins.json').read_text())['files'] == manifest['sources']
selection = json.loads((HERE / 'gate-publication-selection.json').read_text())
assert selection['finalized'] and selection['public_heads'] == HEADS
assert selection['lean_jobs'] == 3 and selection['infrastructure_attempts'] == 1
assert selection['strict_jobs'] == 2 and selection['public_jobs'] == 1
assert selection['failed_checks'] == 1 and selection['warning_checks'] == 0
assert selection['canonical_jobs'] == selection['constructed_pairs'] == 0
assert selection['new_public_pairs'] == 2 and not selection['unselected_successes']
source = (HERE / SOURCE).read_text()
assert sha(source.encode()) == selection['source_sha256']
assert source == (HERE / (selection['selected_strict'] + '.source.lean')).read_text()
assert len(source.splitlines()) == 208
assert re.findall(r'^theorem (\w+)', source, re.M) == ['primary', 'secondary']
assert not re.search(r'^(?:def|inductive|structure|axiom) |\bsorry\b|\badmit\b|native_decide|trustCompiler', source, re.M)
assert source.count('SourceCurrentRequiredPublicationHistory.unfold') == 2
assert source.count('Outcome.done.inj (done.symm.trans actual)') == 2
assert source.count('@ChildPost Symbol Guard edgeDec') == 2
assert source.count('@EdgesPost Symbol Guard edgeDec') == 2
assert source.count('SourcePrimaryGateEffects.child_effects') == source.count('SourcePrimaryGateEffects.path_effects') == 1
assert source.count('SourceCurrentSecondaryEffects.child_effects') == source.count('SourceCurrentSecondaryEffects.path_effects') == 1
ledger = json.loads((HERE / 'gate-publication-attempt-ledger.json').read_text())['attempts']
assert len(ledger) == 4
assert sum(item['lean_launched'] for item in ledger) == 3
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
    usage = json.loads((HERE / (stem + '.usage.json')).read_text())
    assert usage['age_seconds'] < 120 and usage['remaining_percent'] > 1
    if item['lean_launched']:
        assert json.loads((HERE / meta['limits']).read_text()) == {'memory.max': '4294967296', 'memory.high': '4294967296', 'memory.swap.max': '0'}
    else:
        assert stem == 'gate-publication-direct-1' and item['kind'] == 'infrastructure'
        assert not (HERE / meta['limits']).exists()
        assert log_path.read_bytes() == b'Failed to connect to bus: Operation not permitted\n'
assert not (HERE / (selection['selected_strict'] + '.log')).read_bytes()
assert 'typeclass instance problem is stuck' in (HERE / 'gate-publication-direct-2.log').read_text()
printer = (HERE / (selection['selected_public'] + '.source.lean')).read_text()
assert printer.startswith(source)
for option in ['linter.all true', 'pp.explicit true', 'pp.fullNames true', 'pp.proofs true', 'pp.proofs.threshold 254', 'pp.universes true', 'pp.deepTerms true', 'pp.maxSteps 10000000']:
    assert 'set_option ' + option in printer
for head in HEADS:
    for directive in ['#check @', '#print ', '#print axioms ']:
        assert printer.count(directive + head + '\n') == 1
log = (HERE / (selection['selected_public'] + '.log')).read_text()
assert len(log.encode()) == selection['public_log_bytes'] == 4966
assert not re.search(r'sorryAx|\b(?:warning|error)(?:\([^)]*\))?:|failed to pretty print|pp\.rawOnError|maximum recursion depth|maximum number of heartbeats|⋯|…|\.\.\.', log)
for head in HEADS:
    checked = log.split('@' + head + ' : ', 1)[1].split('\ntheorem ' + head + ' : ', 1)[0]
    printed = log.split('theorem ' + head + ' : ', 1)[1].split("'" + head + "'", 1)[0]
    typ, body = printed.split(':=', 1)
    assert re.sub(r'\s+', '', checked) == re.sub(r'\s+', '', typ), head
    assert typ.strip() and body.strip() and '_private' not in typ
    axioms = re.search(r"'" + re.escape(head) + r"' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)", log)
    assert axioms
    names = set() if axioms.group(1) is None else set(re.split(r',\s*', re.sub(r'\.\{[^}]*\}', '', axioms.group(1)).strip()))
    assert names <= {'propext', 'Classical.choice', 'Quot.sound'}, names
print(json.dumps({'status': 'PASS', 'pins': len(manifest['files']) + len(manifest['sources']), 'lean_jobs': 3, 'infrastructure_attempts': 1, 'failed_checks': 1, 'new_public_pairs': 2, 'constructed_pairs': 0, 'canonical_jobs': 0, 'live': args.live}))
