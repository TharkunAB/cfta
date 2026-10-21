import argparse
import hashlib
import json
import os
import re
import subprocess
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
FINAL = '924446496dd6d5fe0032bd703411d0dbdb5d5595e904d56516a2cb422e18f6da'
HEADS = ['MicroCFTA.SourceCurrentAllocatedNativeActualScope.word_ranges',
         'MicroCFTA.SourceCurrentAllocatedNativeActualScope.step']


def check(path, pin):
    data = path.read_bytes()
    assert len(data) == pin['bytes'] and hashlib.sha256(data).hexdigest() == pin['sha256'], path


def normalized(text):
    return re.sub(r'\s+', ' ', text).strip()


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--root', type=Path, required=True)
    parser.add_argument('--live', action='store_true')
    args = parser.parse_args()
    manifest = json.loads((HERE / 'review-manifest.json').read_text())
    assert manifest['finalized'] and manifest['independent_review']
    assert manifest['owned_lean_lake_commands'] == manifest['owned_public_pairs'] == 0
    for pin in manifest['files']:
        check(HERE / pin['path'], pin)
    assert json.loads((HERE / 'review-source-pins.json').read_text())['sources'] == manifest['sources']
    for pin in manifest['sources']:
        check(HERE / pin['snapshot'], pin)
        if args.live:
            check(args.root / pin['path'], pin)
    owner = HERE / 'inputs/owner'
    text = (owner / 'SourceCurrentAllocatedNativeActualScope.lean').read_text()
    assert hashlib.sha256(text.encode()).hexdigest() == FINAL and len(text.splitlines()) == 78
    assert re.findall(r'^theorem (\w+)', text, re.M) == ['word_ranges', 'step']
    assert not re.search(r'\b(?:sorry|axiom|admit|native_decide|trustCompiler)\b|_private', text)
    word = text.split('theorem word_ranges ', 1)[1].split(':=', 1)[0]
    step = text.split('theorem step ', 1)[1].split(':=', 1)[0]
    assert 'Trace fuel control before (.code (.pure value)) after' in word
    assert 'WordRanges control before' in word
    for token in ['SourceCurrentAllocatedTargetQuery.Step left right before result after',
                  'Good before', 'SemanticReady before.native.machine.heap',
                  'Scoped before.native', 'Idle before.native',
                  'Available before.native.machine.heap left', 'Available before.native.machine.heap right',
                  'left.free = []', 'right.free = []',
                  'Scoped after.native', 'Idle after.native', 'result.free = []']:
        assert token in step, token
    for token in ['Cap', 'PositiveAt', 'WordRanges', 'History', 'execute', 'Support']:
        assert token not in step, token
    for token in ['SourceCurrentAllocatedNativeScopeCompletion.initial_complete',
                  'actual.unique (.run receipt.trace)',
                  'Outcome.yielded.inj (one.symm.trans observed)',
                  'exact ih rest _ _ _ tail']:
        assert text.count(token) == 1, token
    earlier = (owner / 'actual-scope-direct-2.source.lean').read_text()
    assert earlier.replace('(scoped :', '(scopedCache :').replace(
        'before good scoped semantic', 'before good scopedCache semantic') == text
    ledger = json.loads((owner / 'actual-scope-attempt-ledger.json').read_text())['attempts']
    assert len(ledger) == 4 and sum(item['lean_launched'] for item in ledger) == 3
    infra = ledger[0]
    assert infra['name'] == 'actual-scope-direct-1' and not infra['lean_launched']
    assert infra['kind'] == 'infrastructure' and infra['exit_code'] == 1
    assert not (owner / 'actual-scope-direct-1.limits.json').exists()
    assert (owner / 'actual-scope-direct-1.log').read_text() == 'Failed to connect to bus: Operation not permitted\n'
    assert [(item['name'], item['exit_code']) for item in ledger[1:]] == [
        ('actual-scope-direct-2', 1), ('actual-scope-direct-3', 0), ('actual-scope-public-1', 0)]
    assert not (owner / 'actual-scope-direct-3.log').read_bytes()
    data = (owner / 'actual-scope-public-1.log').read_bytes()
    assert len(data) == 204263 and hashlib.sha256(data).hexdigest() == '260ef997c01c7ceecef2745b3c9a80def71a95f828a78ccae3e04619b42c9534'
    log = data.decode()
    assert not re.search(r'sorryAx|\b(?:warning|error)(?:\([^)]*\))?:|failed to pretty print|pp\.rawOnError|maximum recursion depth|maximum number of heartbeats|⋯|…|\.\.\.', log)
    printer = (owner / 'actual-scope-public-1.source.lean').read_text()
    for option in ['linter.all true', 'pp.explicit true', 'pp.fullNames true', 'pp.proofs true',
                   'pp.proofs.threshold 254', 'pp.universes true', 'pp.deepTerms true', 'pp.maxSteps 10000000']:
        assert printer.count('set_option ' + option) == 1
    for head in HEADS:
        checked, theorem = log.split('@' + head + ' :', 1)[1].split('\ntheorem ' + head, 1)
        typ, proof = theorem.split(' :=', 1)
        assert normalized(checked) == normalized(typ.removeprefix(' :'))
        assert '_private' not in checked + typ and len(proof) > 1000
        match = re.search(re.escape("'" + head + "' depends on axioms:") + r'\s*\[([^\]]*)\]', log)
        assert match
        assert {re.sub(r'\.\{[^}]*\}', '', name.strip()) for name in match.group(1).split(',')} == {
            'propext', 'Classical.choice', 'Quot.sound'}
    command = [sys.executable, str(owner / 'actual-scope-verify.py'), '--root', str(args.root)]
    if args.live:
        command.append('--live')
    result = subprocess.run(command, cwd='/', env=dict(os.environ, PYTHONDONTWRITEBYTECODE='1'),
                            capture_output=True, text=True)
    assert result.returncode == 0, (result.stdout, result.stderr)
    owner_result = json.loads(result.stdout)
    assert owner_result['status'] == 'PASS'
    assert owner_result['lean_jobs'] == 3 and owner_result['failed_checks'] == 1
    assert owner_result['infrastructure_attempts'] == 1 and owner_result['public_pairs'] == 2
    print(json.dumps({'status': 'PASS', 'live': args.live,
        'pins': len(manifest['files']) + len(manifest['sources']),
        'independent_review': True, 'material_issues': 0,
        'owned_lean_lake_commands': 0, 'owned_public_pairs': 0,
        'reused_lean_jobs': 3, 'reused_public_pairs': 2, 'reused_failures': 1,
        'reused_infrastructure_no_launch_attempts': 1,
        'full_public_log_bytes': len(data), 'all_eight_printer_settings': True,
        'public_type_readback_identical': True, 'standard_axioms_only': True,
        'frozen_owner_checker': owner_result}))


if __name__ == '__main__':
    main()
