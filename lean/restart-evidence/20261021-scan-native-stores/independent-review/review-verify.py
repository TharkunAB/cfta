import argparse
import hashlib
import json
import os
import re
import subprocess
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
SOURCE = 'SourceCurrentScanNativeStores.lean'
FINAL = '1c92862363f0484d5cedb052e90c3b969eeb6d414bf7777ad2e516675625b77e'
HEAD = 'MicroCFTA.SourceCurrentScanNativeStores.scan'


def check(path, pin):
    data = path.read_bytes()
    assert len(data) == pin['bytes']
    assert hashlib.sha256(data).hexdigest() == pin['sha256'], path


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
    source = (owner / SOURCE).read_text()
    assert hashlib.sha256(source.encode()).hexdigest() == FINAL
    assert len(source.splitlines()) == 296
    assert re.findall(r'^theorem (\w+)', source, re.M) == ['scan']
    assert not re.search(r'\b(?:sorry|axiom|admit|native_decide|trustCompiler)\b|_private', source)
    previous = (HERE / 'inputs/prelaunch/SourceCurrentScanNativeStores.lean.txt').read_text()
    assert previous.replace('| force result heap projected =>', '| force heap projected =>').replace(
        'have resident := SourceCurrentNativeOpenRequestResults.node_result _ _ _ _ _ tail.ready.good.native native',
        'have resident := SourceCurrentNativeOpenRequestResults.node_result _ ⟨IntersectionEmptyDomain.emptyDomain,_,_⟩ _ _ _\n        tail.ready.good.native native') == source
    public = source.split('\ntheorem scan\n', 1)[1].split(':=', 1)[0]
    for token in ['Scan budget unconstrained reaches values classes before memo outcome selected after saved',
                  'Ready before', 'Values before.native.machine.heap values',
                  'proper : ∀ paths ∈ classes, ∀ path ∈ paths, path ≠ []',
                  'Current before', 'Support before.native.machine.heap before.native',
                  'History empty before.native.machine.heap', 'Ready after',
                  'Effects (physical before) (physical after)',
                  'Extension before.native.machine after.native.machine',
                  'Values after.native.machine.heap values', 'Current after',
                  'Support after.native.machine.heap after.native',
                  'Nonempty (History empty after.native.machine.heap)']:
        assert token in public, token
    for token in ['Cap', 'Memo.Correct', 'WordRanges', 'PositiveAt', 'closed', 'FoldRanges']:
        assert token not in public, token
    for token in ['SourceCurrentNativeCurrentStores.step actualStep',
                  'SourceCurrentAllocatedNativeActualScope.step actualStep',
                  'SourceCurrentNativeOpenRequestResults.node_result',
                  'SourceCurrentConstrainedCapProjectionGuard.forest Plain projected',
                  'obtain ⟨natural, rfl, supportedPath⟩ := supportedPath',
                  'SourceCurrentConjunctionPublicationHistory.call actual initial available']:
        assert source.count(token) == 1, token
    assert 'SourceEqualityAnnotationHeap' not in source
    assert 'SecondaryProjectionHeap.forest_heap' not in source
    assert not (owner / 'scan-stores-direct-2.log').read_bytes()
    data = (owner / 'scan-stores-public-1.log').read_bytes()
    assert len(data) == 1247088
    assert hashlib.sha256(data).hexdigest() == 'f606138fdb4b8d5ebf0099614bd365f9dee9efca6642e438abd1bb3d62febc0d'
    log = data.decode()
    assert not re.search(r'sorryAx|\b(?:warning|error)(?:\([^)]*\))?:|failed to pretty print|pp\.rawOnError|maximum recursion depth|maximum number of heartbeats|⋯|…|\.\.\.', log)
    printer = (owner / 'scan-stores-public-1.source.lean').read_text()
    assert printer.startswith(source)
    for option in ['linter.all true', 'pp.explicit true', 'pp.fullNames true', 'pp.proofs true',
                   'pp.proofs.threshold 254', 'pp.universes true', 'pp.deepTerms true', 'pp.maxSteps 10000000']:
        assert printer.count('set_option ' + option) == 1
    checked, theorem = log.split('@' + HEAD + ' :', 1)[1].split('\ntheorem ' + HEAD, 1)
    typ, proof = theorem.split(' :=', 1)
    assert normalized(checked) == normalized(typ.removeprefix(' :'))
    assert '_private' not in checked + typ and len(proof.encode()) > 1200000
    match = re.search(re.escape("'" + HEAD + "' depends on axioms:") + r'\s*\[([^\]]*)\]', log)
    assert match
    assert {re.sub(r'\.\{[^}]*\}', '', name.strip()) for name in match.group(1).split(',')} == {
        'propext', 'Classical.choice', 'Quot.sound'}
    command = [sys.executable, str(owner / 'scan-stores-verify.py'), '--root', str(args.root)]
    if args.live:
        command.append('--live')
    result = subprocess.run(command, cwd='/', env=dict(os.environ, PYTHONDONTWRITEBYTECODE='1'),
                            capture_output=True, text=True)
    assert result.returncode == 0, (result.stdout, result.stderr)
    owner_result = json.loads(result.stdout)
    assert owner_result['status'] == 'PASS' and owner_result['lean_jobs'] == 3
    assert owner_result['failed_checks'] == 1 and owner_result['infrastructure_attempts'] == 0
    assert owner_result['new_public_pairs'] == 1 and owner_result['canonical_jobs'] == 0
    print(json.dumps({'status': 'PASS', 'live': args.live,
        'pins': len(manifest['files']) + len(manifest['sources']),
        'independent_review': True, 'material_issues': 0,
        'owned_lean_lake_commands': 0, 'owned_public_pairs': 0,
        'reused_lean_jobs': 3, 'reused_public_pairs': 1, 'reused_failures': 1,
        'reused_infrastructure_no_launch_attempts': 0,
        'full_public_log_bytes': len(data), 'all_eight_printer_settings': True,
        'public_type_readback_identical': True, 'standard_axioms_only': True,
        'authored_dependencies_disclosed': ['SourceCurrentNativeCurrentStores',
                                          'SourceCurrentConjunctionPublicationHistory'],
        'frozen_owner_checker': owner_result}))


if __name__ == '__main__':
    main()
