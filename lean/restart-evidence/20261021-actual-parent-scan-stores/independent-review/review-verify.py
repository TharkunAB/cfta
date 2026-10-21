import argparse
import hashlib
import json
import os
import re
import subprocess
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
SOURCE = 'SourceCurrentActualParentScanNativeStores.lean'
FINAL = 'fb94ee44471c161ec6d3c94348b07a38ee52fc3823ac28296c66334dc952e8e0'
HEAD = 'MicroCFTA.SourceCurrentActualParentScanNativeStores.selected_scan'


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
    assert len(source.splitlines()) == 147
    assert source == (HERE / 'inputs/prelaunch/SourceCurrentActualParentScanNativeStores.lean.txt').read_text()
    assert re.findall(r'^theorem (\w+)', source, re.M) == ['selected_scan']
    assert not re.search(r'\b(?:sorry|axiom|admit|native_decide|trustCompiler)\b|_private', source)
    public = source.split('\ntheorem selected_scan\n', 1)[1].split(':=', 1)[0]
    proposed = (HERE / 'inputs/plan/proposed-signature.lean.txt').read_text().split('\ntheorem selected_scan\n', 1)[1]
    assert normalized(public) == normalized(proposed)
    for token in ['SourceCurrentActualParentSemanticReads.parent formulas solver inventory budget',
                  'graph_scan numeric.actual noncontradictory precheck',
                  'SourceCurrentAllocatedScanWorkerCompletion.scan_complete actualScan',
                  'SourceCurrentAllocatedRecordScanWorker.scan_mapPaths g s p h n budget values records',
                  'SourceCurrentAllocatedScanWorkerStability.scan_done_unique completed literal',
                  'SourceCurrentAllocatedLocalReductionActual.prefix_verified formulas solver inventory',
                  'SourceCurrentScanNativeStores.scan formulas solver actualScan prefixReceipt.ready prefixAvailable proper']:
        assert source.count(token) == 1, token
    assert source.count('SourceCurrentAllocatedPrecheck.state_native') == 4
    assert 'obtain ⟨sameResult, sameState, sameFourth⟩' in source
    assert 'obtain ⟨sameOutcome, sameSelected⟩ := Prod.mk.inj sameResult' in source
    assert 'subst outcome selected scanState returnedFourth' in source
    assert 'prefixReceipt.classes records rfl' in source
    assert not (owner / 'parent-scan-stores-direct-1.log').read_bytes()
    data = (owner / 'parent-scan-stores-public-1.log').read_bytes()
    assert len(data) == 735805
    assert hashlib.sha256(data).hexdigest() == 'f30035ba8b61a94c6a4791a17f08d88b84eb52c98aecda6fd74405bb5aa44028'
    log = data.decode()
    assert not re.search(r'sorryAx|\b(?:warning|error)(?:\([^)]*\))?:|failed to pretty print|pp\.rawOnError|maximum recursion depth|maximum number of heartbeats|⋯|…|\.\.\.', log)
    printer = (owner / 'parent-scan-stores-public-1.source.lean').read_text()
    assert printer.startswith(source)
    for option in ['linter.all true', 'pp.explicit true', 'pp.fullNames true', 'pp.proofs true',
                   'pp.proofs.threshold 254', 'pp.universes true', 'pp.deepTerms true', 'pp.maxSteps 10000000']:
        assert printer.count('set_option ' + option) == 1
    checked, theorem = log.split('@' + HEAD + ' :', 1)[1].split('\ntheorem ' + HEAD, 1)
    typ, proof = theorem.split(' :=', 1)
    assert normalized(checked) == normalized(typ.removeprefix(' :'))
    assert '_private' not in checked + typ and len(proof.encode()) > 600000
    match = re.search(re.escape("'" + HEAD + "' depends on axioms:") + r'\s*\[([^\]]*)\]', log)
    assert match
    assert {re.sub(r'\.\{[^}]*\}', '', name.strip()) for name in match.group(1).split(',')} == {
        'propext', 'Classical.choice', 'Quot.sound'}
    command = [sys.executable, str(owner / 'parent-scan-stores-verify.py'), '--root', str(args.root)]
    if args.live:
        command.append('--live')
    result = subprocess.run(command, cwd='/', env=dict(os.environ, PYTHONDONTWRITEBYTECODE='1'),
                            capture_output=True, text=True)
    assert result.returncode == 0, (result.stdout, result.stderr)
    owner_result = json.loads(result.stdout)
    assert owner_result['status'] == 'PASS'
    assert owner_result['lean_jobs'] == 2 and owner_result['failed_checks'] == 0
    assert owner_result['warning_checks'] == owner_result['infrastructure_attempts'] == 0
    assert owner_result['canonical_jobs'] == owner_result['constructed_pairs'] == 0
    assert owner_result['public_pairs'] == 1
    print(json.dumps({'status': 'PASS', 'live': args.live,
        'pins': len(manifest['files']) + len(manifest['sources']),
        'independent_review': True, 'material_issues': 0,
        'owned_lean_lake_commands': 0, 'owned_public_pairs': 0,
        'reused_lean_jobs': 2, 'reused_public_pairs': 1, 'reused_failures': 0,
        'reused_infrastructure_no_launch_attempts': 0,
        'full_public_log_bytes': len(data), 'all_eight_printer_settings': True,
        'public_type_readback_identical': True, 'plan_public_type_identical': True,
        'standard_axioms_only': True,
        'authored_dependencies_disclosed': ['SourceCurrentNativeCurrentStores',
                                          'SourceCurrentConjunctionPublicationHistory'],
        'frozen_owner_checker': owner_result}))


if __name__ == '__main__':
    main()
