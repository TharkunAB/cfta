import argparse
import hashlib
import json
import os
import re
import subprocess
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
FINAL = '01a135ec67ebb6937106a4958c7efa418d02af1eb9c061a7c07bf6727fc5b577'
HEAD = 'MicroCFTA.SourceCurrentNativeCurrentPositivePositions.step'


def check(path, pin):
    data = path.read_bytes()
    assert len(data) == pin['bytes'], ('bytes', path)
    assert hashlib.sha256(data).hexdigest() == pin['sha256'], ('hash', path)
    return data


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--root', type=Path, required=True)
    parser.add_argument('--live', action='store_true')
    args = parser.parse_args()
    manifest = json.loads((HERE / 'manifest.json').read_text())
    assert manifest['finalized'] and manifest['independent_review']
    assert manifest['owned_lean_lake_commands'] == manifest['owned_public_pairs'] == 0
    for pin in manifest['files']:
        check(HERE / pin['path'], pin)
    assert json.loads((HERE / 'source-pins.json').read_text())['sources'] == manifest['sources']
    for pin in manifest['sources']:
        check(HERE / pin['snapshot'], pin)
        if args.live:
            check(args.root / pin['path'], pin)
    owner = HERE / 'inputs/owner'
    text = (owner / 'SourceCurrentNativeCurrentPositivePositions.lean').read_text()
    assert hashlib.sha256(text.encode()).hexdigest() == FINAL
    assert len(text.splitlines()) == 81
    assert re.findall(r'^theorem (\w+)', text, re.M) == ['step']
    assert 'RawCorridorPositiveProjection' not in text
    public = text.split('theorem step ', 1)[1].split(':=', 1)[0]
    for token in ['Step left right before result after',
                  'Good before', 'SemanticReady before.native.machine.heap',
                  'At Plain before', 'Support before.native.machine.heap before.native',
                  'History empty before.native.machine.heap',
                  'left.free = []', 'right.free = []',
                  'Cap Plain depth left', 'Cap Plain depth right',
                  'At Plain after', 'Support after.native.machine.heap after.native',
                  'History empty after.native.machine.heap', 'Cap Plain depth result',
                  'PositiveAt result path → PositiveAt left path ∨ PositiveAt right path']:
        assert token in public, token
    for token in ['cases actual with', 'let source := before.native.machine.heap',
                  'SourceCurrentNativeRequestPositivePositions.call source',
                  'SourceCurrentConstrainedCapCurrentNative.step depth formulas solver (.run trace)',
                  'originalInputs trace (fun final value => Available final.heap value)',
                  '(grows_refl _) (extends_refl _) (fun _ => trivial) current.2.2 certificate',
                  'facts query.2.2.1.context.valid.1 query.2.2.1.context.growth query.2.2.1.context.history captured.1 query.1',
                  'exact ⟨next.1,rebased,query.2.2.2,next.2.1,query.2.1⟩']:
        assert text.count(token) == 1, token
    assert not re.search(r'\b(?:sorry|admit|axiom|native_decide|trustCompiler)\b', text)
    log = (owner / 'current-position-public-1.log').read_text()
    report = re.search("'" + re.escape(HEAD) + r"' depends on axioms:\s*\[([^\]]*)\]", log)
    assert report
    assert {re.sub(r'\.\{[^}]*\}', '', n.strip()) for n in report.group(1).split(',')} == {
        'propext', 'Classical.choice', 'Quot.sound'}
    typ, proof = log.split('theorem ' + HEAD, 1)[1].split(':=', 1)
    assert '_private' not in typ and len(proof) > 1000
    command = [sys.executable, str(owner / 'current-position-verify.py'), '--root', str(args.root)]
    if args.live:
        command.append('--live')
    checked = subprocess.run(command, cwd='/', env=dict(os.environ, PYTHONDONTWRITEBYTECODE='1'),
                             capture_output=True, text=True)
    assert checked.returncode == 0, (checked.stdout, checked.stderr)
    result = json.loads(checked.stdout)
    assert result['status'] == 'PASS' and result['lean_jobs'] == 2 and result['public_pairs'] == 1
    print(json.dumps({'status': 'PASS', 'live': args.live,
                      'pins': len(manifest['files']) + len(manifest['sources']),
                      'independent_review': True, 'material_issues': 0,
                      'owned_lean_lake_commands': 0, 'owned_public_pairs': 0,
                      'reused_lean_jobs': 2, 'reused_public_pairs': 1,
                      'reused_failures': 0, 'full_public_log_bytes': len(log.encode()),
                      'standard_axioms_only': True, 'frozen_owner_checker': result}))


if __name__ == '__main__':
    main()
