import argparse
import hashlib
import json
import os
import re
import subprocess
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
FINAL = 'd0b9482f3a3558eeba112de5ed3216c1be00d425deb1bf0915c2bbda53bee154'
HEAD = 'MicroCFTA.SourceCurrentNativePositiveSupportAdvance.advance'


def check(path, pin):
    data = path.read_bytes()
    assert len(data) == pin['bytes'], ('bytes', path)
    assert hashlib.sha256(data).hexdigest() == pin['sha256'], ('hash', path)


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
    text = (owner / 'SourceCurrentNativePositiveSupportAdvance.lean').read_text()
    assert hashlib.sha256(text.encode()).hexdigest() == FINAL and len(text.splitlines()) == 35
    assert re.findall(r'^theorem (\w+)', text, re.M) == ['advance']
    public = text.split('theorem advance ', 1)[1].split(':=', 1)[0]
    for token in ['At Plain before', 'Support before.native.machine.heap before.native', 'Good after',
                  'Extension before.native.machine after.native.machine',
                  'after.native.nodes = before.native.nodes', 'after.native.edges = before.native.edges',
                  'Support after.native.machine.heap after.native']:
        assert token in public, token
    for token in ['History', 'SemanticReady', 'GuardHeap', 'DecidableEq', 'Trace', 'PositiveAt']:
        assert token not in public, token
    for token in ['Support before.native.machine.heap after.native',
                  'simpa only [nodes] using supported.1', 'simpa only [edges] using supported.2',
                  'Stored before.native.machine.heap after.native',
                  'simpa only [nodes] using current.2.2.nodes', 'simpa only [edges] using current.2.2.edges',
                  'SourceCurrentNativePositiveSupportRebase.rebase before.native.machine.heap after.native.machine.heap',
                  'after.native current.1.valid.1 good.native.machine.1 extension.heap extension.history origins retained']:
        assert text.count(token) == 1, token
    assert not re.search(r'\b(?:sorry|admit|axiom|native_decide|trustCompiler)\b', text)
    log = (owner / 'support-advance-public-1.log').read_text()
    match = re.search("'" + re.escape(HEAD) + r"' depends on axioms:\s*\[([^\]]*)\]", log)
    assert match
    assert {re.sub(r'\.\{[^}]*\}', '', n.strip()) for n in match.group(1).split(',')} == {
        'propext', 'Classical.choice', 'Quot.sound'}
    typ, proof = log.split('theorem ' + HEAD, 1)[1].split(':=', 1)
    assert '_private' not in typ and len(proof) > 1000
    command = [sys.executable, str(owner / 'support-advance-verify.py'), '--root', str(args.root)]
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
                      'reused_lean_jobs': 2, 'reused_public_pairs': 1, 'reused_failures': 0,
                      'full_public_log_bytes': len(log.encode()), 'standard_axioms_only': True,
                      'frozen_owner_checker': result}))


if __name__ == '__main__':
    main()
