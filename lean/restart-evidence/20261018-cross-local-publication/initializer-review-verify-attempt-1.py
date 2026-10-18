"""Verify frozen read-only initializer review pins and reused proof receipts."""
import hashlib
import json
import re
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
PREFIX = 'initializer-review'

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def main():
    manifest = json.loads((HERE / f'{PREFIX}-manifest.json').read_text())
    for entry in manifest['entries']:
        path = ROOT / entry['path']
        assert path.stat().st_size == entry['bytes'] and sha(path) == entry['sha256'], path
    selection = json.loads((HERE / f'{PREFIX}-selection.json').read_text())
    assert selection['owned_lean_runs'] == selection['owned_pairs'] == 0
    assert selection['reused_public_pairs'] == 2
    assert sha(ROOT / selection['production']) == selection['sha256']
    for stem in [selection['strict'], selection['canonical'], selection['groups'][0]['name']]:
        metadata = json.loads((HERE / f'{stem}.json').read_text())
        assert metadata['exit_code'] == 0
        assert metadata['wrapper'][0:5] == ['/home/tritlo/Code/heavy-management/bin/capped', '--mem', '4G', '--time', '5m']
        assert json.loads((HERE / metadata['limits']).read_text()) == {
            'memory.max': '4294967296', 'memory.high': '4294967296', 'memory.swap.max': '0'}
        if 'source' in metadata:
            assert sha(HERE / metadata['source']) == metadata['sha256']
    strict = json.loads((HERE / f"{selection['strict']}.json").read_text())
    assert strict['sha256'] == selection['sha256']
    assert not (HERE / strict['log']).read_bytes()
    canonical = (HERE / f"{selection['canonical']}.log").read_text()
    assert 'Build completed successfully' in canonical and 'error:' not in canonical
    warnings = re.findall(r'^warning: (.*)$', canonical, re.M)
    assert warnings == ["MicroCFTA/InternedFreshOrdinaryClosedCompletion.lean:24:5: Variable name `inputs` is not explicitly referenced."]
    group = selection['groups'][0]
    metadata = json.loads((HERE / f"{group['name']}.json").read_text())
    source = (HERE / metadata['source']).read_text()
    output = (HERE / metadata['log']).read_text()
    for option in ['linter.all true', 'pp.explicit true', 'pp.fullNames true', 'pp.proofs true',
                   'pp.proofs.threshold 254', 'pp.universes true', 'pp.deepTerms true', 'pp.maxSteps 10000000']:
        assert f'set_option {option}' in source
    for pattern in [r'^#check @', r'^#print (?!axioms )', r'^#print axioms ']:
        assert len(re.findall(pattern, source, re.M)) == group['pairs'] == 2
    assert not re.search(r'sorryAx|\b(?:warning|error)(?:\([^)]*\))?:|failed to pretty print|pp\.rawOnError|maximum recursion depth|maximum number of heartbeats|⋯|…|\.\.\.', output)
    axioms = re.findall(r'depends on axioms:\s*\[([^\]]*)\]', output)
    assert len(axioms) + len(re.findall(r'does not depend on any axioms', output)) == 2
    for report in axioms:
        cleaned = re.sub(r'\.\{[^}]*\}', '', report)
        assert set(re.split(r',\s*', cleaned.strip())) <= {'propext', 'Classical.choice', 'Quot.sound'}
    actual = (ROOT / 'lean/MicroCFTA/SourceCurrentConstructedOuterInitial.lean').read_text()
    assert 'SourceCurrentConstrainedCapGuardExecution.closed_heap Plain expression' in actual
    assert 'Frame.initial formulas solver inventory machine operations ready guards same' in actual
    assert 'SourceCurrentOuterInitialActual.node_call formulas solver fuel seed context currentFrame' in actual
    assert 'Generated' not in actual and 'Directed' not in actual
    guard = (ROOT / 'lean/MicroCFTA/SourceCurrentConstrainedCapGuardExecution.lean').read_text()
    assert 'open InternedFreshOrdinaryConstruction' in guard
    assert '(build expression [] empty).state' in guard
    assert manifest['groups'] == selection['groups']
    print(json.dumps({'status': 'PASS', 'entries': len(manifest['entries']), 'owned_lean_runs': 0,
                      'owned_pairs': 0, 'reused_public_pairs': 2, 'canonical_known_old_warning': True}, sort_keys=True))

if __name__ == '__main__':
    main()
