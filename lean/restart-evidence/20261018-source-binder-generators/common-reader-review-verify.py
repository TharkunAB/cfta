import hashlib
import json
import re
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
PREFIX = 'common-reader-review'
LIMITS = {
    'memory.max': '4294967296',
    'memory.high': '4294967296',
    'memory.swap.max': '0',
}
OPTIONS = [
    'linter.all true', 'pp.explicit true', 'pp.fullNames true',
    'pp.proofs true', 'pp.proofs.threshold 254', 'pp.universes true',
    'pp.deepTerms true', 'pp.maxSteps 10000000',
]


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def receipt(stem):
    meta = json.loads((HERE / (stem + '.json')).read_text())
    assert meta['exit_code'] == 0, stem
    assert meta['wrapper'][:5] == [
        '/home/tritlo/Code/heavy-management/bin/capped',
        '--mem', '4G', '--time', '5m',
    ], stem
    assert json.loads((HERE / meta['limits']).read_text()) == LIMITS, stem
    if 'source' in meta:
        assert sha(HERE / meta['source']) == meta['sha256'], stem
    return meta


def group(stem, expected):
    meta = receipt(stem)
    source = (HERE / meta['source']).read_text()
    log = (HERE / meta['log']).read_text()
    for option in OPTIONS:
        assert 'set_option ' + option in source, (stem, option)
    assert re.findall(r'^#check @(.+)$', source, re.M) == [expected], stem
    assert re.findall(r'^#print (?!axioms )(.+)$', source, re.M) == [expected], stem
    assert re.findall(r'^#print axioms (.+)$', source, re.M) == [expected], stem
    assert not re.search(
        r'sorryAx|\b(?:warning|error)(?:\([^)]*\))?:|failed to pretty print|pp\.rawOnError|'
        r'maximum recursion depth|maximum number of heartbeats|⋯|…|\.\.\.', log), stem
    reports = re.findall(r'depends on axioms:\s*\[([^\]]*)\]', log)
    assert len(reports) + len(re.findall(r'does not depend on any axioms', log)) == 1, stem
    for report in reports:
        cleaned = re.sub(r'\.\{[^}]*\}', '', report)
        assert set(re.split(r',\s*', cleaned.strip())) <= {
            'propext', 'Classical.choice', 'Quot.sound',
        }, (stem, report)


def main():
    manifest = json.loads((HERE / (PREFIX + '-manifest.json')).read_text())
    for item in manifest['entries']:
        path = ROOT / item['path']
        assert path.stat().st_size == item['bytes'], path
        assert sha(path) == item['sha256'], path
    selection = json.loads((HERE / (PREFIX + '-selection.json')).read_text())
    assert selection['finalized']
    assert selection['owned_public_pairs'] == selection['owned_constructed_pairs'] == 0
    assert selection['owned_lean_executions'] == 0
    assert selection['reused_public_pairs'] == selection['reused_constructed_pairs'] == 1
    owner = json.loads((HERE / 'common-reader-selection.json').read_text())
    assert owner['status'] == 'final'
    assert owner['strict'] == 'common-reader-direct-2'
    assert owner['canonical'] == 'common-reader-canonical-1'
    assert owner['constructed_strict'] == selection['constructed_strict']
    production = manifest['production']
    strict = receipt(production['strict'])
    assert not (HERE / strict['log']).read_bytes()
    assert sha(ROOT / production['path']) == strict['sha256'] == production['sha256']
    canonical = receipt(production['canonical'])
    log = (HERE / canonical['log']).read_text()
    assert re.search(r'Build completed successfully \(\d+ jobs\)\.', log)
    assert not re.search(r'\b(?:warning|error)(?:\([^)]*\))?:|sorryAx|failed to pretty print', log)
    fixture = receipt(selection['constructed_strict'])
    assert not (HERE / fixture['log']).read_bytes()
    printed_fixture = receipt('common-reader-kernels-public-1')
    assert (HERE / fixture['source']).read_bytes() in (HERE / printed_fixture['source']).read_bytes()
    group('common-reader-public-1', 'MicroCFTA.SourceCurrentCommonReaderBinderSupport.node')
    group('common-reader-kernels-public-1', 'MicroCFTA.CommonReaderKernels.open_used')
    print(json.dumps({
        'status': 'PASS', 'entries': len(manifest['entries']),
        'owned_public_pairs': 0, 'owned_constructed_pairs': 0,
        'owned_lean_executions': 0, 'reused_public_pairs': 1,
        'reused_constructed_pairs': 1,
    }, sort_keys=True))


if __name__ == '__main__':
    main()
