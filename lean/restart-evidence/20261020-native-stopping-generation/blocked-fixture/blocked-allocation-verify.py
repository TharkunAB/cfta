import argparse
import hashlib
import json
from pathlib import Path
import re

HERE = Path(__file__).resolve().parent
ATTEMPTS = {
    'blocked-allocation-calculation-1': 0,
    'blocked-allocation-prefix-1': 1,
    'blocked-allocation-direct-1': 1,
    'blocked-allocation-direct-2': 0,
    'blocked-allocation-public-1': 0,
}
NAME = 'MicroCFTA.NativeBlockedAllocationFixture.actual_blocked_nested_creation'


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--root', type=Path, default=Path('/home/tritlo/Code/mcfta'))
    parser.add_argument('--live', action='store_true')
    args = parser.parse_args()
    manifest = json.loads((HERE / 'blocked-allocation-manifest.json').read_text())
    for base, entries in [(HERE, manifest['files']), (args.root, manifest['sources'])]:
        for item in entries:
            data = (base / item['path']).read_bytes()
            assert len(data) == item['bytes'] and hashlib.sha256(data).hexdigest() == item['sha256'], item['path']
    actual = {f.stem for f in HERE.iterdir()
              if re.fullmatch(r'blocked-allocation-(?:calculation|prefix|direct|public)-\d+\.json', f.name)}
    assert actual == set(ATTEMPTS), actual
    for stem, code in ATTEMPTS.items():
        meta = json.loads((HERE / (stem + '.json')).read_text())
        assert meta['exit_code'] == code
        assert meta['command'][0] == '/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean'
        assert '-Dlinter.all=true' in meta['command']
        assert hashlib.sha256((HERE / meta['source']).read_bytes()).hexdigest() == meta['sha256']
        limits = json.loads((HERE / meta['limits']).read_text())
        assert limits == {'memory.max':'4294967296','memory.high':'4294967296','memory.swap.max':'0'}
        assert meta['wrapper'][meta['wrapper'].index('--mem') + 1] == '4G'
        assert meta['wrapper'][meta['wrapper'].index('--time') + 1] == '5m'
        usage = json.loads((HERE / (stem + '.usage.json')).read_text())
        assert usage['age_seconds'] < 120 and usage['remaining_percent'] > 1
        if code:
            assert re.search(r'\berror:', (HERE / meta['log']).read_text())
    source = (HERE / 'blocked-allocation-kernels.lean').read_bytes()
    assert source == (HERE / 'blocked-allocation-direct-2.source.lean').read_bytes()
    assert not (HERE / 'blocked-allocation-direct-2.log').read_bytes()
    assert not re.search(rb'\b(?:sorry|axiom)\b', source)
    assert source.count(b'SourceCurrentNativeMuStoppingGeneration.execute') == 1
    printer = (HERE / 'blocked-allocation-public-1.source.lean').read_text()
    assert printer.encode().startswith(source)
    assert printer == (HERE / 'blocked-allocation-public.lean').read_text()
    for option in ['linter.all true','pp.explicit true','pp.fullNames true','pp.proofs true',
                   'pp.proofs.threshold 254','pp.universes true','pp.deepTerms true','pp.maxSteps 10000000']:
        assert 'set_option ' + option in printer
    for pattern in [r'^#check @',r'^#print (?!axioms )',r'^#print axioms ']:
        assert len(re.findall(pattern, printer, re.M)) == 1
    assert '#check @' + NAME in printer and '#print ' + NAME in printer and '#print axioms ' + NAME in printer
    log = (HERE / 'blocked-allocation-public-1.log').read_text()
    assert not re.search(r'sorryAx|\b(?:warning|error)(?:\([^)]*\))?:|failed to pretty print|pp\.rawOnError|maximum recursion depth|maximum number of heartbeats|⋯|…|\.\.\.', log)
    reports = re.findall(r'depends on axioms:\s*\[([^\]]*)\]', log)
    assert len(reports) + len(re.findall(r'does not depend on any axioms', log)) == 1
    for report in reports:
        cleaned = re.sub(r'\.\{[^}]*\}', '', report)
        assert set(re.split(r',\s*', cleaned.strip())) <= {'propext','Classical.choice','Quot.sound'}
    diagnostic = (HERE / 'blocked-allocation-calculation-1.log').read_text()
    assert 'pending:MicroCFTA.InternedBinderProtocol.NodeKey.mu' in diagnostic
    assert '(5, 6, 6, 16)' in diagnostic and '(false, true, true, false)' in diagnostic
    assert not re.search(r'\b(?:warning|error):', diagnostic)
    selection = json.loads((HERE / 'blocked-allocation-selection.json').read_text())
    assert selection['finalized'] and selection['attempts'] == list(ATTEMPTS)
    assert selection['strict'] == 'blocked-allocation-direct-2' and selection['public_heads'] == [NAME]
    assert selection['groups'] == [{'name':'blocked-allocation-public-1','pairs':1,'kind':'constructed','full_proof':True}]
    assert selection['lean_jobs'] == 5 and selection['failed_attempts'] == 2 and selection['evaluation_jobs'] == 1
    assert selection['production_pairs'] == 0 and selection['constructed_pairs'] == 1
    assert selection['canonical'] is None and selection['canonical_jobs'] == 0
    print(json.dumps({'status':'PASS','pins':len(manifest['files'])+len(manifest['sources']),
                      'public_pairs':0,'constructed_pairs':1,'lean_jobs':5,'failed_attempts':2,
                      'evaluation_jobs':1,'canonical_jobs':0,'mode':'live' if args.live else 'ordinary'}))


if __name__ == '__main__':
    main()
