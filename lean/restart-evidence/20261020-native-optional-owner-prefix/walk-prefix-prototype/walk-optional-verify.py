import argparse
import hashlib
import json
from pathlib import Path
import re

HERE = Path(__file__).resolve().parent
ATTEMPTS = {'walk-optional-direct-1':1,'walk-optional-direct-2':0,
            'walk-optional-direct-3':0,'walk-optional-public-1':0}
NAMES = ['MicroCFTA.SourceCurrentNativeWalkOptionalPrefix.cut']


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--root', type=Path, default=Path('/home/tritlo/Code/mcfta'))
    parser.add_argument('--live', action='store_true')
    args = parser.parse_args()
    manifest = json.loads((HERE / 'walk-optional-manifest.json').read_text())
    for base, entries in [(HERE,manifest['files']),(args.root,manifest['sources'])]:
        for item in entries:
            data = (base / item['path']).read_bytes()
            assert len(data) == item['bytes'] and hashlib.sha256(data).hexdigest() == item['sha256'], item['path']
    assert {f.stem for f in HERE.iterdir() if re.fullmatch(r'walk-optional-(?:direct|public)-\d+\.json',f.name)} == set(ATTEMPTS)
    for stem, code in ATTEMPTS.items():
        meta = json.loads((HERE / (stem + '.json')).read_text())
        assert meta['exit_code'] == code and '-Dlinter.all=true' in meta['command']
        assert meta['command'][0] == '/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean'
        assert hashlib.sha256((HERE / meta['source']).read_bytes()).hexdigest() == meta['sha256']
        assert json.loads((HERE / meta['limits']).read_text()) == {
            'memory.max':'4294967296','memory.high':'4294967296','memory.swap.max':'0'}
        assert meta['wrapper'][meta['wrapper'].index('--mem') + 1] == '4G'
        assert meta['wrapper'][meta['wrapper'].index('--time') + 1] == '5m'
        usage = json.loads((HERE / (stem + '.usage.json')).read_text())
        assert usage['age_seconds'] < 120 and usage['remaining_percent'] > 1
        if code:
            assert re.search(r'\berror(?:\([^)]*\))?:', (HERE / meta['log']).read_text())
    source = (HERE / 'SourceCurrentNativeWalkOptionalPrefix.lean').read_bytes()
    assert source == (HERE / 'walk-optional-direct-3.source.lean').read_bytes()
    assert not (HERE / 'walk-optional-direct-3.log').read_bytes()
    assert b'_private' not in source and not re.search(rb'\b(?:sorry|axiom)\b',source)
    assert len(re.findall(rb'^theorem ',source,re.M)) == 1
    printer = (HERE / 'walk-optional-public-1.source.lean').read_text()
    assert printer.encode().startswith(source) and printer == (HERE / 'walk-optional-public.lean').read_text()
    for option in ['linter.all true','pp.explicit true','pp.fullNames true','pp.proofs true',
                   'pp.proofs.threshold 254','pp.universes true','pp.deepTerms true','pp.maxSteps 10000000']:
        assert 'set_option ' + option in printer
    for pattern in [r'^#check @',r'^#print (?!axioms )',r'^#print axioms ']:
        assert len(re.findall(pattern,printer,re.M)) == 1
    for name in NAMES:
        assert '#check @' + name in printer and '#print ' + name in printer and '#print axioms ' + name in printer
    log = (HERE / 'walk-optional-public-1.log').read_text()
    assert not re.search(r'sorryAx|\b(?:warning|error)(?:\([^)]*\))?:|failed to pretty print|pp\.rawOnError|maximum recursion depth|maximum number of heartbeats|⋯|…|\.\.\.',log)
    reports = re.findall(r'depends on axioms:\s*\[([^\]]*)\]',log)
    assert len(reports) + len(re.findall(r'does not depend on any axioms',log)) == 1
    for report in reports:
        assert set(re.split(r',\s*',re.sub(r'\.\{[^}]*\}','',report).strip())) <= {'propext','Classical.choice','Quot.sound'}
    selection = json.loads((HERE / 'walk-optional-selection.json').read_text())
    assert selection['finalized'] and selection['public_heads'] == NAMES
    assert selection['attempts'] == list(ATTEMPTS) and selection['strict'] == 'walk-optional-direct-3'
    assert selection['groups'] == [{'name':'walk-optional-public-1','pairs':1,'kind':'prototype-public','full_proof':True}]
    assert selection['lean_jobs'] == 4 and selection['failed_attempts'] == 1
    assert selection['production_pairs'] == 1 and selection['constructed_pairs'] == 0
    assert selection['warning_attempts'] == 1
    warning_log = (HERE / 'walk-optional-direct-2.log').read_text()
    assert 'warning:' in warning_log and 'unused' in warning_log and not re.search(r'\berror:',warning_log)
    assert selection['canonical'] is None and selection['canonical_jobs'] == 0
    print(json.dumps({'status':'PASS','pins':len(manifest['files'])+len(manifest['sources']),
                      'public_pairs':1,'constructed_pairs':0,'lean_jobs':4,'failed_attempts':1,
                      'warning_attempts':1,'canonical_jobs':0,'mode':'live' if args.live else 'ordinary'}))


if __name__ == '__main__':
    main()
