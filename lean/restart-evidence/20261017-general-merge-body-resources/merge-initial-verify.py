"""Verify the frozen initial Merge composition without rebuilding."""
from pathlib import Path
import hashlib
import json
import re
ROOT=Path(__file__).resolve().parents[3]
HERE=Path(__file__).resolve().parent
manifest=json.loads((HERE/'merge-initial-manifest.json').read_text())
for entry in manifest['entries']:
    data=(ROOT/entry['path']).read_bytes()
    assert len(data)==entry['bytes'],entry['path']
    assert hashlib.sha256(data).hexdigest()==entry['sha256'],entry['path']
for item in manifest['strict']:
    assert (ROOT/item['log']).read_bytes()==b''
    assert (ROOT/item['source']).read_bytes()==(ROOT/item['snapshot']).read_bytes()
for name,jobs in manifest['canonical'].items():
    assert f'Build completed successfully ({jobs} jobs).' in (ROOT/name).read_text()
for check in manifest['checks']:
    source=(ROOT/check['source']).read_text()
    log=(ROOT/check['log']).read_text()
    assert not re.search(r'error(?:\(|:)|warning(?:\(|:)|sorryAx|⋯|\.\.\.',log),check['log']
    declarations=re.findall(r'^#print axioms (\S+)',source,re.M)
    assert len(declarations)==check['pairs']
    assert len(re.findall(r'^#check @',source,re.M))==check['pairs']
    assert log.count('depends on axioms:')+log.count('does not depend on any axioms')==check['pairs']
    for name in declarations:
        assert '#check @'+name in source and name in log,name
    for block in re.findall(r'depends on axioms: \[([^\]]*)\]',log,re.S):
        axioms={re.sub(r'\.\{[^}]*\}','',name.strip()) for name in block.split(',') if name.strip()}
        assert axioms<={'propext','Classical.choice','Quot.sound'},axioms
    for setting in ['linter.all true','pp.explicit true','pp.fullNames true','pp.proofs true','pp.universes true','pp.deepTerms true','pp.maxSteps 10000000']:
        assert 'set_option '+setting in source,setting
print('PASS:',len(manifest['entries']),'hashes;14 complete pairs;3 strict sources;3 canonical targets;diagnostics 0')
