import hashlib, json, re, runpy
from pathlib import Path
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[2]
manifest=json.loads((HERE/'root-row-lineage-manifest.json').read_text())
for entry in manifest['entries']:
    path=ROOT/entry['path']
    assert path.stat().st_size==entry['bytes'],entry['path']
    assert hashlib.sha256(path.read_bytes()).hexdigest()==entry['sha256'],entry['path']
checks=runpy.run_path(str(HERE/'verify-probes.py'))
for group in manifest['groups']:checks['check_group'](group)
for module,stem in manifest['stricts'].items():
    report=json.loads((HERE/(stem+'.json')).read_text())
    assert report['exit_code']==0
    assert not (HERE/report['log']).read_bytes()
    assert (HERE/report['source']).read_bytes()==(ROOT/'lean/MicroCFTA'/(module+'.lean')).read_bytes()
    checks['check_limits'](stem)
for module,stem in manifest['canonicals'].items():
    report=json.loads((HERE/(stem+'.json')).read_text())
    assert report['exit_code']==0
    log=(HERE/report['log']).read_text()
    assert 'Build completed successfully' in log
    assert not re.search(r'error:|sorryAx|failed to pretty',log,re.I)
    for warning in re.findall(r'^warning:.*$',log,re.M):
        assert 'InternedFreshOrdinaryClosedCompletion.lean:24:5' in warning
    checks['check_limits'](stem)
print(json.dumps({'status':'PASS','entries':len(manifest['entries']),'public_pairs':sum(g['pairs'] for g in manifest['groups']),'strict_modules':len(manifest['stricts'])}))
