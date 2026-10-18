import ast,json,re,runpy
from pathlib import Path
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[2]
def read(name):return json.loads((HERE/name).read_text())
checks=runpy.run_path(str(HERE/'verify-probes.py'))
manifest=read('finite-execution-manifest.json')
for entry in manifest['entries']:
 path=ROOT/entry['path'];assert checks['sha'](path)==entry['sha256'],entry['path']
 assert path.stat().st_size==entry['bytes'],entry['path']
selection=read('finite-execution-selection.json')
assert selection['new_public_pairs']==7
for group in selection['groups']:checks['check_group'](group)
for module,stem in selection['strict'].items():
 receipt=read(stem+'.json');assert receipt['exit_code']==0
 assert not (HERE/receipt['log']).read_bytes()
 assert checks['sha'](HERE/receipt['source'])==checks['sha'](ROOT/'lean/MicroCFTA'/(module+'.lean'))
 checks['check_limits'](stem)
for stem in selection['canonical'].values():
 receipt=read(stem+'.json');log=(HERE/receipt['log']).read_text()
 assert receipt['exit_code']==0 and 'Build completed successfully' in log
 assert not re.search(r'^warning:',log,re.M)
 checks['check_limits'](stem)
for name in ['finite-execution-verify.py','root-run-check.py','root-capped-worker.py','verify-probes.py']:
 ast.parse((HERE/name).read_text(),filename=name)
print(json.dumps({'status':'PASS','public_pairs':7,'constructed_pairs':0,'entries':len(manifest['entries']),'strict_modules':2}))
