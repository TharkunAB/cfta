import hashlib, importlib.util, json, re, sys
from pathlib import Path
sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()
manifest = json.loads((HERE/'callback-kernels-manifest.json').read_text())
assert manifest['status'] == 'final'
assert len({x['path'] for x in manifest['files']}) == len(manifest['files'])
for item in manifest['files']:
    path = ROOT/item['path']
    assert path.stat().st_size == item['bytes'] and sha(path) == item['sha256'], item['path']
assert not any(x['path'].endswith('/callback-kernels-peaks.txt') for x in manifest['files'])
selection = json.loads((HERE/'callback-kernels-selection.json').read_text())
spec = importlib.util.spec_from_file_location('owned_head_probe', HERE/'callback-kernels-probe-tools.py')
probe = importlib.util.module_from_spec(spec)
spec.loader.exec_module(probe)
source = HERE/'callback-kernels.lean'
assert sha(source) == selection['source_sha256']
for stem, code in selection['attempts'].items():
    meta = json.loads((HERE/(stem+'.json')).read_text())
    assert meta['exit_code'] == code and sha(HERE/meta['source']) == meta['sha256']
    assert meta['command'][:2] == ['/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean','-Dlinter.all=true']
    assert meta['wrapper'][:5] == ['/home/tritlo/Code/heavy-management/bin/capped','--mem','4G','--time','5m']
    probe.check_limits(stem)
strict = json.loads((HERE/(selection['strict']+'.json')).read_text())
assert strict['exit_code'] == 0 and (HERE/strict['log']).read_bytes() == b''
assert (HERE/strict['source']).read_bytes() == source.read_bytes()
for group in selection['groups']:
    probe.check_group(group)
    meta = json.loads((HERE/(group['name']+'.json')).read_text())
    assert (HERE/meta['source']).read_bytes().startswith(source.read_bytes())
text = source.read_text()
assert re.search(r'private theorem checked_witness(.*?) := by',text,re.S).group(1) == re.search(r'theorem raw_callback(.*?) := checked_witness',text,re.S).group(1)
assert sha(ROOT/selection['module']) == selection['module_sha256']
meta = json.loads((HERE/'callback-canonical-1.json').read_text())
assert meta['exit_code'] == 0 and 'Build completed successfully' in (HERE/meta['log']).read_text()
probe.check_limits('callback-canonical-1')
peaks = (HERE/'callback-kernels-final-peaks.txt').read_text().splitlines()
assert len(peaks) == len(selection['attempts']) and [int(x.split()[-1]) for x in peaks] == list(selection['attempts'].values())
assert all(x.split()[2] == '4G' for x in peaks)
print(json.dumps({'status':'PASS','pins':len(manifest['files']),'manifest_sha256':sha(HERE/'callback-kernels-manifest.json'),'constructed_pairs':1,'owned_production_public_pairs':0,'owned_jobs':len(selection['attempts']),'strict_literal_zero':True,'private_public_statements_identical':True},sort_keys=True))
