import hashlib
import json
import os
import subprocess
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
def git(*args):
    return subprocess.check_output(['git',*args],cwd=ROOT)
assert not git('status','--porcelain'),'Checkpoint must be clean'
head = git('rev-parse','HEAD').decode().strip()
head_entries = {}
for record in git('ls-tree','-r','--full-tree','-z','HEAD').split(b'\0'):
    if not record:
        continue
    meta,raw = record.split(b'\t',1)
    mode,kind,oid = meta.split()
    assert kind == b'blob'
    path = ROOT/os.fsdecode(raw)
    data = os.fsencode(os.readlink(path)) if mode == b'120000' else path.read_bytes()
    assert hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest().encode() == oid,str(path)
    if mode in [b'100644',b'100755']:
        assert bool(path.stat().st_mode&0o111) == (mode==b'100755'),str(path)
    head_entries[raw] = (mode,oid)
index_entries = {}
for record in git('ls-files','--stage','-z').split(b'\0'):
    if not record:
        continue
    meta,raw = record.split(b'\t',1)
    mode,oid,stage = meta.split()
    assert stage == b'0'
    index_entries[raw] = (mode,oid)
assert index_entries == head_entries
checks = []
for line in (HERE/'SHA256SUMS').read_text().splitlines():
    expected,name = line.split('  ',1)
    assert hashlib.sha256((ROOT/name).read_bytes()).hexdigest() == expected,name
    checks.append(name)
assert set(checks) == {str(path.relative_to(ROOT)) for path in HERE.rglob('*') if path.is_file() and path.name!='SHA256SUMS'}
assert all(os.fsencode(name) in head_entries for name in checks+[str((HERE/'SHA256SUMS').relative_to(ROOT))])
for name in ['root-scope-manifest.json']:
    for entry in json.loads((HERE/name).read_text())['files']:
        path = ROOT/entry['path']
        assert hashlib.sha256(path.read_bytes()).hexdigest() == entry['sha256'],str(path)
        assert path.stat().st_size == entry['bytes']
report = json.loads(subprocess.check_output(['python3',str(HERE/'verify-import.py')],cwd=ROOT))
assert report == json.loads((HERE/'import-validation.json').read_text())
for name in json.loads((HERE/'component-manifests.json').read_text()):
    for entry in json.loads((HERE/name).read_text())['files']:
        path = ROOT/entry['path']
        assert hashlib.sha256(path.read_bytes()).hexdigest()==entry['sha256'],str(path)
        assert path.stat().st_size==entry['bytes']
print(json.dumps({'head':head,'tracked_blobs_and_modes':len(head_entries),
    'filesystem_index_head_equal':True,'evidence_checksums':len(checks),
    'import_matches_retained_report':True,'component_and_scope_pins_pass':True,'clean':True},indent=2))
