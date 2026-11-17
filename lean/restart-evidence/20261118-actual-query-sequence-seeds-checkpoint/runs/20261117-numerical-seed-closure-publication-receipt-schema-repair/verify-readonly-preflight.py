from pathlib import Path
import hashlib
import json

root = Path('/home/tritlo/Code/mcfta')
repair = Path(__file__).resolve().parent
name = 'prepare-publication-receipt-schema-repair.py'
source = (repair / name).read_bytes()
marker = b'# Root runs the mutation phase only after reviewing every preflight check.'
assert source.count(marker) == 1
prefix = source.split(marker, 1)[0]
work_file = root / 'lean/restart-evidence/20261117-numerical-source-callbacks-work' / name
assert not work_file.exists(), 'This runner supplies only a virtual Work filename.'
manifest_path = repair / 'MANIFEST.json'
original_read_bytes = Path.read_bytes
original_read_text = Path.read_text
virtual_manifest = None
if not manifest_path.exists():
    files = {}
    for path in sorted(repair.iterdir()):
        if path.is_file() and path.name != 'MANIFEST.json':
            data = original_read_bytes(path)
            files[path.name] = {'bytes': len(data), 'sha256': hashlib.sha256(data).hexdigest()}
    virtual_manifest = json.dumps({'files': files})


def read_bytes(path):
    if path == work_file:
        return source
    return original_read_bytes(path)


def read_text(path, *args, **kwargs):
    if path == manifest_path and virtual_manifest is not None:
        return virtual_manifest
    return original_read_text(path, *args, **kwargs)


Path.read_bytes = read_bytes
Path.read_text = read_text
scope = {'__file__': str(work_file), '__name__': '__read_only_preflight__'}
try:
    exec(compile(prefix, str(work_file), 'exec'), scope)
finally:
    Path.read_bytes = original_read_bytes
    Path.read_text = original_read_text
assert not scope['runtime'].exists()
print(json.dumps({'read_only_preflight_passed': True,
    'unique_bound_files_verified': len(scope['bound']),
    'current_Source_files': len(scope['current']),
    'selected_modules': len(scope['components']),
    'private_actual_session': scope['receipt']['actual_session'],
    'manifest_supplied_in_memory': virtual_manifest is not None,
    'Work_filename_supplied_virtually': True,
    'Work_Source_runtime_Git_compiler_mutations': False}))
