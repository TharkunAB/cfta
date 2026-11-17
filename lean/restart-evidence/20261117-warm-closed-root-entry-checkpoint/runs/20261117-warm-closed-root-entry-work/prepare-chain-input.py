from pathlib import Path
import hashlib
import json
import sys

root = Path('/home/tritlo/Code/mcfta')
base = root / 'lean/restart-evidence'
work = Path(__file__).parent
packet = base / '20261117-closed-root-warm-entry-chain-metadata-repair'
key = sys.argv[1]
sha = lambda data: hashlib.sha256(data).hexdigest()
manifest = packet / 'MANIFEST.sha256'
assert sha(manifest.read_bytes()) == '5c42cb61700ffbea8ac54d6cda2f32dc921fe95c393db5e341d622343240a715'
for line in manifest.read_text().splitlines():
    digest, name = line.split(None, 1)
    assert sha((packet / name.strip().lstrip('*')).read_bytes()) == digest, name
layout = next(item for item in json.loads((packet / 'NORMAL-SOURCE-LAYOUT.json').read_text())['layouts']
              if item['key'] == key)
owner = root / layout['owner']
old = owner.read_bytes()
assert len(old) == layout['base_bytes'] and sha(old) == layout['base_sha256']
snapshot = work / (owner.stem + '-BEFORE.lean.txt')
if not snapshot.exists():
    baseline = json.loads((work / 'baseline-source-pins.json').read_text())
    assert sha(old) == baseline[layout['owner']]
    snapshot.write_bytes(old)
append = (packet / (key.upper() + '-APPEND.lean.txt')).read_bytes()
assert sha(append) == layout['append_sha256']
raw = old + b'\n' + append
assert sha(raw) == layout['expected_pure_source_sha256']
header = (packet / (key.upper() + '-FIRST-HEADER.lean.txt')).read_bytes()
declaration = header[header.index(b'theorem '):].rstrip()
start = raw.index(declaration.splitlines()[0] + b'\n')
assert raw[start:raw.index(b' := by', start)].rstrip() == declaration
input_dir = base / ('20261117-closed-root-chain-' + key + '-check-input')
input_dir.mkdir()
(input_dir / owner.name).write_bytes(raw)
(input_dir / 'FIRST-HEADER.lean.txt').write_bytes(header)
(input_dir / 'PROBES.lean.txt').write_bytes((packet / layout['check_extra']).read_bytes())
binding = {'packet': packet.name, 'manifest_sha256': sha(manifest.read_bytes()),
           'key': key, 'owner': layout['owner'], 'base_sha256': sha(old),
           'base_bytes': len(old), 'old_owner_exact_prefix': True,
           'raw_sha256': sha(raw), 'original_header_file_sha256': sha(header),
           'declaration_content_byte_exact_excluding_trailing_padding': True,
           'new_theorem_reports': 1, 'normal_source_changed': False,
           'physical_interface_only': True, 'joint_finite_completion_proved': False}
(input_dir / 'ORIGINAL-PACKET-BINDING.json').write_text(json.dumps(binding, indent=2) + '\n')
files = {p.name: {'sha256': sha(p.read_bytes()), 'bytes': p.stat().st_size}
         for p in input_dir.iterdir() if p.is_file()}
(input_dir / 'MANIFEST.json').write_text(json.dumps({'files': files}, indent=2) + '\n')
print(json.dumps({'input': input_dir.name, 'module': owner.stem, 'sha256': sha(raw),
                  'expected_reports': 1, 'normal_source_changed': False}))
