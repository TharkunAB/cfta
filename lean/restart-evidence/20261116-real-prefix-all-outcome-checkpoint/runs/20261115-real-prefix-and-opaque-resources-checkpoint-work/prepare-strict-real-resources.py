from pathlib import Path
import hashlib
import json
import shutil

work = Path(__file__).parent
base = Path('lean/restart-evidence')
old = base / '20261116-current-real-prefix-all-outcome-uniform-resource-repair'
new = base / '20261116-current-real-prefix-all-outcome-explicit-selection-repair'
new.mkdir()
name = 'SourcePruningEnumerationRealPrefixAllResources.lean'
text = (old / name).read_text()
needle = ' := by\n  classical\n  obtain ⟨_roots, _paths, _storage, realized, _counts, _flags⟩ := packet.valid'
assert text.count(needle) == 1
text = text.replace(needle, needle.replace('  classical\n', '  classical\n  clear chosen\n'))
(new / name).write_text(text)
for file in ['PUBLIC-HEADER.lean.txt', 'ZERO-HEADER.lean.txt', 'NONCONTINUING-HEADER.lean.txt',
             'PROBES.lean.txt', 'REMAINING-CONTINUING-TARGET-UNPROVED.lean.txt']:
    shutil.copyfile(old / file, new / file)
digest = hashlib.sha256((new / name).read_bytes()).hexdigest()
(new / 'REPAIR.json').write_text(json.dumps({'status':'UNCOMPILED','parent':str(old),
    'raw_sha256':digest,'all_public_headers_and_probes_exact':True,
    'proof_change':'Explicitly discard chosen, which the resource-only result does not need.',
    'no_linter_disabled':True,'algorithm_fuels_and_conclusions_unchanged':True}, indent=2) + '\n')
manifest = {p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(new.iterdir()) if p.is_file()}
(new / 'MANIFEST.json').write_text(json.dumps(manifest, indent=2) + '\n')
script = (work / 'prepare-all-and-continuing.py').read_text()
changes = {
    '20261116-current-real-prefix-all-outcome-scrutinee-repair':new.name,
    '682493f492e1f33c9ef0aeb8faef876aa8c48e40f3b8c41110654cb506e6dd77':digest,
    '20261116-current-real-prefix-continuing-resources-draft':'20261116-current-real-prefix-continuing-normalization-repair',
    '0a34a9f679d15f80b8ea2a14c9f4b962b3f879b76b2d8fbbe6da78eb265f8a13':'a4aa29f351942383e910ab40a9fd172e1eee6bef3b80f3601c9a2767a0dbf9f8',
    '20261116-native-real-all-and-continuing-check':'20261116-native-real-resources-strict-normalization-check'}
for before, after in changes.items():
    assert script.count(before) == 1, before
    script = script.replace(before, after)
(work / 'prepare-strict-check.py').write_text(script)
print(json.dumps({'raw_sha256':digest,'lines':len(text.splitlines()),'original_header_unchanged':True}))
