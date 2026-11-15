from pathlib import Path
import hashlib
import json
import shutil

work = Path(__file__).parent
base = Path('lean/restart-evidence')
old = base / '20261116-current-real-prefix-all-outcome-scrutinee-repair'
new = base / '20261116-current-real-prefix-all-outcome-uniform-resource-repair'
new.mkdir()
name = 'SourcePruningEnumerationRealPrefixAllResources.lean'
text = (old / name).read_text()
before = '''              | some action =>
                  split
                  · split
                    · exact reachedResources
                    · split
                      · exact reachedResources
                      · split <;> exact reachedResources
                  · exact reachedResources'''
after = '''              | some action =>
                  repeat' first
                  | exact reachedResources
                  | split'''
assert text.count(before) == 1
text = text.replace(before, after)
assert text.count('  clear actual\n') == 1
text = text.replace('  clear actual\n', '')
(new / name).write_text(text)
files = ['PUBLIC-HEADER.lean.txt', 'ZERO-HEADER.lean.txt', 'NONCONTINUING-HEADER.lean.txt',
    'PROBES.lean.txt', 'REMAINING-CONTINUING-TARGET-UNPROVED.lean.txt']
for file in files:
    shutil.copyfile(old / file, new / file)
    assert (new / file).read_bytes() == (old / file).read_bytes()
digest = hashlib.sha256((new / name).read_bytes()).hexdigest()
(new / 'REPAIR.json').write_text(json.dumps({'status':'UNCOMPILED','parent':str(old),
    'raw_sha256':digest,'all_public_headers_and_probes_exact':True,
    'changes':['Use the same reached resources at every action-result leaf; split only when needed.',
        'Retain actual equation because the dependent noncontinuing hypothesis uses it.'],
    'algorithm_fuels_and_predicates_unchanged':True}, indent=2) + '\n')
(new / 'README.md').write_text('''# All-outcome resource proof repair

Uncompiled. All three public headers and probes remain byte-exact.
Resources ignores the action-result fields of a narrowed result. Every such
leaf uses the same reached caller and heap. Split only the remaining matches.
Keep the actual equation because the noncontinuing hypothesis depends on it.
The complete continuing-prefix target remains separate and open.
''')
manifest = {p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(new.iterdir()) if p.is_file()}
(new / 'MANIFEST.json').write_text(json.dumps(manifest, indent=2) + '\n')
script = (work / 'prepare-real-typing.py').read_text()
script = script.replace('20261116-current-real-prefix-all-outcome-typing-repair', new.name)
script = script.replace('20261115-current-real-prefix-all-outcome-resources-draft', old.name)
script = script.replace('f350538dffec54109541e43449e402c0c9a2482db647236e620efb09e95a6340', digest)
script = script.replace('20261116-native-real-prefix-all-outcome-typing-check', '20261116-native-real-prefix-uniform-resource-check')
(work / 'prepare-uniform-check.py').write_text(script)
print(json.dumps({'raw_sha256':digest,'lines':len(text.splitlines()),'public_headers_preserved':True}))
