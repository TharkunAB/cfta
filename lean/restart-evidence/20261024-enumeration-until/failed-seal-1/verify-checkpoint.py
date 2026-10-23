"""Check retained enumeration evidence and its live source identities without Lean."""
import argparse
import gzip
import hashlib
import json
import re
from pathlib import Path

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--root', required=True, type=Path)
args = parser.parse_args()
root = args.root.resolve()
here = root/'lean/restart-evidence/20261024-enumeration-until'
def sha(data):
    return hashlib.sha256(data).hexdigest()
def load(name):
    return json.loads((here/name).read_text())

manifest = {}
for line in (here/'SHA256SUMS').read_text().splitlines():
    digest, name = line.split('  ', 1)
    assert name not in manifest and not Path(name).is_absolute() and '..' not in Path(name).parts
    manifest[name] = digest
actual = {p.relative_to(here).as_posix() for p in here.rglob('*') if p.is_file()}
assert actual == set(manifest) | {'SHA256SUMS'}
for name, digest in manifest.items():
    assert sha((here/name).read_bytes()) == digest, name

baseline = json.loads(gzip.decompress((here/'work/starting-files.json.gz').read_bytes()))
changes = load('work/document-changes.json')
assert len(baseline) == 126320
changed = []
for name, entry in baseline.items():
    path = root/name
    data = path.read_bytes()
    assert ('100755' if path.stat().st_mode & 0o111 else '100644') == entry['mode'], name
    if sha(data) == entry['sha256']:
        continue
    changed.append(name)
    if name == 'lean/MicroCFTA/Audit.lean':
        addition = b'import MicroCFTA.EnumerationUntilBridge\n'
        assert data.startswith(addition) and sha(data[len(addition):]) == entry['sha256']
    else:
        change = changes[name]
        text = data.decode()
        index, addition = change['insertion_character'], change['inserted']
        assert text[index:index+len(addition)] == addition
        assert sha((text[:index]+text[index+len(addition):]).encode()) == entry['sha256']
        assert sha(data) == change['after_sha256']
assert set(changed) == set(changes) | {'lean/MicroCFTA/Audit.lean'}

for name in ['EnumerationUntil.lean', 'EnumerationUntilBridge.lean', 'Audit.lean']:
    assert (root/'lean/MicroCFTA'/name).read_bytes() == (here/'production-sources'/name).read_bytes()
assert not re.search(r'\b(?:sorry|admit|axiom|unsafe)\b',
    (root/'lean/MicroCFTA/EnumerationUntil.lean').read_text() +
    (root/'lean/MicroCFTA/EnumerationUntilBridge.lean').read_text())

reports = list((here/'work').glob('*/report.json'))
assert len(reports) == 12
for path in reports:
    report = json.loads(path.read_text())
    raw = (path.parent/'raw.log').read_bytes()
    assert len(raw) == report['raw_bytes'] and sha(raw) == report['raw_sha256']
    if 'source_sha256' in report:
        sources = list(path.parent.rglob('*.lean'))
        assert len(sources) == 1 and sha(sources[0].read_bytes()) == report['source_sha256']
        assert '-DwarningAsError=true' in report['command'] and '-Dlinter.all=true' in report['command']

assert load('work/combined-check-5/report.json')['exit_code'] == 0
assert (here/'work/combined-check-5/raw.log').read_bytes() == b''
for name in ['focused-build-1', 'audit-1', 'public-2']:
    assert load('work/'+name+'/report.json')['exit_code'] == 0
audit = (here/'work/audit-1/raw.log').read_text()
assert 'Checked axiom dependencies of 75635 MicroCFTA theorems.' in audit
assert 'Build completed successfully (3659 jobs).' in audit
assert audit.count('warning:') == 1 and 'InternedFreshOrdinaryClosedCompletion.lean:24:5' in audit
public = (here/'work/public-2/raw.log').read_text()
assert sum(line.startswith('MicroCFTA.') for line in public.splitlines()) == 21
axioms = re.findall(r"'MicroCFTA\.[^']+' (?:depends on axioms: \[(.*?)\]|(does not depend on any axioms))", public, re.S)
assert len(axioms) == 12
for names, empty in axioms:
    if not empty:
        assert {name.strip().split('.{', 1)[0] for name in names.split(',')} <= {'propext', 'Classical.choice', 'Quot.sound'}
assert not re.search(r':\d+:\d+: (?:error|warning)', public)
for path in (here/'inputs').glob('*.limits.json'):
    assert json.loads(path.read_text()) == {'memory.max':'4294967296', 'memory.high':'4294967296', 'memory.swap.max':'0'}
for path in (here/'inputs').glob('*.usage.json'):
    usage = json.loads(path.read_text())
    assert 0 <= usage['age_seconds'] <= 600 and usage['remaining_percent'] > 1
assert load('work/preservation.json')['status'] == 'PASS'
print(json.dumps(dict(status='PASS', sealed_files=len(manifest), baseline_files=len(baseline),
                     preserved_earlier_files=len(baseline)-len(changed), retained_attempts=len(reports),
                     complete_checked_signatures=21, axiom_reports=12, new_lean_jobs=0,
                     goal='ACTIVE_INCOMPLETE'), indent=2))
