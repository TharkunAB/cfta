import hashlib
import json
import shutil
from pathlib import Path

root = Path('/home/tritlo/Code/mcfta')
area = Path('/tmp/mcfta-native-references-20261025')
evidence = root / 'lean/restart-evidence/20261025-native-references'
old = '''Actual terminal, child, traversal and selected-edge completion now retain
fixed allowed references and global pending-reference history. Selected-edge
completion also preserves incoming avoidance of a protected old root.
'''
new = '''Actual terminal, child and traversal completion now retain fixed allowed
references. These producers and selected-edge completion preserve global
pending-reference history. Selected-edge completion also preserves incoming
avoidance of a protected old root.
'''
documents = ['NEXT-PROMPT.md', 'HANDOFF.md', 'FINDINGS.md', 'lean/README.md',
             'lean/SYSTEM.md', 'lean/COVERAGE.md', 'lean/API-COVERAGE.md',
             'lean/notes-current-system-claim.md', 'lean/notes-proof-status-20261017.md']
for relative in documents:
    path = root / relative
    text = path.read_text()
    assert text.count(old) == 1
    path.write_text(text.replace(old, new, 1))
shutil.copyfile(area / 'refine-summary.py', evidence / 'refine-summary.py')
sha = lambda data: hashlib.sha256(data).hexdigest()
manifest = {str(p.relative_to(evidence)): dict(bytes=p.stat().st_size, sha256=sha(p.read_bytes()))
            for p in sorted(evidence.rglob('*')) if p.is_file() and p.name != 'manifest.json'}
(evidence / 'manifest.json').write_text(json.dumps(manifest, indent=2) + '\n')
print(json.dumps(dict(payloads=len(manifest), total_bytes=sum(v['bytes'] for v in manifest.values()),
                     manifest_sha256=sha((evidence / 'manifest.json').read_bytes()))))
