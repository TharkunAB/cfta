import difflib
import re
from pathlib import Path

root = Path('/home/tritlo/Code/mcfta')
basis = Path('/tmp/mcfta-pair-node-counter-growth-bootstrap.py')
saved = root / 'lean/restart-evidence/20261023-pair-node-counter-growth/completed-root-support/mcfta-pair-node-counter-growth-bootstrap.py'
assert basis.read_bytes() == saved.read_bytes()
text = basis.read_text()
replacements = {
    '20261023-demand-node-counter-growth':'20261023-pair-node-counter-growth',
    '20261023-pair-node-counter-growth':'20261023-scan-node-counter-growth',
    'mcfta-demand-node-counter-growth':'mcfta-pair-node-counter-growth',
    'mcfta-pair-node-counter-growth':'mcfta-scan-node-counter-growth',
    'codex/backup-pair-node-counter-growth-':'codex/backup-scan-node-counter-growth-',
    'SourceEqualityNativeDemandNodeCounterGrowth':'SourceCurrentSameSymbolEdgeControlNodeCounterGrowth',
    'SourceCurrentSameSymbolEdgeControlNodeCounterGrowth':'SourceCurrentOriginalRowClusterScanNodeCounterGrowth',
    'de085728ebe1e905ae339eaba8d26348126e5ada':'527a5cd981b6b406cf7078ac2fe96c288379afb7',
    '86b6dd30387c62a1f8f46e1914824695c4a0e908':'de085728ebe1e905ae339eaba8d26348126e5ada',
    '7bdd945140a975dd1537be82d71ce5e34bf40fc3ceef0df3a9d3d5972d02c4ca':'4b39f17903d76604a38774c485883d9b7ceeebf07aba9d2aac063a0064874057',
    '122017':'124005','3654':'3655','3144':'3145'}
assert all(old in text for old in replacements)
changed = re.sub('|'.join(re.escape(old) for old in replacements),lambda match:replacements[match.group()],text)
prefix,tail = changed.split("(HERE / 'current-progress.md').write_text('''",1)
_old_note,suffix = tail.split("''')",1)
note = '''# Cluster scan node-counter growth

H37 was sealed, pushed and remote-verified at 527a5cd981b6b406cf7078ac2fe96c288379afb7.
The full formalization goal remains ACTIVE and incomplete.
The next component is actual Scan step and finite execute node-counter growth.
Retain the complete pair State from all five actual Scan outcomes.
Define one public total outcomeState in the new module. It needs no equality instance.
Both theorems use the two existing inline equality instances.
Use H37 at the same actual inner control and full pair state.
Cluster and scan list transitions retain the complete state.
Every comparison result forwards its actual after state, including failed and blocked outcomes.
State projection discards the returned control. Do not split the identity tests.
Fuel induction retains the actual yielded next control and complete state.
Do not assume validity, readiness, success, completion or a desired counter bound.
Neither the defining Scan module nor its pair module defines resume.
Fresh investigation, exact declaration and whole body reviews precede compilation.
No declaration, body or compiler result is claimed at this bootstrap.
The next lift composes the actual finite Scan trace and final rebuild through H23.
Fixed-source initial counter order and original global domain history remain separate.
Earlier H23 conditional completion and language preservation remain proved.
Full-pipeline upper resources, Room, WordRanges, generated execution, Mu/full pass,
practical width, Haskell and solver correspondence, and convergence remain open.
H6 constructed_node_calls remains strongest combined.
Keep the optimized interned core and all older constructor and equality work.
No Haskell repair is proposed. FINDINGS keeps its external repair index first.
No board operation, memory write or ADR is added.
'''
changed = prefix + "(HERE / 'current-progress.md').write_text('''" + note + "''')" + suffix
target = Path('/tmp/mcfta-scan-node-counter-growth-bootstrap.py')
assert not target.exists()
target.write_text(changed)
Path('/tmp/mcfta-scan-node-counter-growth-bootstrap.patch').write_text(''.join(difflib.unified_diff(text.splitlines(True),changed.splitlines(True),fromfile=str(basis),tofile=str(target))))
print('Prepared the literal bootstrap adaptation and its complete forward diff.')
