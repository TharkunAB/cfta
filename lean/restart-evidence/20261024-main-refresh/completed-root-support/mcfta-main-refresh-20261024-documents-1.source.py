import hashlib
import json
import subprocess
from pathlib import Path

root = Path('/home/tritlo/Code/mcfta')
out = Path('/tmp/mcfta-main-refresh-20261024')
assert subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=root, text=True).strip() == '058b11fe8f3706460156d7a1fc454063406a4634'
assert not subprocess.check_output(['git', 'status', '--porcelain'], cwd=root)
update = Path('/tmp/mcfta-main-refresh-20261024-update.md').read_text()
documents = ['NEXT-PROMPT.md', 'HANDOFF.md', 'FINDINGS.md', 'lean/README.md',
             'lean/SYSTEM.md', 'lean/API-COVERAGE.md', 'lean/COVERAGE.md',
             'lean/notes-proof-status-20261017.md', 'lean/notes-current-system-claim.md']
changes = {}
for name in documents:
    path = root / name
    before = path.read_bytes()
    text = before.decode()
    if name == 'FINDINGS.md':
        old = 'No new Haskell repair is required by this proof checkpoint.'
        assert text.count(old) == 1
        text = text.replace(old, 'The negative type-depth repair is fixed locally in `058b11fe8f`.\nTwo optional LPO repairs remain open. Native counterexamples are retained below.', 1)
        old = '| Repair | Imported status | External action |'
        assert text.count(old) == 1
        text = text.replace(old, '| Repair | Current status | External action |', 1)
        old = 'at current imported main `794903b3f`'
        assert text.count(old) == 1
        text = text.replace(old, 'at the earlier imported main `794903b3f`', 1)
        anchor = '\nBoth repairs are in the imported main history. No Haskell source changes\nin this checkpoint. All earlier repair entries and evidence remain below.\n'
        assert text.count(anchor) == 1
        rows = ('| Negative Specftacular type depth | Fixed locally in `058b11fe8f`; CLI, search and grammar entries reject it. The pre-fix call timed out. | Import this commit into main. |\n'
                '| Optional LPO comparator transitivity | OPEN. Native well-typed terms give `s < t < u < s`, also after canonicalTypes. | Repair annotation handling and the order fallback. See the retained comparator regression. |\n'
                '| Optional LPO application context | OPEN. Native terms give `f a > a` and `(f a) x < a x`. | Establish an order compatible with function application and actual rewriting. The annotation repair alone is insufficient. |\n')
        text = text.replace(anchor, rows + '\nThe two earlier repairs remain in the imported main history. The local\ntype-depth fix and both open LPO repairs are recorded in the current note.\nAll earlier repair entries and evidence remain below.\n\n' + update, 1)
        assert text.index('## Haskell fix handoff for external work') < text.index('## Imported main:')
    else:
        head, separator, tail = text.partition('\n\n')
        assert separator
        text = head + separator + update + '\n' + tail
        assert text.replace(update + '\n', '', 1).encode() == before
    path.write_text(text)
    changes[name] = {'before_sha256': hashlib.sha256(before).hexdigest(),
                     'after_sha256': hashlib.sha256(path.read_bytes()).hexdigest()}
note = root / 'lean/notes-current-upstream-program-enumeration.md'
assert not note.exists()
note.write_bytes(Path('/tmp/mcfta-main-refresh-20261024-note.md').read_bytes())
(out / 'document-changes.json').write_text(json.dumps(changes, indent=2) + '\n')
subprocess.run(['git', 'diff', '--check'], cwd=root, check=True)
print(json.dumps({'status': 'PASS', 'documents': len(changes), 'focused_note': str(note),
                  'external_haskell_repairs_first': True, 'open_LPO_repairs': 2}))
