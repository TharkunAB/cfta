from pathlib import Path
import hashlib
import json
import re
import subprocess

root = Path('/home/tritlo/Code/mcfta')
area = Path('/tmp/mcfta-native-proper-20261027')
review = area / 'root-source-review'
review.mkdir()


def digest(data):
    return hashlib.sha256(data).hexdigest()


sources = []
modules = json.loads((area / 'modules.json').read_text())
for module in modules:
    source = root / 'lean/MicroCFTA' / (module + '.lean')
    data = source.read_bytes()
    copy = review / 'sources' / source.name
    copy.parent.mkdir(exist_ok=True)
    copy.write_bytes(data)
    sources.append(dict(source=str(source), whole=dict(path=str(copy.relative_to(review)),
        bytes=len(data), sha256=digest(data)), cuts=[],
        review_scope='Whole final module read. Versioned draft and failed-check lineage remain separately recorded.'))
for relative in ['new-public-blocks.txt', 'root-contract-comparisons.json',
        'public-prefix-comparison.json', 'source-validation.json', 'preservation-validation.json']:
    source = area / relative
    data = source.read_bytes()
    copy = review / 'sources' / relative
    copy.write_bytes(data)
    sources.append(dict(source=str(source), whole=dict(path=str(copy.relative_to(review)),
        bytes=len(data), sha256=digest(data)), cuts=[], review_scope='Whole record read.'))
note = root / 'lean/notes-current-native-proper.md'
copy = review / 'sources' / note.name
data = note.read_bytes()
copy.write_bytes(data)
sources.append(dict(source=str(note), whole=dict(path=str(copy.relative_to(review)),
    bytes=len(data), sha256=digest(data)), cuts=[], review_scope='Whole current note read.'))
for record in json.loads((area / 'document-validation.json').read_text()):
    if 'inserted_bytes' not in record:
        continue
    source = root / record['path']
    data = source.read_bytes()
    old = (area / 'prior-documents' / record['path']).read_bytes()
    begin = record['offset']
    end = begin + record['inserted_bytes']
    assert data[:begin] + data[end:] == old
    inserted = data[begin:end]
    copy = review / 'insertions' / (record['path'].replace('/', '__') + '.txt')
    copy.parent.mkdir(exist_ok=True)
    copy.write_bytes(inserted)
    first = len(data[:begin].splitlines()) + 1
    last = first + len(inserted.splitlines()) - 1
    sources.append(dict(source=str(source), source_bytes=len(data), source_sha256=digest(data),
        reconstruction=dict(prior=dict(path=str(area / 'prior-documents' / record['path']),
            bytes=len(old), sha256=digest(old)), insert=dict(path=str(copy),
            bytes=len(inserted), sha256=digest(inserted)), offset=begin),
        cuts=[dict(path=str(copy.relative_to(review)), bytes=len(inserted), sha256=digest(inserted),
            first_line=first, last_line=last)],
        review_scope='Only the exact inserted current section was read. Whole older body preserved and checked by inverse.'))
(review / 'source-index.json').write_text(json.dumps(dict(sources=sources), indent=2) + '\n')
commands = []
for path in sorted(area.glob('*/report.json')):
    result = json.loads(path.read_text())
    raw = (path.parent / 'raw.log').read_bytes()
    assert len(raw) == result['bytes'] and digest(raw) == result['sha256']
    assert result['cgroup_limits'] == {'memory.max': '4294967296', 'memory.high': '4294967296', 'memory.swap.max': '0'}
    commands.append(dict(name=path.parent.name, report=result))
assert len(commands) == 27
assert [r['name'] for r in commands if r['report']['exit_code']] == ['child-proper-strict-1', 'terminal-proper-strict-1']
(area / 'actual-commands.json').write_text(json.dumps(commands, indent=2) + '\n')
documents = json.loads((area / 'document-paths.json').read_text())
(area / 'current-document-changes.patch').write_bytes(subprocess.check_output(
    ['git', 'diff', '--', *documents], cwd=root))
(review / 'report.md').write_text('''# Root current source review

All fourteen final modules and all thirty new full public statements were read.
The old startup declaration (1350 bytes) and captured resource declaration
(5913 bytes) are retained exactly after rename, grouping and added conclusions.
Each old producer is called once. The same actual endpoints and constructed
model supply the appended progress guarantee. No producer admission is added.

Successful traversal and selected/captured preservation require actual complete
execution. Rejected attached-cache observers have their own stronger statements.
ProperInputs differs from ProperTrie. Captured storage derives inherited validity.
ProperState does not establish Safe or Packet on arbitrary rejected caches.
Full recursive origin, policy pruning and whole-system coverage remain open.

All final strict checks, aggregate Audit and public readback pass. Two actual
elaboration failures and their unchanged-statement proof repairs remain intact.
No proof source or check was rerun for an evidence helper. No Haskell source,
Cabal file, native test or benchmark changed or ran. The new note and all nine
current document insertions were read. Each whole older body is retained.

This root record does not claim whole-file review of the large old restart
documents or unlisted operational source files. The source index marks actual
whole reads and exact current insertion cuts. The three independent bounded
reviews have their own source provenance and final seals.
''')
print(json.dumps(dict(status='pass', root_source_records=len(sources), actual_commands=len(commands))))
