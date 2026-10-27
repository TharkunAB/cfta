from pathlib import Path
import hashlib
import json
import re
import subprocess

root = Path('/home/tritlo/Code/mcfta')
area = Path('/tmp/mcfta-native-history-proper-20261027')
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
note = root / 'lean/notes-current-native-history-proper.md'
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
assert len(commands) == 34
assert len([r for r in commands if r['report']['exit_code']]) == 7
(area / 'actual-commands.json').write_text(json.dumps(commands, indent=2) + '\n')
documents = json.loads((area / 'document-paths.json').read_text())
(area / 'current-document-changes.patch').write_bytes(subprocess.check_output(
    ['git', 'diff', '--', *documents], cwd=root))
(review / 'report.md').write_text("""# Root final source review

All fourteen final modules and all twenty-one complete new public statements
were read. Eight ENTIRE original declarations remain after theorem rename,
one outer group and the appended observer. Their literal comparisons pass.
Seven wrappers call the old producer once. The native branch wrapper follows
the actual old selected-list induction with one strengthened head call per
processed head. It observes that receipt's own cache and keeps full Memos.

The startup wrapper keeps all original admission and resources. Literal startup
and the SAME emitted output's actual ResourceHistory derive proper storage
without a new invariant or model input. Stopped attached local caches remain
covered. Aggregate zero-output cache history, policy semantics, coverage,
discharge/render coverage, public admission and physical correspondence remain
open. H6 and conditional rendered soundness keep their previous scopes.

All final strict sources, Audit and full public readback pass. Seven actual
failed proof attempts and all source snapshots remain. Result generalization
annotations change observer syntax but add no gate. Native head and branch
repairs change only proof bodies. Catalogue and evidence-helper corrections
cause no additional proof check. Thirty-four actual commands run serially
under measured4GiB memory.high/max and zero swap.

The entire new note and all current document insertion bytes were read.
Eight common insertions are byte-identical and one FINDINGS insertion also
contains the KBO repair status. All nine whole old bodies are preserved.
No claim of whole-file reading of the giant older documents is made.

The imported two-file KBO repair equals main. Golden and actual public-API
context/generated-weight witnesses pass; exact Natural weight63 exceeds Int.
This closes the specific weight-overflow finding, not general KBO laws.
The full golden build/linker output is retained; only its build prefix and
suite result tail were read. No benchmark or local Haskell edit occurred.

Three independent bounded reviews have separate final source pins and seals.
Older constructor/equality proofs, repairs, counterexamples and all prior
frozen evidence remain unchanged. Goal ACTIVE.
""")
print(json.dumps(dict(status='pass', root_source_records=len(sources), actual_commands=len(commands))))
