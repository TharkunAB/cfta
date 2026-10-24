import hashlib,json,subprocess
from pathlib import Path
root=Path('/home/tritlo/Code/mcfta');area=Path('/tmp/mcfta-pruning-record-types-20261024')
baseline='824808fb47ccd3ad7a4da2ff423f05c1dc8fa804';proof='83926524d89062128512a9d43814543dd921f953'
assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=root).decode().strip()==proof
note=area/'current-note.md';s=note.read_text();assert 'Proof:' not in s
s=s.replace('Main: `c4f7319acf84213fccc8ea389487d4176e4f0b62`, incorporated.','Main: `c4f7319acf84213fccc8ea389487d4176e4f0b62`, incorporated.\nProof: `'+proof+'`.')
note.write_text(s)
destination=root/'lean/notes-current-pruning-record-types.md';assert not destination.exists();destination.write_bytes(note.read_bytes())
prefix='''
## Type-position recording and callback observations

Updated: 2026-10-24. Main `c4f7319acf` is incorporated.
Proof: `83926524d89062128512a9d43814543dd921f953`.
Read `lean/notes-current-pruning-record-types.md`.

The concrete recordTypes callback now has checked metadata, compression-frame,
agreement, fuel-retention and finite-transport laws. Its empty catalog skips the
oracle while retaining the type update. The source selectors and three pure
position/rendering helpers preserve full labels, child order, raw IDs and
program-hole duplicates. Insertion has membership, sorting and uniqueness laws.
Global helper canonicality and native IntSet/Int/Text extraction remain open.

Both final modules pass strict Lean and the installed build. Audit passes 3678
jobs and 76071 dependency checks, with one older warning and no new-source
warning. All 40 signatures and 32 axiom reports were read. Only the standard
propext, Classical.choice and Quot.sound axioms occur. Every earlier failed
attempt and the frozen helper proposal remain in the evidence.

Next, implement the actual native node view needed by typedTypes. Mu-only
exemptions must retain union behavior, real nodeEdges and smart construction.
The enumeration-ID to stored-Value/history bridge remains open. No arbitrary
emptiness callback is sufficient. H6 remains strongest combined. H23 is queued.
Canonical histories, selected-current protection, cached scheduling, semantic
pruning, phase 4, resources, practical width, runtime/solver and convergence
remain open. No Haskell source changes. FINDINGS keeps its external repair index
FIRST: five fixes are on main; the trailing-hash repair still needs an import.
The full goal is ACTIVE and incomplete. This precedes the evidence commit and push.

'''
paths=list(json.loads(Path('/tmp/mcfta-derived-scalar-shape-20261024/document-changes.json').read_text()))
assert len(paths)==9
changes={}
for name in paths:
 p=root/name;before=p.read_text();assert p.read_bytes()==subprocess.check_output(['git','show',baseline+':'+name],cwd=root)
 position=before.index('## Generated scalar shape proof') if name=='FINDINGS.md' else before.index('\n')+1
 after=before[:position]+prefix+before[position:];p.write_text(after)
 changes[name]=dict(insertion_character=position,inserted=prefix,before_sha256=hashlib.sha256(before.encode()).hexdigest(),after_sha256=hashlib.sha256(after.encode()).hexdigest())
(area/'document-changes.json').write_text(json.dumps(changes,indent=2)+'\n')
(area/'proof-commit.json').write_text(json.dumps(dict(commit=proof,baseline=baseline,paths=['lean/MicroCFTA/SourcePruningPositions.lean','lean/MicroCFTA/SourcePruningRecordTypes.lean','lean/MicroCFTA/Audit.lean']),indent=2)+'\n')
print(json.dumps(dict(documents=paths,note=str(destination),proof=proof)))
