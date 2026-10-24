import hashlib,json,subprocess
from pathlib import Path
root=Path('/home/tritlo/Code/mcfta');area=Path('/tmp/mcfta-th-repair-main-20261024')
baseline='ed89dccbf8242231cde1abf87e52f909cb726470';main='74250bd889685da436cdbfe32ac4b5a0878ffd09';merge='ea9965949bdad994709318cf54162bea1c23cf40'
def git(*args):return subprocess.check_output(['git',*args],cwd=root)
assert git('rev-parse','HEAD').decode().strip()==merge and not git('status','--porcelain')
assert git('rev-parse',merge+'^{tree}')==git('rev-parse',baseline+'^{tree}')
(area/'merge.json').write_text(json.dumps(dict(commit=merge,parents=git('show','-s','--format=%P',merge).decode().split(),tree_equal_to=baseline,main=main),indent=2)+'\n')
p=root/'FINDINGS.md';original=p.read_text();old_header,rest=original.split('## Type-position recording and callback observations',1)
header=old_header
needle='Focused native repair probes pass. Historical counterexamples remain below.'
header=header.replace(needle,needle+'\nThe generated scalar-view name repair is merged in PR #172 at `74250bd88`.\nUpstream `f1f266ab4` has the same five files as local `07229ca7f3`.')
old='| Generated scalar-view names ending in # | Repaired on formalize at `07229ca7f3`. The producer rejects trailing-hash type and constructor names before namespace lookup. | Import the shared name check, two existing-suite regression cases and documentation. The repair is not on main. |'
new='| Generated scalar-view names ending in # | Fixed by `f1f266ab4`, merged in PR #172 at `74250bd88`. Its five source/package files equal local `07229ca7f3`. | No additional patch. Keep the producer rejection, regression cases and evidence. |'
assert header.count(old)==1;header=header.replace(old,new)
old='The first five repairs are in the imported main history. The generated-name\nrepair is on formalize and still needs an upstream import. General proofs\nremain separate. All earlier repair entries and evidence remain below.'
new='All six repairs are in the imported main history. General proofs remain\nseparate. All earlier repair entries and evidence remain below.'
assert old in header;header=header.replace(old,new)
old='External action: import `07229ca7f3208385a52c442965d8f2dcf73f7d99` from formalize.\nIt contains the generatedName suffix check, two rejection cases and documentation.\nDo not change the Node naming rule.'
new='External action: no additional patch. PR #172 merges the suffix check, both\nrejection cases and documentation. The five files equal local `07229ca7f3`.\nKeep the Node naming rule and the retained regression evidence.'
assert old in header;header=header.replace(old,new)
updated=header+'## Type-position recording and callback observations'+rest;p.write_text(updated)
(area/'findings-index-change.json').write_text(json.dumps(dict(before=old_header,after=header,before_sha256=hashlib.sha256(original.encode()).hexdigest(),after_sha256=hashlib.sha256(updated.encode()).hexdigest()),indent=2)+'\n')
note='''# Generated-name repair merged on main

Updated: 2026-10-24. Baseline: `ed89dccbf8242231cde1abf87e52f909cb726470`.
Main: `74250bd889685da436cdbfe32ac4b5a0878ffd09`, incorporated.
Merge: `ea9965949bdad994709318cf54162bea1c23cf40`.

PR #172 merges the trailing-hash generated-name repair at f1f266ab4.
Its five Haskell/package/document files are byte- and mode-identical to the
checked local repair07229ca7f3. The merge's complete Git tree equals the
baseline tree. No Haskell or Lean source contents change during this integration.

FINDINGS now marks all six recorded Haskell repairs as merged. The generated-name
row and detailed external action require no additional patch. Historical local
repair, original failures and red/green evidence remain retained. The shared
name check, both rejection cases and literal Node naming rule remain intact.

The existing focused Haskell suite, package checks and native probes apply to
the same five files. The strict Lean helpers/callback, installed build, public
signature/axiom reports and Audit also apply to the same proof-source bytes.
No successful check is repeated for this content-identical merge. The prior
checkpoint passed Audit3678 jobs and76071 dependency checks, with its one older
warning. All40 public signatures and32 permitted axiom reports remain checked.

H6 remains the strongest combined result. Covered closed source construction,
valid initial cache and original allocation history derive sufficient mathematical
width/fuel for any finite sequence of modeled node-call rounds. Empty inherited
payload gives exact finite-tree language equivalence. withoutRedundantEdges,
convergence and complete Haskell/runtime correspondence remain outside that result.
The new recordTypes observation results remain checked and separate.

Next, continue the concrete native node view for typedTypes. Preserve the Mu-only
exemptions, union closure, actual smart construction and constructor-cache history.
The enumeration-ID to stored-Value bridge, full helper canonicality, canonical
mutation histories, selected-current protection, cached-driver composition,
semantic pruning, phase4, resource use, practical width, runtime/solver and
convergence remain open. H23 stays queued. The full goal remains active.

Evidence is in restart-evidence/20261024-th-repair-main. Its verifier checks all
127926 baseline blobs and modes, exact nine documentation additions and the
current repair-index change. It verifies merge parents and whole-tree equality,
main's exact five-path delta and source identities. Previous-publication retains
the preceding proof checkpoint's post-seal publication receipts. Earlier sealed
evidence, proofs, counterexamples, repairs, drafts and optimized interned code remain.
'''
(area/'current-note.md').write_text(note);dst=root/'lean/notes-current-th-repair-main.md';assert not dst.exists();dst.write_text(note)
prefix='''
## Generated-name repair merged on main

Updated: 2026-10-24. Main `74250bd88` is incorporated.
Merge: `ea9965949bdad994709318cf54162bea1c23cf40`.
Read `lean/notes-current-th-repair-main.md`.

PR #172 merges the trailing-hash generated-name repair. Its five files equal
local `07229ca7f3` byte for byte and mode for mode. The merge tree equals the
previous pushed tree. No Haskell or Lean source contents change. Existing
validation applies to the same bytes; no successful check is repeated.
FINDINGS keeps the repair index FIRST and marks all six fixes merged.
No external patch remains for these six recorded defects. General proofs stay open.

The checked recordTypes and position-helper observation results remain.
H6 remains strongest combined. Next continue the concrete Mu-only native node
view and enumeration-ID/cache-history bridge for typedTypes. Global helper
canonicality, mutation histories, selected-current protection, cached scheduling,
semantic pruning, phase 4, resources, practical width, runtime/solver and
convergence remain open. H23 stays queued. The full goal is ACTIVE and incomplete.
This record precedes evidence creation and the authorized push.

'''
paths=list(json.loads(Path('/tmp/mcfta-pruning-record-types-20261024/document-changes.json').read_text()));changes={}
for name in paths:
 p=root/name;before=p.read_text()
 if name!='FINDINGS.md':assert p.read_bytes()==git('show',baseline+':'+name)
 position=before.index('## Type-position recording and callback observations') if name=='FINDINGS.md' else before.index('\n')+1
 after=before[:position]+prefix+before[position:];p.write_text(after)
 changes[name]=dict(insertion_character=position,inserted=prefix,before_sha256=hashlib.sha256(before.encode()).hexdigest(),after_sha256=hashlib.sha256(after.encode()).hexdigest())
(area/'document-changes.json').write_text(json.dumps(changes,indent=2)+'\n')
print(json.dumps(dict(main=main,merge=merge,documents=len(paths),repairs_merged=6)))
