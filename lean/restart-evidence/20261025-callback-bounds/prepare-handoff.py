import hashlib
import json
import re
import shutil
import subprocess
from pathlib import Path

root = Path('/home/tritlo/Code/mcfta')
area = Path('/tmp/mcfta-callback-bounds-20261025')
evidence = root / 'lean/restart-evidence/20261025-callback-bounds'
base = '9befafd4bd8b4487e9866de327ae457b0a84d60c'
sha = lambda data: hashlib.sha256(data).hexdigest()
old_source = lambda relative: subprocess.check_output(['git', 'show', base + ':' + relative], cwd=root).decode()
checks = {p.parent.name: json.loads(p.read_text()) for p in sorted(area.glob('*/report.json'))}
strict = {name for name in checks if name.startswith('strict-')}
failed = {name for name, report in checks.items() if report['exit_code'] != 0}
assert len(checks) == 18 and len(strict) == 12
assert failed == {'strict-render-bounds-1', 'strict-match-bounds-1', 'strict-match-bounds-2',
                  'strict-match-bounds-3', 'strict-resume-bounds-1', 'strict-resume-bounds-2'}
final_strict = {'strict-render-bounds-2', 'strict-match-bounds-4', 'strict-template-bounds-1',
                'strict-resume-bounds-3', 'strict-oracle-bounds-1', 'strict-callback-bounds-1'}
assert not failed.intersection(final_strict)
public_bytes = (area / 'public-final/raw.log').read_bytes()
public = public_bytes.decode()
assert public.count('depends on axioms:') == 13 and '⋯' not in public and '...' not in public
for axioms in re.findall(r'depends on axioms:\s*\[([^]]*)\]', public):
    assert set(re.findall(r'[A-Za-z_.]+', axioms)) <= {'propext', 'Classical.choice', 'Quot.sound'}
assert 'Checked axiom dependencies of 76809 MicroCFTA theorems.' in (area / 'aggregate-audit/raw.log').read_text()

sources = ['lean/MicroCFTA/' + name + '.lean' for name in [
    'EnumerationPartialBounds', 'SourcePruningPartialMatch', 'SourcePruningTemplates',
    'SourcePruningResume', 'SourcePruningOracle', 'SourcePruningCallbackCompletion']]
markers = {
    'SourcePruningPartialMatch': '/-- A successful partial match parks only holes',
    'SourcePruningTemplates': '/-- Program selection retains the allocated-hole bound',
    'SourcePruningResume': 'private theorem parts_bounded',
    'SourcePruningOracle': '/-- A completed fragment callback returns only allocated',
    'SourcePruningCallbackCompletion': '/-- A completed fragment event keeps every returned pending ID',
}
for module, marker in markers.items():
    relative = 'lean/MicroCFTA/' + module + '.lean'
    old = old_source(relative)
    current = (root / relative).read_text()
    if module == 'SourcePruningPartialMatch':
        assert current.count('import MicroCFTA.EnumerationPartialBounds\n') == 1
        current = current.replace('import MicroCFTA.EnumerationPartialBounds\n', '', 1)
        start = current.index('/-- Every parked match names an allocated variable. -/')
        stop = current.index('mutual\n', start)
        current = current[:start] + current[stop:]
    if module == 'SourcePruningResume':
        start = current.index('private theorem sequenced_bounded')
        stop = current.index('variable {Symbol Guard : Type}', start)
        current = current[:start] + current[stop:]
    namespace = 'SourcePruningRecordTypes' if module == 'SourcePruningCallbackCompletion' else module
    assert current[:current.index(marker)].rstrip() == old[:old.index('end MicroCFTA.' + namespace)].rstrip(), module
unchanged = ['lean/MicroCFTA/' + name + '.lean' for name in [
    'Audit', 'EnumerationState', 'EnumerationCorrectness', 'EnumerationOrder', 'EnumerationReferences',
    'EnumerationDriver', 'EnumerationPartialObservation', 'EnumerationPartialCompletion',
    'SourcePruningRecordTypes', 'SourcePruningEnumerationSelectedOrdinary',
    'SourcePruningEnumerationNativeBranchCompletion', 'SourcePruningEnumerationNativeOrdinary',
    'SourceCurrentColdFiniteWarmCalls']]
unchanged += ['cfta/src/Data/CFTA/' + name for name in [
    'Enumeration.hs', 'Interned/Type.hs', 'Interned/Cache.hs', 'Interned/Memo.hs', 'Interned/Operations.hs']]
for relative in unchanged:
    assert old_source(relative) == (root / relative).read_text(), relative
subprocess.run(['git', 'diff', '--quiet', base, '--', '*.hs', '*.cabal'], cwd=root, check=True)
for relative in sources:
    assert not re.search(r'\b(sorry|admit|axiom)\b', (root / relative).read_text()), relative

block = '''## Concrete callbacks preserve allocated pending IDs

Rendering and match bounds: `3c1d159ff`. Callback result: `f6f7985dc`.
The goal stays ACTIVE.

The concrete Left callback now returns allocated IDs for every pending
group in its actual metadata result. The proof covers rendered holes,
selected programs, new matches, compressed parked representatives and
final filtering. Bounds hold for accepted and rejected results alike.
The strengthened producer uses the same completion witness and cache.
The earlier completion interfaces and runtime workers stay unchanged.

All six changed modules pass strict checking. Installed public readback
and Audit pass. Audit checks 76809 dependencies. H6 remains the strongest
end-to-end language result. Haskell and Audit source stay unchanged.
Next: establish and preserve Stratified through native traversal, pending
merges and final writes. Derive returned-hole targets at each endpoint.
Then compose Left callbacks with actual branch caches, metadata and
native Graph classifications. Initial-only numeric admission, scheduler
restart, arbitrary forcing, extraction and whole-driver semantics remain.
Bounds for all other metadata fields and machine Ints are not established.
Details: `lean/notes-current-pruning-enumeration-callback-bounds.md`.

'''
documents = ['NEXT-PROMPT.md', 'HANDOFF.md', 'FINDINGS.md', 'lean/README.md',
             'lean/SYSTEM.md', 'lean/COVERAGE.md', 'lean/API-COVERAGE.md',
             'lean/notes-current-system-claim.md', 'lean/notes-proof-status-20261017.md']
for relative in documents:
    path = root / relative
    text = path.read_text()
    marker = '## Concrete fragment callbacks now have finite completion proofs'
    assert marker in text and block.splitlines()[0] not in text
    path.write_text(text.replace(marker, block + marker, 1))
path = root / 'FINDINGS.md'
text = path.read_text()
marker = '### Concrete callback completion and allocated parked IDs'
addition = '''### Returned callback pending IDs stay allocated

The modeled concrete Left callback now preserves the allocation bound for
all pending IDs in its returned metadata. Rendering, new matches, resumed
representatives and filtering retain this bound at the actual final cache.
The theorem covers either rejection flag. The producer retains its original
completion witness. All previous runtime expressions and interfaces stay.
The previous output-pending-ID proof gap is closed. Native fragment levels,
heap classification, callback interleaving and scheduler semantics stay open.
This establishes a model invariant. It identifies no Haskell runtime defect.
External action: no new patch is proposed. Keep the external Haskell repair
table and the pending Sized documentation repair above.
Details: lean/notes-current-pruning-enumeration-callback-bounds.md.

'''
assert addition.splitlines()[0] not in text
path.write_text(text.replace(marker, addition + marker, 1))
assert path.read_text().index('## Haskell fix handoff') < path.read_text().index(block.splitlines()[0])

note = f'''# Allocated pending IDs from concrete callbacks

## Current result

Rendering and match bounds: `3c1d159ff`.
Concrete callback output: `f6f7985dc`.
Main remains `153e1a211b56dd78bd22f6b427fb78e673041d55`.
The whole formalization goal stays ACTIVE.

The concrete Left callback now returns only allocated pending IDs in its
actual metadata result. The stronger finite producer uses the same fuel,
result and final cache as the earlier completion theorem. It does not rerun
the callback or require a desired final state. The earlier callback producer
types stay exact. The output-bound gap from the preceding checkpoint is closed.

## Preservation chain

EnumerationPartialBounds.TermBound checks every hole label in a partial term.
TermsBound applies that requirement to its finite ordered child list.
expandPartial_bounded proves both RenderStable and the bound at the actual
returned allocation counter. It uses actual bounded getValue reads and
storage bounds for expanded fragments. Pending holes retain their raw IDs.
The recursive empty-bucket case retains the existing truncation behavior.
This successful-execution theorem does not require Stratified or a completed
graph. The separate finite producer still requires dependency levels.

SourcePruningPartialMatch.PendingBound checks each parked entry's raw ID.
matchPartial_bounded proves that successful matching can only park holes
already present in the bounded partial term. It covers all pattern forms,
both wildcards, exact and prefix child matching, holes and truncation.
The private child matcher concatenates the bounded results in order.

programs_bounded retains bounds for the exact app and filter program views.
startMatches_bounded applies matching at those selected programs.
finishChecks_bounded retains bounds through optional-result filtering and
the final nonempty-group filter. No group order or duplicate is changed.

resume_bounded uses the actual representative-read path for each parked ID.
An allocated input has an allocated representative. If that root is current,
matching uses the bounded rendered term. Otherwise the exact representative
is parked again. The proof sequences all optional results and concatenates
their pieces. It retains the actual final allocation counter through every
compression step. Safety follows from bounded reads, never Frame alone.

oracle_inl_bounded covers early rejection, idle and full observation.
The observation reads every pending group before combining results.
Its output groups come from bounded resumption or bounded startMatches.
The bound holds for either rejection flag. No acceptance premise is used.

recordTypes_inl_bounded handles the empty-catalog branch and actual oracle
branch. recordTypes_inl_complete_bounded applies this result to the exact
earlier completion witness. It returns safe storage, full Frame, unchanged
dependency levels, the exact type-position update, unchanged openHoles and
typing, and allocated IDs for all returned metadata.pending groups.

## Verification and evidence

All six changed modules pass Lean 4.34.1 with all linters and warnings as
errors. Twelve strict attempts contain six retained failures. Renderer
substitution accounts for one. Matcher recursor binders and singleton
substitution account for two; unused simplifier arguments account for one.
Resume state substitutions and an unused section instance account for one;
the strict linter rejects the first omit-based repair in another. The final
proof puts the pure helper outside that instance section. All six final
strict checks pass. Template, oracle and callback checks pass first time.

Four installed helper builds pass. Aggregate Audit passes with 3761 jobs
and 76809 checked dependencies. Audit source stays byte-identical.
Installed public readback checks ten new preservation theorems, both older
callback producers and H6. Its full output has {len(public.splitlines())} lines
and {len(public_bytes)} bytes. Its SHA-256 is
`{sha(public_bytes)}`.
All axiom sets are subsets of propext, Classical.choice and Quot.sound.
The old unused inputs warning remains unchanged. All eighteen checks run
serially under 4 GiB heavy-management caps with no swap.

Source review confirms actual endpoint bounds, both rejection outcomes,
all new and resumed groups, and reuse of the same completion witness.
Preservation checks retain all previous runtime expressions and theorem
text. New predicates and appended proofs account for the changes.
H6, native workers and every Haskell source stay unchanged. No Haskell
suite is repeated. No new Haskell defect or repair is identified.
Root FINDINGS keeps the external Haskell handoff first.
Full attempted sources, logs, reports, final snapshots, proof patch,
cap records and preservation checks remain in
restart-evidence/20261025-callback-bounds.

## Remaining work and strongest claim

Initial metadata still needs genuine allocated pending IDs. The theorem
now preserves that property at its output. Other native operations must
transport it to later caches when the allocation counter grows.
The new theorem does not bound every metadata field or establish native
Int, IntSet or physical container correspondence.

Establish and preserve Stratified through native traversal, pending-class
merges and final fragment writes. Reuse the existing graph worker's
traversal_stratified and write_stratified design. Derive that each returned
fragment hole resolves to a pending slot at the actual traversal endpoint.
PendingReferences alone does not prove fragment acyclicity.

Connect the supplied Graph.node classification to the actual native heap
and handle decoding. Compose each Left callback at its own successful
branch receipt's Caller, memos, queries, cache and metadata. Retain source
callback/recursive-loop timing and rejection. Arbitrary Haskell forcing,
scheduler restart, initial-only capacity forecasts, extraction and whole-driver
language semantics remain open. No whole-loop termination is proved.

H6 remains the strongest end-to-end language theorem. Covered closed
construction, a valid initial cache, original allocation history and any
prescribed finite budget and modeled node-call rounds derive sufficient
finite bounds and one mathematical width chosen after construction. With
empty inherited payload, the final available value has exactly the original
finite-tree language under the formal formula and entailment interfaces.
Concrete solver and physical runtime correspondence remain outside that claim.
'''
(root / 'lean/notes-current-pruning-enumeration-callback-bounds.md').write_text(note)

evidence.mkdir()
for name in checks:
    shutil.copytree(area / name, evidence / name)
for name in ['check.py', 'prepare-handoff.py', 'stage.py', 'heavy-peaks']:
    shutil.copyfile(area / name, evidence / name)
for name, report in checks.items():
    raw = (evidence / name / 'raw.log').read_bytes()
    assert len(raw) == report['bytes'] and sha(raw) == report['sha256']
    if name in strict:
        source = next((evidence / name / 'MicroCFTA').glob('*.lean'))
        assert sha(source.read_bytes()) == report['source_sha256']
        if name in final_strict:
            assert source.read_bytes() == (root / 'lean/MicroCFTA' / source.name).read_bytes()
            assert not raw
assert sha((evidence / 'public-final/public.lean').read_bytes()) == checks['public-final']['source_sha256']
snapshots = sources + unchanged
for relative in snapshots:
    target = evidence / 'sources' / relative
    target.parent.mkdir(parents=True, exist_ok=True)
    shutil.copyfile(root / relative, target)
(evidence / 'proof-change.patch').write_bytes(subprocess.check_output(
    ['git', 'diff', base, 'HEAD', '--', 'lean/MicroCFTA'], cwd=root))
summary = dict(base=base, proof_head=subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=root, text=True).strip(),
               checks=18, strict_attempts=12, rejected_strict_attempts=6, final_strict_modules=6,
               public_declarations=13, audit_dependencies=76809, public_lines=len(public.splitlines()),
               public_bytes=len(public_bytes), public_sha256=sha(public_bytes), unchanged_paths=unchanged,
               old_runtime_and_declarations='byte-identical after removing new predicates, import and proof blocks',
               new_runtime_workers=0, audit_changes='none',
               admission_scope='same initial Safe, Stratified, allocated fragment holes and incoming parked IDs',
               output_pending_id_bounds=True, native_stratified_preservation=False,
               source_sha256={p: sha((root / p).read_bytes()) for p in snapshots})
(evidence / 'verification.json').write_text(json.dumps(summary, indent=2) + '\n')
manifest = {str(p.relative_to(evidence)): dict(bytes=p.stat().st_size, sha256=sha(p.read_bytes()))
            for p in sorted(evidence.rglob('*')) if p.is_file()}
(evidence / 'manifest.json').write_text(json.dumps(manifest, indent=2) + '\n')
print(json.dumps(dict(payloads=len(manifest), total_bytes=sum(v['bytes'] for v in manifest.values()),
                     manifest_sha256=sha((evidence / 'manifest.json').read_bytes()))))
