import hashlib
import json
import re
import shutil
import subprocess
from pathlib import Path

root = Path('/home/tritlo/Code/mcfta')
area = Path('/tmp/mcfta-partial-completion-20261025')
evidence = root / 'lean/restart-evidence/20261025-partial-completion'
base = '32ecf9186a98b1c3c2814ec63eb021bfc2114da8'
sha = lambda data: hashlib.sha256(data).hexdigest()
old_source = lambda relative: subprocess.check_output(['git', 'show', base + ':' + relative], cwd=root).decode()
checks = {p.parent.name: json.loads(p.read_text()) for p in sorted(area.glob('*/report.json'))}
assert len(checks) == 12
strict = {name for name in checks if name.startswith('strict-')}
failed = {name for name, report in checks.items() if report['exit_code'] != 0}
assert len(strict) == 8 and failed == {'strict-partial-1', 'strict-partial-2', 'strict-callback-1'}
final_strict = {'strict-partial-3', 'strict-resume-1', 'strict-oracle-1', 'strict-callback-2', 'strict-audit-1'}
assert not failed.intersection(final_strict)
public_bytes = (area / 'public-final/raw.log').read_bytes()
public = public_bytes.decode()
assert public.count('depends on axioms:') == 7 and '⋯' not in public and '...' not in public
for axioms in re.findall(r'depends on axioms:\s*\[([^]]*)\]', public):
    assert set(re.findall(r'[A-Za-z_.]+', axioms)) <= {'propext', 'Classical.choice', 'Quot.sound'}
assert 'Checked axiom dependencies of 76754 MicroCFTA theorems.' in (area / 'aggregate-audit/raw.log').read_text()

sources = ['lean/MicroCFTA/' + name + '.lean' for name in [
    'EnumerationPartialCompletion', 'SourcePruningResume', 'SourcePruningOracle',
    'SourcePruningCallbackCompletion', 'Audit']]
for module, marker in [('SourcePruningResume', '/-- A total forest gives a finite resume'),
                       ('SourcePruningOracle', '/-- Bounded fragment history constructs')]:
    relative = 'lean/MicroCFTA/' + module + '.lean'
    old = old_source(relative)
    current = (root / relative).read_text()
    if module == 'SourcePruningOracle':
        assert current.count('import MicroCFTA.EnumerationPartialCompletion\n') == 1
        current = current.replace('import MicroCFTA.EnumerationPartialCompletion\n', '', 1)
    assert current[:current.index(marker)].rstrip() == old[:old.index('end MicroCFTA.' + module)].rstrip()
assert (root / sources[-1]).read_text() == 'import MicroCFTA.SourcePruningCallbackCompletion\n' + old_source(sources[-1])
unchanged = ['lean/MicroCFTA/' + name + '.lean' for name in [
    'EnumerationState', 'EnumerationCorrectness', 'EnumerationOrder', 'EnumerationReferences',
    'EnumerationDriver', 'EnumerationPartialObservation', 'SourcePruningRecordTypes',
    'SourcePruningEnumerationSelectedOrdinary', 'SourcePruningEnumerationNativeBranchCompletion',
    'SourcePruningEnumerationNativeOrdinary', 'SourceCurrentColdFiniteWarmCalls']]
unchanged += ['cfta/src/Data/CFTA/' + name for name in [
    'Enumeration.hs', 'Interned/Type.hs', 'Interned/Cache.hs', 'Interned/Memo.hs', 'Interned/Operations.hs']]
for relative in unchanged:
    assert old_source(relative) == (root / relative).read_text(), relative
subprocess.run(['git', 'diff', '--quiet', base, '--', '*.hs', '*.cabal'], cwd=root, check=True)
for relative in sources[:-1]:
    assert not re.search(r'\b(sorry|admit|axiom)\b', (root / relative).read_text()), relative
for relative in [sources[0], sources[3]]:
    assert not re.search(r'^(?:noncomputable )?def ', (root / relative).read_text(), re.M)

block = '''## Concrete fragment callbacks now have finite completion proofs

Partial rendering and resume: `4880eef42`. Concrete callback: `32ceddf6c`.
The goal stays ACTIVE.

A safe cache, bounded fragment holes, allocated parked IDs and the existing
Stratified dependency levels now derive an actual finite Left callback.
The proof constructs partial rendering and every pending-group read before
combining results. It retains rejection, idle and empty-catalog branches.
The returned cache is safe and framed. The actual type-position update and
unchanged open-hole and typing fields are derived at that same endpoint.
No successful rendering, resume or callback is an input premise.

All five changed modules pass strict checking. Installed public readback
and Audit pass. Audit checks 76754 dependencies. H6 remains the strongest
end-to-end language result. Runtime workers and Haskell stay unchanged.
Next: preserve bounds for newly returned pending matches, and establish
Stratified history through native traversal, merges and final writes.
These inputs are not derived from pending-reference history alone.
Branch-endpoint callback integration, initial-only capacity, scheduler
restart, extraction and whole-driver language semantics remain open.
Details: `lean/notes-current-pruning-enumeration-callback-completion.md`.

'''
documents = ['NEXT-PROMPT.md', 'HANDOFF.md', 'FINDINGS.md', 'lean/README.md',
             'lean/SYSTEM.md', 'lean/COVERAGE.md', 'lean/API-COVERAGE.md',
             'lean/notes-current-system-claim.md', 'lean/notes-proof-status-20261017.md']
for relative in documents:
    path = root / relative
    text = path.read_text()
    marker = '## Original selection reaches admitted ordinary expansion'
    assert marker in text and block.splitlines()[0] not in text
    path.write_text(text.replace(marker, block + marker, 1))
path = root / 'FINDINGS.md'
text = path.read_text()
marker = '### Native ordinary alternatives retain their own caller receipts'
addition = '''### Concrete callback completion and allocated parked IDs

The modeled fragment callback now has a finite completion proof from actual
cache safety, allocated holes and parked IDs, and fragment dependency levels.
It reads every pending group before combining match results. Rejection is
a completed result. Runtime definitions and older declarations stay exact.
Total representative lookup alone does not establish safe storage. A read
of an unallocated raw ID can add a forest entry beyond the allocation limit.
The new safety theorem therefore requires allocated incoming parked IDs.
This proof boundary is not a reachable Haskell counterexample.
Native fragment-history preservation and bounds for newly returned pending
matches remain open. No Haskell runtime defect or repair is identified.
External action: no patch is proposed for this source observation.
The external Haskell repair table and pending Sized documentation repair stay.
Details: lean/notes-current-pruning-enumeration-callback-completion.md.

'''
assert addition.splitlines()[0] not in text
path.write_text(text.replace(marker, addition + marker, 1))
assert path.read_text().index('## Haskell fix handoff') < path.read_text().index(block.splitlines()[0])

note = f'''# Finite completion of the concrete fragment callback

## Current result

Partial rendering and parked matches: `4880eef42`.
Concrete callback and Audit import: `32ceddf6c`.
Main remains `153e1a211b56dd78bd22f6b427fb78e673041d55`.
The whole formalization goal stays ACTIVE.

The concrete modeled Left callback now derives an actual finite execution
from Safe storage, allocated fragment holes, allocated parked IDs and the
existing Stratified dependency levels. The proof supplies rendering and
every pending-group read. It assumes no successful render, resume or callback.
The result retains the actual cache endpoint, its full compression frame,
safe storage and the same dependency levels. Callback rejection remains
a completed result. No acceptance or pruning-language theorem is added.

## Partial rendering

EnumerationPartialCompletion.getValue_complete constructs an actual bounded
slot read. Totality supplies a root path. Forest bounds keep the root allocated.
Supply alignment supplies its stored slot. The actual findRoot execution
then produces getValue and its RenderStable receipt.

expandPartial_complete uses EnumerationOrder.Stratified. Equivalent variables
have the same level. Every stored enumerated fragment refers only to holes
at strictly higher levels. Each expanded root has a level below the frontier.
Following an enumerated fragment therefore decreases frontier minus level.
Structural recursion handles concrete fragment children. All finite child
traversals share a derived sufficient fuel bound.

Pending slots stop as holes. An unconstrained recursive boundary produces
the existing truncation marker. Other pending slots retain the original raw
hole ID. No Finished, CompleteGraph, graph-bearing value, empty template
catalog or hole-free fragment premise is needed.

The full Frame comes from the actual rendering execution. RenderStable comes
from bounded compression reads. stratified_read retains the same levels.
The input Stratified invariant is genuine. Safe storage and bounded holes
alone do not exclude a stored fragment that refers to its own class.

## Parked matches and the concrete oracle

SourcePruningResume.resume_complete constructs finite representative reads
for each parked entry from UnionFind.Total. Pure matching produces either
a pending result or none. A none result does not omit later state reads.
mapM_terminates and existing moreFuel theorems supply a common bound.
The successful resume retains the complete compression Frame.

resume_read separately proves RenderStable from Safe and allocated parked
IDs. The actual representative_read receipt preserves the allocation counter,
so each later parked reference keeps its bound. Frame alone never supplies
Safe. A missing raw ID outside the allocation domain can have a finite
representative lookup that inserts an out-of-range forest root. This is
a proof admission boundary, not an established reachable Haskell defect.

oracle_inl_complete preserves early rejection and the idle fast path. The
observe branch renders once, then resumes every pending group in source order.
It combines pure results only after all those reads. The proof raises render
and group fuels to one common bound without changing terms, results or the
actual final state. A rejected match remains a completed callback result.

recordTypes_inl_complete retains the empty-catalog pure branch. Other calls
use that same concrete oracle witness and endpoint. The final metadata has
the exact updatedTypes result. openHoles and typing stay unchanged.
The older inr theorem still supplies the pure pre-expansion event.

## Verification and evidence

All five changed modules pass Lean 4.34.1 with all linters and warnings as
errors. Eight strict attempts contain three retained failures: the first
partial proof refers to a helper outside its imports; the second leaves
a term witness unresolved; the first callback proof has a record-layout
parse error. The corrected final five module checks pass. No runtime worker
or older theorem declaration changes.

Two installed helper builds pass. The aggregate Audit passes with 3760 jobs
and 76754 checked dependencies. Installed public readback checks six new
declarations and the unchanged H6 declaration. Its full output has
{len(public.splitlines())} lines and {len(public_bytes)} bytes. Its SHA-256 is
`{sha(public_bytes)}`.
All axiom sets are subsets of propext, Classical.choice and Quot.sound.
The old unused inputs warning remains unchanged. All twelve checks run
serially under 4 GiB heavy-management caps with no swap.

Source review confirms the strict rank decrease, bounded-read safety, all
pending groups and actual callback endpoint. Existing runtime and theorem
text in Resume and Oracle remains byte-identical apart from the one new
import and appended proofs. Audit adds one import. H6, native workers and
all Haskell sources stay unchanged. No Haskell suite is repeated.
Full attempted inputs, logs, reports, final source snapshots, proof patch,
cap records and preservation checks are in
restart-evidence/20261025-partial-completion.
Root FINDINGS keeps the external Haskell handoff first. No new Haskell
runtime defect or repair is identified.

## Remaining work and strongest claim

The theorem does not export allocated IDs for returned metadata.pending.
Prove bounds for resumed representatives and newly parked holes in the
actual partial term. Then preserve those bounds through repeated callbacks.

Native traversal, merges and final fragment writes still need to establish
and preserve Stratified. Reuse the existing traversal_stratified and
write_stratified design. PendingReferences tracks suspended equality
references. It does not establish acyclic stored-fragment dependencies.
Derive pending targets for returned fragment holes at each actual endpoint.

Callback integration must use each successful branch receipt's own Caller,
memos, queries and cache. The serial scan's final Caller cannot replace that
endpoint. Native-heap/Graph correspondence, callback and recursive-loop
interleaving, arbitrary Haskell forcing, scheduler restart and whole-driver
language semantics remain open. Initial-only numeric admission still needs
the quantitative scheduler forecast described in the selected-ordinary note.
This checkpoint proves no whole-loop progress, termination or convergence.

H6 remains the strongest end-to-end language theorem. Covered closed
construction, a valid initial cache, original allocation history and any
prescribed finite budget and modeled node-call rounds derive sufficient
finite bounds and one mathematical width chosen after construction. With
empty inherited payload, the final available value has exactly the original
finite-tree language under the formal formula and entailment interfaces.
Concrete solver and physical runtime correspondence remain outside that claim.
'''
(root / 'lean/notes-current-pruning-enumeration-callback-completion.md').write_text(note)

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
            assert raw.decode().strip() == ('Checked axiom dependencies of 76754 MicroCFTA theorems.' if source.name == 'Audit.lean' else '')
assert sha((evidence / 'public-final/public.lean').read_bytes()) == checks['public-final']['source_sha256']
snapshots = sources + unchanged
for relative in snapshots:
    target = evidence / 'sources' / relative
    target.parent.mkdir(parents=True, exist_ok=True)
    shutil.copyfile(root / relative, target)
(evidence / 'proof-change.patch').write_bytes(subprocess.check_output(
    ['git', 'diff', base, 'HEAD', '--', 'lean/MicroCFTA'], cwd=root))
summary = dict(base=base, proof_head=subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=root, text=True).strip(),
               checks=12, strict_attempts=8, rejected_strict_attempts=3, final_strict_modules=5,
               public_declarations=7, audit_dependencies=76754, public_lines=len(public.splitlines()),
               public_bytes=len(public_bytes), public_sha256=sha(public_bytes), unchanged_paths=unchanged,
               old_runtime_and_declarations='byte-identical prefix; Oracle adds one import',
               new_runtime_workers=0, audit_changes='one import only',
               admission_scope='Safe, Stratified, allocated fragment holes and incoming parked IDs',
               output_pending_id_bounds=False, native_stratified_preservation=False,
               source_sha256={p: sha((root / p).read_bytes()) for p in snapshots})
(evidence / 'verification.json').write_text(json.dumps(summary, indent=2) + '\n')
manifest = {str(p.relative_to(evidence)): dict(bytes=p.stat().st_size, sha256=sha(p.read_bytes()))
            for p in sorted(evidence.rglob('*')) if p.is_file()}
(evidence / 'manifest.json').write_text(json.dumps(manifest, indent=2) + '\n')
print(json.dumps(dict(payloads=len(manifest), total_bytes=sum(v['bytes'] for v in manifest.values()),
                     manifest_sha256=sha((evidence / 'manifest.json').read_bytes()))))
