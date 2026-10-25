import hashlib
import json
import re
import shutil
import subprocess
from pathlib import Path

root = Path('/home/tritlo/Code/mcfta')
area = Path('/tmp/mcfta-native-callback-cache-20261026')
evidence = root / 'lean/restart-evidence/20261026-native-callback-cache'
base = (area / 'base.txt').read_text().strip()
sha = lambda data: hashlib.sha256(data).hexdigest()
old = lambda rel: subprocess.check_output(['git', 'show', base + ':' + rel], cwd=root)
checks = {p.parent.name: json.loads(p.read_text()) for p in sorted(area.glob('*/report.json'))}
assert len(checks) == 6
assert {name for name, report in checks.items() if report['exit_code']} == {'strict-native-cache-frame-1'}
finals = {
    'SourcePruningEnumerationNativeCacheFrame': 'strict-native-cache-frame-2',
    'SourcePruningEnumerationReceiptCallback': 'strict-callback-cache-1',
}
sources = ['lean/MicroCFTA/' + module + '.lean' for module in finals]
for module, name in finals.items():
    source = root / 'lean/MicroCFTA' / (module + '.lean')
    assert source.read_bytes() == (area / name / 'MicroCFTA' / source.name).read_bytes()
    assert sha(source.read_bytes()) == checks[name]['source_sha256']
    assert not re.search(rb'\b(sorry|admit|axiom)\b', source.read_bytes())
for name, report in checks.items():
    raw = (area / name / 'raw.log').read_bytes()
    assert len(raw) == report['bytes'] and sha(raw) == report['sha256']
public_bytes = (area / 'public-final/raw.log').read_bytes()
public = public_bytes.decode()
assert public.count('depends on axioms:') == 10 and '⋯' not in public and '...' not in public
for axioms in re.findall(r'depends on axioms:\s*\[([^]]*)\]', public):
    assert set(re.findall(r'[A-Za-z_.]+', axioms)) <= {'propext', 'Classical.choice', 'Quot.sound'}
assert 'def MicroCFTA.SourcePruningEnumerationReceiptCallback.Completes' in public
assert 'Checked axiom dependencies of 76842 MicroCFTA theorems.' in (area / 'aggregate-audit/raw.log').read_text()
relative = sources[1]
previous, current = old(relative).decode(), (root / relative).read_text()
headers = {}
for marker, end in [('def Completes ', '\n  | .complete'), ('theorem completes ', ' := by')]:
    a, b = previous.index(marker), current.index(marker)
    header = current[b:current.index(end, b)]
    assert previous[a:previous.index(end, a)] == header
    headers[marker.strip()] = sha(header.encode())
assert previous.count('recordTypes_inl_complete_bounded graph') == current.count('recordTypes_inl_complete_bounded graph') == 1
marker = '      obtain ⟨fuel, result, final, success, stable, frame, finalOrder, types, holes, typing, finalBounded⟩ :='
a, b = previous.index(marker), current.index(marker)
assert previous[a:previous.index('      exact', a)] == current[b:current.index('      exact', b)]
unchanged = ['lean/MicroCFTA/' + module + '.lean' for module in [
    'Audit', 'SourcePruningEnumerationSelectedOrdinary', 'SourcePruningEnumerationSelectedNarrow',
    'SourcePruningEnumerationNativeBranches', 'SourcePruningEnumerationNativeBranchCompletion',
    'SourcePruningEnumerationNativeOrdinary', 'SourcePruningEnumerationCapturedEdge',
    'SourcePruningCallbackCompletion', 'SourcePruningRecordTypes', 'SourcePruningEnumerationNativeIndex',
    'EnumerationCompressionFrame', 'EnumerationPendingOrder', 'EnumerationPendingReplacement',
    'EnumerationFragmentHistory', 'EnumerationOrder', 'EnumerationPureSelection', 'EnumerationIndexSelection',
    'EnumerationDriver', 'SourceCurrentColdFiniteWarmCalls',
]]
unchanged += ['cfta/src/Data/CFTA/' + name for name in [
    'Enumeration.hs', 'Interned/Type.hs', 'Interned/Cache.hs', 'Interned/Memo.hs', 'Interned/Operations.hs',
]]
for rel in unchanged:
    assert old(rel) == (root / rel).read_bytes(), rel
subprocess.run(['git', 'diff', '--quiet', base, '--', '*.hs', '*.cabal'], cwd=root, check=True)
main = subprocess.check_output(['git', 'rev-parse', 'origin/main'], cwd=root).decode().strip()
assert main == '153e1a211b56dd78bd22f6b427fb78e673041d55'
block = '''## Concrete callbacks retain the native indexed cache

Proof: `faec19a56`. The goal stays ACTIVE.

The concrete callback result now retains Admitted and FragmentHistory at
its actual returned cache. Existing pending-reference history persists there.
This includes actual root paths, realized native handles, canonical waiting
counts, candidate flags, the captured fragment and dependency levels.
Safety comes from the actual callback result, separately from its frame.
No new input or callback execution is added. SelectedOrdinary stays exact
and inherits the stronger completion output.

For any fixed preference, pure next selection is unchanged by the callback's
compression. Use the updated metadata's preference on both sides. The result
does not equate scheduling preferences before and after metadata changes.
All strict checks, public readback and Audit pass. Audit checks 76842
dependencies. H6 remains the strongest end-to-end language theorem.
Next: compose the actual callback Boolean with reject or scheduler restart,
using its returned metadata and cache. Exact recursive-continuation/native
effect interleaving, initial-only capacity, native Graph correspondence,
extraction and whole-driver language semantics remain open.
Details: `lean/notes-current-pruning-enumeration-callback-cache.md`.

'''
documents = ['NEXT-PROMPT.md', 'HANDOFF.md', 'FINDINGS.md', 'lean/README.md',
             'lean/SYSTEM.md', 'lean/COVERAGE.md', 'lean/API-COVERAGE.md',
             'lean/notes-current-system-claim.md', 'lean/notes-proof-status-20261017.md']
for rel in documents:
    path = root / rel
    text = path.read_text()
    marker = '## Selected ordinary receipts derive concrete fragment callbacks'
    assert marker in text and block.splitlines()[0] not in text
    path.write_text(text.replace(marker, block + marker, 1))
path = root / 'FINDINGS.md'
text = path.read_text()
addition = '''### Concrete callbacks preserve native cache certificates

The modeled concrete Left callback now returns the full indexed-cache
certificate at its actual final cache. Safety comes from RenderStable.
A separate compression frame retains root paths, stored values, ancestry,
fragment targets and suspended-reference history. Frame alone is not used
to infer safe storage. A fixed selection preference gives the same next
selection after compression. Updated metadata can select another preference.
The reframed completed receipt is an invariant certificate. It is not a new
raw captured-edge execution receipt. Either callback Boolean is retained;
a true pruning result makes no claim that the driver continues.
No Haskell runtime defect or new repair is identified. External action:
no new patch is proposed. Keep the repair table and Sized repair above.
Details: lean/notes-current-pruning-enumeration-callback-cache.md.

'''
marker = '### Selected receipts and concrete callback availability'
assert marker in text and addition.splitlines()[0] not in text
path.write_text(text.replace(marker, addition + marker, 1))
assert path.read_text().index('## Haskell fix handoff') < path.read_text().index(block.splitlines()[0])
note = f'''# Native cache certificates after concrete fragment callbacks

## Current result

Proof commit: `faec19a56`.
Main remains `{main}` after fetch.
The whole formalization goal stays ACTIVE.

The actual concrete Left callback endpoint now retains the native indexed
cache, captured-fragment certificate and dependency history. It also retains
suspended-reference history when the original receipt supplies that history.
The existing selected-ordinary producer supplies the original history.
Its entire source remains unchanged and inherits the stronger completion
predicate through its existing proof call. No runtime worker changes.

## Cache transport uses actual safety and exact root paths

NativeCacheFrame.cacheValid_frame accepts the original CacheValid, an actual
compression Frame and separately Safe after. It retains the same root map:
each stored root path follows Frame.reaches. StorageValid comes from Safe.
PendingRealized follows exact slot equality at the same native Caller heap.
Canonical waiting counts and native candidate flags follow exact values.
EnumerationExpandableIndex.frame retains the original waiting map and flags.

Frame alone does not establish Safe. An explicit entry beyond the allocation
counter can preserve effective root paths and still violate the forest bound.
The concrete callback's actual RenderStable.safe supplies the needed safety.
No new Safe assumption is added to the callback producer.

admitted_complete_frame retains the full successful receipt certificate:
CacheValid, Safe, bounded fragment, the original captured-slot fragment,
empty expansion ancestry and the captured raw root. Counter, values and
ancestry follow the same frame. The actual self-root path retains its size.
fragmentHistory_complete_frame retains original-to-final allocation growth,
actual pending targets for all fragment holes and conditional frontier+1.
The same frame transports actual targets and the existing dependency levels.
pending_complete_frame retains suspended-reference history with the existing
frame_pending theorem. It does not require a new oracle property.

These outputs use a reframed complete constructor as a certificate. They
do not claim that CapturedEdge.run returned the cache after the later callback.
The original callback action and its actual endpoint remain explicit.
Caller and saved query fields stay those of the original branch receipt.

## Pure selection and updated metadata

selection_frame proves exact next selection for any fixed preference after
framing a new core with the original indexes and allocation counter.
The candidate list uses List.range counter. Unchanged indexes alone are
insufficient; actual counter equality is also used. The lemma needs no
Graph, Safe, values or representative-class premise.

Apply it with the preference built from the callback's returned metadata
on both sides. The callback updates type positions and pending matches,
so its metadata can change an expansion order. This theorem does not equate
preferences built from old and new metadata. A true callback pruning result
still terminates its branch in the source. Selection equality is a state
property, not a proof that a rejected branch performs another selection.

## Strengthened existing completion output

ReceiptCallback.Completes retains its exact declaration type and inputs.
Its output predicate is strengthened. At the same actual callback result it
now includes Admitted and FragmentHistory for the reframed cache, conditional
Pending transport and pure next-selection equality for every fixed preference.
The earlier Success, RenderStable, Frame, Stratified, exact metadata fields
and returned pending-ID bounds remain in the output.

The completes theorem retains its exact declaration type. It calls
recordTypes_inl_complete_bounded exactly once, with the same arguments and
same chosen fuel, metadata result and final cache. The new conclusions are
derived from that existing witness and its actual safety and frame.
There is no callback-success premise, new admission input or second execution.

SelectedOrdinary.complete_with_history already returns Completes for every
processed receipt. The stronger result therefore reaches original selection
without changing that producer, its wrapper, its original Pending history,
its ordinary node gate, its numeric Ranges or any reached Caller endpoint.
The independent per-receipt callbacks still use the supplied branch metadata.
Sibling metadata is not folded: each returned metadata value belongs to its
own recursive continuation. Exact native effect interleaving remains open.

## Verification and evidence

Lean 4.34.1 checks both changed modules with all linters and warnings as
errors. Three strict attempts retain one failed first helper check: unfolding
selection leaves a reflexive goal, which the final rfl closes. The final
helper and concrete callback checks pass. The installed helper build passes.
Aggregate Audit rebuilds the unchanged selected consumer and passes with
3767 jobs and 76842 theorem dependencies. Audit source remains exact.

Installed public readback checks ten declarations and their axiom sets.
It also prints the full installed Completes definition to expose its new
output clauses. The full output has {len(public.splitlines())} lines and
{len(public_bytes)} bytes. Its SHA-256 is `{sha(public_bytes)}`.
There is no output ellipsis. All axiom sets are subsets of propext,
Classical.choice and Quot.sound. The earlier unused inputs warning is
unchanged. All six checks run serially under heavy-management 4 GiB caps.
No Haskell source or package file changes, so its suites are not repeated.

A separate source review confirms the safety boundary, original Caller and
query fields, actual callback endpoint, fixed-preference quantification and
reframed-certificate meaning. It finds no new future-success premise or
claim that the driver continues after callback pruning.

Evidence: lean/restart-evidence/20261026-native-callback-cache.
The manifest records exact payload bytes and SHA-256, including raw logs,
strict source copies, failed attempt, public definition readback, final and
original source snapshots, proof diff, verification report and cap records.
Force-add exactly the manifest payload list and verify committed bytes.

## Next work and claim boundary

Compose the actual callback Boolean with the source branch decision. A true
result rejects. A false result restarts selection using returned metadata
and the actual framed native cache. Retain all native cache and history
certificates through that continuation. Do not assume the old metadata's
preference equals the updated metadata's preference.

The repeated-recursion path clears its bucket and restarts without narrowing
or an oracle call. Its actual indexed-cache receipt is already available;
connect it to the same scheduler step while preserving branch-local metadata.
Exact depth-first native effect and recursive-continuation interleaving,
initial-only native query capacity, native Graph/heap correspondence,
terminal/nonordinary outer fallback, pruning language laws, extraction and
complete finite-machine/Haskell correspondence remain open.

H6 constructed_node_calls is unchanged and remains the strongest end-to-end
language theorem. It covers closed construction, valid initial constraint
history, any prescribed finite budget/rounds, derived finite fuels and one
mathematical width chosen after construction. It preserves the original
finite-tree language under the formal formula/solver interfaces. It does
not prove the whole typing/pruning enumeration driver.
'''
(root / 'lean/notes-current-pruning-enumeration-callback-cache.md').write_text(note)
verification = dict(base=base, source_commit='faec19a56', main=main, checks=checks,
                    final_strict_modules=finals, preserved_header_sha256=headers,
                    public_declarations=10, public_definition_printed=True,
                    public_lines=len(public.splitlines()), public_bytes=len(public_bytes),
                    public_sha256=sha(public_bytes), audit_dependencies=76842,
                    final_source_sha256={rel: sha((root / rel).read_bytes()) for rel in sources},
                    unchanged_source_sha256={rel: sha((root / rel).read_bytes()) for rel in unchanged},
                    goal_status='active', runtime_workers_and_haskell_unchanged=True)
(area / 'verification.json').write_text(json.dumps(verification, indent=2) + '\n')
(area / 'proof-change.patch').write_bytes(subprocess.check_output(['git', 'diff', base, 'HEAD', '--', *sources], cwd=root))
for rel in sources + unchanged:
    destination = area / 'sources' / rel
    destination.parent.mkdir(parents=True, exist_ok=True)
    shutil.copyfile(root / rel, destination)
assert not evidence.exists()
shutil.copytree(area, evidence)
manifest = {str(p.relative_to(evidence)): dict(bytes=p.stat().st_size, sha256=sha(p.read_bytes()))
            for p in sorted(evidence.rglob('*')) if p.is_file()}
(evidence / 'manifest.json').write_text(json.dumps(manifest, indent=2) + '\n')
print(json.dumps(dict(payloads=len(manifest), bytes=sum(item['bytes'] for item in manifest.values()),
                      manifest_sha256=sha((evidence / 'manifest.json').read_bytes()))))
