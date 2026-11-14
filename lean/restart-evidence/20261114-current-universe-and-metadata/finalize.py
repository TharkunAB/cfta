from pathlib import Path
import datetime
import gzip
import hashlib
import json
import subprocess

ROOT = Path('/home/tritlo/Code/mcfta')
PACKET = ROOT / 'lean/restart-evidence/20261114-current-universe-and-metadata'
CODE = 'f3d264a3350ef0545bbc90aacb5b4c430cd6a0ba'
BASE = 'beacf58b0faa51a64acbfa72e01fad731f3a85c8'
assert subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip() == CODE
now = datetime.datetime.now().astimezone().strftime('%Y-%m-%d %H:%M %Z')
report = json.loads(Path('/tmp/mcfta-current-universe-ownership-publication-20261114-0840/checked.json').read_text())
assert report['audited_theorems'] == 95458 and report['individual_reports'] == 50
assert all(item['exit'] == 0 and not item['nonstandard_axioms'] for item in report['checks'])
assert subprocess.run(['git', 'diff', '--quiet', BASE, CODE, '--', '*.hs', '*.cabal'], cwd=ROOT).returncode == 0

sources = sorted((ROOT / 'lean/MicroCFTA').glob('*.lean'))
pins = {str(path.relative_to(ROOT)): hashlib.sha256(path.read_bytes()).hexdigest() for path in sources}
tree = b''.join(path.encode() + b'\0' + digest.encode() + b'\n' for path, digest in sorted(pins.items()))
tree_hash = hashlib.sha256(tree).hexdigest()
(PACKET / 'source-pins.json.gz').write_bytes(gzip.compress((json.dumps(pins, indent=2) + '\n').encode(), mtime=0))
patch = subprocess.check_output(['git', 'diff', '--binary', BASE, CODE, '--', 'lean/MicroCFTA'], cwd=ROOT)
(PACKET / 'code.patch.gz').write_bytes(gzip.compress(patch, mtime=0))

common = f'''# Current source ownership and identity worker erasure checked ({now})

GOAL ACTIVE. Continue the complete optimized interned shared eager objective.
For each actual emitted partial root, prove ONE finite accepted term of the SAME
original root with ONE consistent assignment for supported domains, paths,
aliases, residuals and partial readback, including parked backward recompletion.
Original typing, depth adequacy/completeness, default LPO/reduction/refolding,
both language directions, stream order/multiplicity/lazy demand, exact accepted
terms per node-count size, counts/weights/training, BOTH rank/unrank inverses,
host bounds and compiled Haskell correspondence remain in scope.

Checked code: {CODE}. It is pushed and independently verified
at refs/heads/formalize. Main remains e53852064d3ef5a2eafec47d754c27504b11de5f
at the 08:43 CET remote check. Keep unrelated .hypha/ and all earlier proofs,
counterexamples, repairs and marked drafts. Standing push authorization remains.

CURRENT SOURCE RESULT: SourceSynthesisCurrentUniverseOwnership.
current_build_single_universe takes an accepted CURRENT raw expression and its
SAME actual labeled build from empty. The source heap either has no stored Mu,
or every stored Mu equals one resident closed computed type universe, including
its complete body, depth and ordinary fields. Rebuilding that universe in the
final heap or any heap that extends it returns the same value and unchanged heap.
It does not require a supplied universe, callback result or occurrence premise.
RootValue may be Empty even when the heap stores the universe.

The proof derives each stored value's actual writer and source path. It replays
those actual universe calls in ONE common final heap. Determinism there equates
the values. A chronological first-universe proof is unnecessary. Do not resume
the separate uncompiled first-publication draft as a prerequisite.

WORKER RESULT: SourcePruningEnumerationIdentityWorkerMetadataErasure provides
resume_identity_metadata_erasure and runEager_identity_metadata_erasure in the
SourcePruningEnumerationIdentityResultMetadataErasure namespace. They compare
arbitrary metadata with arbitrary Unit metadata after exact erasure. They use
the SAME actual worker, graph, caller, queries, cache and every fuel. The fixed
configuration is identity narrowing, empty templates, no stop callback and no
selection preference. Complete and stopped results retain output order,
duplicates, failure observations, receipts and native endpoints. The maps and
child-policy transport laws are now public dependencies, not pending drafts.
Broader callback and ordering configurations are outside this statement.

Earlier source laws derive OverUniverse from the actual current raw source and
prove its actual labeled universe callback and cleanup. These are in
SourceSynthesisCurrentUniverseOrigins and SourceSynthesisCurrentUniverseBody.
The previous six identity-prefix modules remain checked. Older source modules
retain their bytes except for the additive relevantRows_induction bridge in
SourceSynthesisUniverseOrigins and additive Audit imports/reports.

VALIDATION: Every new module builds, passes strict checking and passes an
independent import. Full Audit builds and strictly checks. Its aggregate checks
axiom dependencies for 95,458 imported project theorems. The 50 explicit reports
are separate: 48 standard-axiom reports and two axiom-free reports. Only propext,
Classical.choice and Quot.sound occur. There are 5,927 project source files and
4,925 direct Audit imports: 4,924 project imports plus Lean. These counts do not
assert a separate strict check of every source file. Checks run serially in Nix
with one Lean thread, memory.max/high 4 GiB and swap0.

BIGGEST GAP: ONE jointly consistent finite completion of each actual emitted
partial root. The source ownership law does not cover paired Mu owners created
by intersection or preprocessing. Derive the actual generated type-cone facts
and connect them to the existing state/assignment meaning. At the clear step,
SourcePruningEnumerationParkedLanguage.checkRepeated_true_satisfies retains
the removed bucket's Suspended.Holds facts as a separate conjunction. Post-clear
satisfaction alone does not derive them. Derive the needed facts or a common
finite witness from the actual reachable source history. Do not replace this
with independent node nonemptiness, marker emission, provenance or a new input
provider. Default preprocessing/refolding and compiled Haskell correspondence
remain separate open obligations.

HASKELL STATUS: No Haskell implementation/Cabal/test-suite source changed and no new defect or fix was
established. The supported proper-type-cycle probe uses need, i and liftF at
source size2. Raw and default public calls and separate typed calls each finish
with one result: need i absent, need liftF present. The positive typed term and
its own empty residual list are retained together. This settles that case only.
The probe does not establish that repeated clearing was entered. The old raw SKI
fixture's 175 results also mean fully enumerated lists, not Lean fuel outcomes.

RESTART INPUTS: lean/restart-evidence/20261114-current-universe-and-metadata/.
The packet retains compact source, drivers, pins, failures and repairs. It has
no compiled archive. Git and proof source reproduce the checked claims. Keep
the previous 20261114-identity-prefixes-checked packet unchanged. Private worker
check8 passed; private ownership check3 passed; their public checks also passed.
Earlier failed checks get no credit. No compiler is active at this checkpoint.
Root remains the sole live writer, compiler and Git owner. Temporary import
overlays link existing objects and do not copy build archives.

Fresh primary usage is 4% at 08:42 CET. Pause and ping Matti only above 80% fresh
primary usage. Filesystem free space was 90.87 GiB at 08:43 CET. Keep watching
/tmp. Do not delete unrelated process data or model weights. Temporary probe
binaries and object files were removed. Record every future Haskell fix in
FINDINGS.md. Liquid Haskell implementation specifications remain planned.

'''

liquid = '''## Liquid Haskell specification targets for implementation work

Use refinements and checked lemmas that match the Lean definitions. Start with
valid handles, representative bounds, interning/cache consistency and alias
updates that retain the original constraints and required child paths. Then
specify how native operations preserve one joint finite completion.

The main semantic target concerns repeated recursive clearing. A postcondition
about the cleared state alone can omit the removed constraints. Relate the
result to the SAME original root and SAME emitted partial root. Retain enough
facts to construct ONE finite assignment that satisfies every supported domain,
path, alias and residual. Independent finite witnesses for individual nodes do
not establish that statement. A Mu marker is not the missing finite witness.

Useful existing references are EnumerationDriver.Ready, the actual caller/cache
invariants, Suspended.Holds, and the assignment Satisfies predicates. The exact
clear meaning law is in lean/MicroCFTA/SourcePruningEnumerationParkedLanguage.lean.
The implementation paths are cfta/src/Data/CFTA/Enumeration.hs, including
checkRepeated, alias updates, required-child propagation and final readback.

Check implementation bodies. Record any assumed library specification or
assume-reflect equality explicitly. Reflection and PLE support checked lemmas;
they do not prove an assumed correspondence. Preserve termination checks where
proofs use termination. No automatic Liquid-Haskell-to-Lean bridge was added.
Matching the predicates and establishing implementation correspondence remain
required before using these specifications for an end-to-end Lean claim.
Official reference: https://ucsd-progsys.github.io/liquidhaskell/specifications/.
No Liquid Haskell implementation specification was checked here. The existing
Liquid synthesis frontend and verification of the engine are separate work.

'''

documents = []
for name in ['NEXT-PROMPT.md', 'HANDOFF.md', 'FINDINGS.md']:
    path = ROOT / name
    previous = subprocess.check_output(['git', 'show', f'{CODE}:{name}'], cwd=ROOT)
    assert path.read_bytes() == previous, name
    prefix = (common + (liquid if name == 'FINDINGS.md' else '')).encode()
    updated = prefix + previous
    assert updated.endswith(previous)
    path.write_bytes(updated)
    target = PACKET / 'document-prefixes' / (name + '.gz')
    target.parent.mkdir(exist_ok=True)
    target.write_bytes(gzip.compress(prefix, mtime=0))
    documents.append({'path': name, 'prior_commit': CODE,
                      'prior_sha256': hashlib.sha256(previous).hexdigest(),
                      'prefix_sha256': hashlib.sha256(prefix).hexdigest(),
                      'updated_sha256': hashlib.sha256(updated).hexdigest(),
                      'prior_bytes_preserved_as_exact_suffix': True})

checkpoint = {'at': now, 'checked_code': CODE, 'prior_packet_code': BASE,
              'source_files': len(sources), 'direct_audit_imports': 4925,
              'audited_theorems': 95458, 'explicit_reports': 50,
              'source_tree_sha256': tree_hash,
              'source_tree_digest_method': 'sorted UTF-8 relative path + NUL + lowercase SHA256 + newline',
              'documents': documents, 'haskell_changed': False,
              'joint_finite_completion_proved': False,
              'compiled_haskell_correspondence_proved': False}
(PACKET / 'checkpoint.json').write_text(json.dumps(checkpoint, indent=2) + '\n')
(PACKET / 'README.md').write_text(f'''# Current universe ownership and identity worker metadata erasure

Checked source: {CODE}. Prior packet source: {BASE}.
The source commit is pushed and independently remote-verified on formalize.

The new source theorem proves no stored Mu or one resident closed computed
universe in the SAME current raw-source build. It also proves replay in the
final and every growing heap. The worker theorem proves exact metadata erasure
for the existing identity worker with empty templates, no stop callback and no
selection preference. It retains complete and stopped observations.

Both results pass public builds, strict checks, independent imports and full
Audit. The final aggregate checks axiom dependencies for 95,458 imported project
theorems. The 50 explicit reports are separate. All axioms are standard.
Joint finite completion, later intersection/preprocessing ownership and compiled
Haskell correspondence remain open. No Haskell source changed.

Git and the Lean source reproduce these claims. Rebuild the named modules and
MicroCFTA.Audit in the existing Nix shell under the serial heavy-management cap.
The archived drivers record the exact strict checks, independent imports and
resource limits. Their temporary absolute paths need adjustment on replay.
These logs record the checks; they are not extra proof assumptions.

The packet contains source, scripts, pins, failed checks, repairs and logs.
It excludes object overlays and compiled files. Large text and literal patches
use gzip. archived-inputs.json maps each original input to its exact archived
bytes and states whether it is compressed. code.patch.gz contains the code
increment from the prior packet. source-pins.json.gz pins every current project
Lean source. The tree digest in checkpoint.json states its exact method.

Private worker checks before check8 failed. check8 passed. Private ownership
checks before check3 failed. check3 passed. Both then passed their public checks.
The first-publication draft remains UNCOMPILED and is not a proof dependency.
The supported proper-type-cycle runtime probe passed on raw and default routes;
it establishes one case only. Earlier source-review text that calls that probe
unrun is preserved history and is superseded by its actual runtime report.

The previous 20261114-identity-prefixes-checked packet retains earlier maps/CPS
inputs. Keep it unchanged. The new document prefixes preserve all previous root
document bytes as exact suffixes. checkpoint.json records their hashes.
manifest.json covers every payload file, including nested manifest.json files;
it excludes only itself.
''')
print(json.dumps({'at': now, 'source_tree_sha256': tree_hash,
                  'source_files': len(sources), 'document_prefix_bytes': len(common.encode())}))
