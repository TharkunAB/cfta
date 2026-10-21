import datetime
import hashlib
import json
import subprocess
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
start = (HERE / 'starting-head.txt').read_text().strip()
proof = (HERE / 'proof-commit-progress.txt').read_text().strip()
now = datetime.datetime.now().astimezone().strftime('%Y-%m-%d %H:%M %Z')
source = ROOT / 'lean/MicroCFTA/SourceCurrentResourceOwnerProgress.lean'
assert hashlib.sha256(source.read_bytes()).hexdigest() == '05b2dd2001743235a81a5190060e28bd61fdd1a044ecb2476096de85e2c11a0e'
assert not (HERE / 'progress-strict-1.log').read_bytes()
audit = (HERE / 'audit-1.log').read_text()
assert 'Build completed successfully (3600 jobs)' in audit and '74974 MicroCFTA theorems' in audit
assert {item['path'] for item in json.loads((HERE / 'components.json').read_text())} == {'progress','independent-review','dispatch-plan'}
full = (HERE / 'progress/resource-owner-progress-public-1.log').read_bytes()
assert len(full) == 10187067 and hashlib.sha256(full).hexdigest() == '024db855722d5722e41d31828886790f03b71336e39d3bf15e93a2b6630f827c'
update = f'''## Current delayed Top owner key separation from one saved writer

Updated: {now}. Proof checkpoint: `{proof[:10]}`.
Start: `{start[:10]}`. Imported main remains `794903b3f`.
Read `lean/notes-current-resource-owner-progress.md`.

ResourceOwnerProgress.key_ne_top now consumes ONE joint historical Written
and derives actual delayed-child payload nonemptiness and Top owner key
separation. It also derives returned-row guard equality and original-row
nonplainness. Original row membership in the ordinary owner and exact full
owner lookup in returned.children remain inputs. No desired path pair,
ancestry relation or independent historical resource witness is supplied.

The same saved Parent execution supplies OwnerSelection and the existing
SelectedCertificates producer. Its numeric construction and same loaded
field derive returned.guard = original.guard, including warm constructors.
The same selected Scan/Required/pass bundles and original false gates feed
ActualOwnerPair. Its actual combined-component pair feeds DelayedCombined
at the SAME index. No resident replay wrapper or historical heap interval
is introduced. Current prefix validity/readiness/field, live combined branch,
later Valid/Grows and initially ready Top remain genuine premises.

The stronger writer ledger already propagates through actual recursive
workers and unfinished prefixes. The next frozen dispatch plan derives the
consumer's current facts and full-owner lookup at one real row child walk.
That integration is not a selected theorem here. This result excludes only
an immediate ready Top ordinary owner key. Non-Top exclusion, renewal,
fresh-call bounds, final retention, general outer completion, convergence,
broader initial resources and Haskell refinement remain open.

Root strict, complete FULL and independent review pass. Audit passes 3600
jobs /74974 dependencies. Six actual Lean/Lake commands retain two failed
stricts. Repairs qualify a notation, apply existing native invariant
conversions and order the guard rewrite. Original unelaborated proposal,
corrected exact qualified proposal and all failures remain. Selected/root
strict logs are empty. One public head has complete identical checked/
printed types, all eight settings and standard axioms. A readback delimiter
correction is metadata only; it adds no failed Lean job. No canonical,
infrastructure, constructed or reviewer proof job ran. Only the old Audit
warning remains. Counts do not measure completion.

All old sources/evidence/version exceptions remain. Haskell/packages/main,
stashes and other worktrees stay unchanged. No new Haskell defect or repair.
FINDINGS keeps the external repair index FIRST. The full goal stays active.
'''
findings = f'''Current proof update: {now}. Proof checkpoint: `{proof[:10]}`.
One joint saved Parent writer now supplies delayed Top owner key separation.
The proof derives returned guard equality, original nonplainness and a pair
in the actual combined component from the same selected execution. It
requires genuine current prefix/live/later-operation facts and the exact
returned full-owner lookup. No caller ancestry or pair witness is supplied.

Strict/FULL/independent review pass; Audit 3600 jobs /74974 dependencies.
Six actual commands retain two failed stricts, no warning there. Original
invalid/unelaborated notation proposal and exact qualified correction stay.
Selected checks are clean; the old Audit warning remains. A parser delimiter
repair is metadata only. One public key_ne_top head; no canonical,
infrastructure, constructed or reviewer proof job. Actual dispatch
integration, non-Top owner exclusion, renewal, final retention, completion,
convergence, broader initial resources and Haskell refinement remain open.
No Haskell source, runtime result, imported main or external repair changes.
Read `lean/notes-current-resource-owner-progress.md`. Goal active.
The external Haskell repair index stays FIRST. Counts are not completion.
'''
note = f'''# Delayed Top owner key separation from the original Parent writer

Updated: {now}. Proof: `{proof}`.
SourceCurrentResourceOwnerProgress has 117 lines and one public theorem,
key_ne_top. Selected SHA256:
05b2dd2001743235a81a5190060e28bd61fdd1a044ecb2476096de85e2c11a0e.

''' + update + f'''
Written is unpacked ONCE. All worker fuels, budget, complete historical
caller, globals, inventory/profile, literal Parent.done, returned checked/
fourth/Merge, Context/Frame/Fits/reservation and native/Merge/history laws
stay together. OwnerSelection uses that exact execution and exact owner
copy. SelectedCertificates already aligns the numeric receipt and every
selected stage. No second writer or new resident-completion/replay producer
is constructed. Scanned readiness supplies semantic/cost facts; the same
Scan effects transport physical Merge storage. Both additional Merge laws
refer to the same unchanged original writer Merge table.

The complete owner lookup excludes reject/sentinel construction branches.
The actual constructor receipt gives returned guard = readback loaded.
The SAME historical loadedAt and cached-field proof give readback loaded =
original guard. Current field, prefix and later growth are rewritten only
by that derived equality. The live combined value exposes its actual record
list. ActualOwnerPair derives a same-child distinct-suffix pair in ONE
combined component, using original false primary gates and exact full
retained records. DelayedCombined uses that pair at the SAME index and
actual later operations. It yields payload not some [] and the key unequal
to the initially ready Top owner's key. No deeper dispatch is claimed.

Root and independent review read the complete original113 source and each
exact delta. Strict1 found the original unelaborated proposal's duplicate
implicit bits argument through local Written notation. The exact one-name
qualified proposal correction preserves all mathematical premises and the
result. The original proposal and failed input stay unchanged. Strict2
found the physical/native Good interface and guard-rewrite order. Existing
public conversions derive native Good from SAME checked Good, semantics
and costs. The guard is fixed under accepted before readback transitivity.
No new premise is added. Strict3/root strict are literal empty.

ONE complete FULL has 10187067 bytes, SHA256
024db855722d5722e41d31828886790f03b71336e39d3bf15e93a2b6630f827c.
The sole public type contains internal := text. A naive first-delimiter
parser was wrong. The retained metadata correction locates the unique
actual theorem proof boundary. Complete checked and printed types match,
all eight settings are present, and the printed proof has no omissions or
private public-type predicate. Axioms are propext, Classical.choice and
Quot.sound. The compiler FULL command passed; its parser correction adds
zero compiler attempts. There are four actual component Lean commands:
two failed stricts by the original author, then passed strict3/FULL by the
takeover author. Root strict and Audit make six actual Lean/Lake jobs with
two failures. Source authorship and takeover command ownership are explicit.
Every actual launch keeps fresh usage, effective max/high 4 GiB, zero swap
and a five-minute cap. No reviewer proof command ran.

The next actual-dispatch plan starts from a literal reached row stage and
genuine initial resources/Origins. It recovers SAME Written through the
actual row head, derives current coherent full-owner readback under a
hypothetical key collision, and follows the actual prefix and completed
earlier take(slot) walk. No future enclosing return, per-sibling Ready,
current-to-past writer inference or changed slot may be assumed. That
planned integration is outside this selected proof checkpoint.

The broad semantic guarantee remains conditional: supported successful
model traversal with empty inherited constraints preserves exactly the
accepted finite terms. Whole-library correctness additionally requires
termination and each public Haskell specification from valid supported
INITIAL inputs. This local Top ordinary-owner result proves no general
active-owner exclusion, renewal rank, bound on fresh requests, all-call
termination, final retention, convergence or Haskell correspondence.
All old proofs/counterexamples and version exceptions stay. FINDINGS keeps
the external Haskell repair index first. Goal active.
'''
documents = ['NEXT-PROMPT.md', 'HANDOFF.md', 'FINDINGS.md', 'lean/README.md',
             'lean/SYSTEM.md', 'lean/API-COVERAGE.md', 'lean/COVERAGE.md',
             'lean/notes-proof-status-20261017.md', 'lean/notes-current-system-claim.md']
for name in documents:
    original = subprocess.check_output(['git', 'show', start + ':' + name], cwd=ROOT, text=True)
    assert (ROOT / name).read_text() == original, name
    if name == 'FINDINGS.md':
        prefix = '# Current formalization findings\n\n## Haskell fix handoff for external work\n'
        marker = prefix + '\n' + (HERE / 'haskell-repair-index.md').read_text().rstrip() + '\n'
        assert original.startswith(marker)
        rest = original[len(marker):]
        assert rest.startswith('\n')
        changed = marker + '\n' + findings + '\n' + rest[1:]
        assert changed.replace(findings + '\n', '', 1) == original
    else:
        first, rest = original.split('\n', 1)
        changed = first + '\n\n' + update + rest
        assert changed.replace(update + '\n', '', 1) == original
    (ROOT / name).write_text(changed)
(HERE / 'current-update.md').write_text(update)
(HERE / 'findings-update.md').write_text(findings)
(ROOT / 'lean/notes-current-resource-owner-progress.md').write_text(note)
print('Updated nine documents and focused note. All prior text remains.')
