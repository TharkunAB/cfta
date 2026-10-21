import datetime
import hashlib
import json
import subprocess
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
SOURCE_SHA = '__H8_SOURCE_SHA256__'
SOURCE_LINES = int('__H8_SOURCE_LINES__')
strict, full, audit_stem = '__H8_SELECTED_STRICT_STEM__', '__H8_SELECTED_FULL_STEM__', '__H8_AUDIT_STEM__'
metrics = {
    'actual_jobs': int('__H8_ACTUAL_JOBS__'),
    'source_jobs': int('__H8_SOURCE_JOBS__'),
    'audit_jobs': int('__H8_AUDIT_JOB_COUNT__'),
    'failed_jobs': int('__H8_FAILED_JOBS__'),
    'warned_source_exit_zero_jobs': int('__H8_WARNED_SOURCE_EXIT_ZERO_JOBS__'),
    'rejected_public_type_jobs': int('__H8_REJECTED_PUBLIC_TYPE_JOBS__'),
    'audit_build_jobs': int('__H8_AUDIT_BUILD_JOBS__'),
    'audit_dependencies': int('__H8_AUDIT_DEPENDENCIES__'),
}
start = (HERE / 'starting-head.txt').read_text().strip()
assert start == '20f4181948591157e502391e20698138b04b2221'
proof = (HERE / 'proof-commit.txt').read_text().strip()
assert len(proof) == 40 and all(c in '0123456789abcdef' for c in proof)
assert subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip() == proof
assert subprocess.check_output(['git', 'branch', '--show-current'], cwd=ROOT, text=True).strip() == 'formalize'
now = datetime.datetime.now().astimezone().strftime('%Y-%m-%d %H:%M %Z')
gate = json.loads((HERE / 'selected-source-gate.json').read_text())
source_path = 'lean/MicroCFTA/SourceCurrentSameSymbolEdgeForwardCompletion.lean'
assert gate['status'] == 'ROOT_ACCEPTED' and gate['path'] == source_path
source = (ROOT / source_path).read_bytes()
assert hashlib.sha256(source).hexdigest() == gate['sha256'] == SOURCE_SHA
assert source == (HERE / gate['snapshot']).read_bytes() and len(source.splitlines()) == gate['lines'] == SOURCE_LINES
assert source == (HERE / (strict + '.source.lean')).read_bytes() and (HERE / (strict + '.log')).read_bytes() == b''
assert json.loads((HERE / (strict + '.json')).read_text())['exit_code'] == 0
raw = (HERE / (full + '.log')).read_bytes()
assert hashlib.sha256(raw).hexdigest() == '__H8_FULL_LOG_SHA256__'
assert json.loads((HERE / (full + '.json')).read_text())['exit_code'] == 0
readback = json.loads((HERE / '__H8_FULL_READBACK_PATH__').read_text())
assert readback['source_sha256'] == SOURCE_SHA and readback['source_lines'] == SOURCE_LINES
assert readback['log_sha256'] == hashlib.sha256(raw).hexdigest() and readback['log_bytes'] == len(raw)
assert readback['owned_public_job_exit'] == 0 and readback['no_omissions'] and len(readback['heads']) == 1
head = readback['heads'][0]
assert head['head'] == 'MicroCFTA.SourceCurrentSameSymbolEdgeForwardCompletion.both_miss_complete'
assert head['check_print_type_identity'] and head['check_print_type_byte_identity'] and head['unique_complete_type_body_delimiter']
checked = (HERE / '__H8_CHECKED_TYPE_PATH__').read_bytes()
assert checked == (HERE / '__H8_PRINTED_TYPE_PATH__').read_bytes()
assert hashlib.sha256(checked).hexdigest() == '__H8_TYPE_SHA256__'
assert not any(marker in checked.decode() for marker in ['_private', '✝', '†', '‡']) and head['private_public_type_names'] is False
assert head['actual_axioms_within_standard_allowed'] and set(head['actual_axioms']) <= {'Classical.choice', 'Quot.sound', 'propext'}
proof_report = json.loads((HERE / '__H8_PROOF_REPORT_PATH__').read_text())
assert proof_report['status'] == 'PASS' and all(proof_report[key] == value for key, value in metrics.items())
audit = (HERE / (audit_stem + '.log')).read_bytes()
assert hashlib.sha256(audit).hexdigest() == proof_report['audit_log_sha256'] == '__H8_AUDIT_LOG_SHA256__'
assert json.loads((HERE / (audit_stem + '.json')).read_text())['exit_code'] == 0
assert f"Build completed successfully ({metrics['audit_build_jobs']} jobs).".encode() in audit
assert f"{metrics['audit_dependencies']} MicroCFTA theorems".encode() in audit

update = f'''## Same-symbol edge forward completion

Updated: {now}. Proof checkpoint: `{proof[:10]}`.
Start: `{start[:10]}`. Imported main remains `794903b3f`.
Read `lean/notes-current-same-symbol-edge-forward-completion.md`.

SourceCurrentSameSymbolEdgeForwardCompletion.both_miss_complete derives
native and wrapper completion for two absent ordered pair keys.
It uses an explicit genuine current packet. This includes semantic-
interpreter Completes and WordRanges. It assumes neither native nor
wrapper success. The pair memo remains separate from native memo tables.
One Receipt retains the SAME result and full checked before/after state.
The original captured pair returns that result. A strict reversal also
returns it in a distinct reversed cell. Earlier returned cells remain.

The strongest combined semantic theorem remains constructed_node_calls.
This edge theorem does not add unconditional Scoped, Covered or Idle.
Warm hits, all-pair admission, sequence capacity, the complete public
withoutRedundantEdges pass and convergence remain separate obligations.
Practical host width, solver composition and Haskell refinement remain open.

All old proofs, counterexamples, marked drafts and optimized code remain.
All 268 Haskell and 207 active package files remain unchanged.
The only old Lean edit is one Audit import. FINDINGS retains the external
Haskell repair index FIRST. Work continues.
'''
findings = update
focused = f'''# Same-symbol edge forward completion

Updated: {now}. Proof checkpoint: `{proof}`. Start: `{start}`.

both_miss_complete derives native and wrapper completion. It does not
assume an observed native or wrapper success. It retains the actual
populated caller and its distinct pair memo. Both requested pair keys
must be absent at entry. It resets no table and changes no width.

The genuine current packet includes source Facts, an input model and
ranked inputs. It includes EdgeScope, Good, Contextual, SemanticReady,
matching symbols, EdgeReady, source growth/history and ActiveAbove at
the required fuel. It also includes semantic-interpreter Completes and
WordRanges for the actual ordered edgeBody request at emptyDomain.
Completes states that the semantic interpreter returns successfully at
some finite fuel. It is not native or wrapper success. Deriving it for
every cluster pair remains a separate admission/completion obligation.

The result contains an actual wrapper done equation and one native
contextual Receipt at the SAME result and full checked before/after.
That Receipt supplies the native completion equation, physical trace,
resident result, Good, Contextual, SemanticReady, machine Extension,
heap Keeps and equality-operation Grows. Its EdgeLaw is contextual.
It does not assert an unconditional total physical-language meet.

The original ordered pair cell captures the original operands and
returns this result. A strict reversal uses a distinct reversed handle
with the same result. FlatMemoThunk.Returned retains earlier completed
pair cells. No native requestEdge cache is identified with this memo.

Selected source: {SOURCE_LINES} lines, SHA `{SOURCE_SHA}`.
Selected clean strict: `{strict}`. Sole selected FULL: `{full}`.
Strict has a literal-empty log. Proof declaration limits stay unchanged.
FULL retains {len(raw)} raw bytes. Check/print TYPE bytes are identical:
{len(checked.splitlines())} logical lines, {checked.count(bytes([10]))} LF,
{len(checked)} bytes and {len(checked.decode())} Unicode characters.
Actual axioms: {', '.join(head['actual_axioms']) or 'none'}.
Four private markers are absent from TYPE. The actual private-helper
checks remain in the full readback. Private body names are permitted.
The complete proof body remains retained. No whole manual body read is claimed.

The actual ledger has {metrics['actual_jobs']} Lean/Lake commands:
{metrics['source_jobs']} source and {metrics['audit_jobs']} Audit commands,
{metrics['failed_jobs']} failed commands, {metrics['warned_source_exit_zero_jobs']}
warned source exit-zero commands and {metrics['rejected_public_type_jobs']}
rejected PUBLIC TYPE commands. All actual inputs, raw logs and exact
repair history remain. Metadata work creates no proof command.
Audit passes with {metrics['audit_build_jobs']} jobs and
{metrics['audit_dependencies']} theorem dependencies. Its actual warning
details remain in the retained log.

No unconditional Scoped, Covered or Idle result is added. Warm pair hits
still need historical writer/residency/law invariants. All-pair source
admission and completion, sequence fuel/width/WordRanges, ruleOut and
cluster control, recursive Mu mapping and the complete public pass
remain open. So do convergence, practical fixed host width, external
solver composition and Haskell refinement. No runtime or Haskell change
is claimed. The strongest combined constructed_node_calls result is unchanged.

All old proof components, counterexamples, marked drafts and optimized
code remain. All 268 Haskell and 207 active package files remain unchanged.
The one old Lean change is the Audit import. The external repair index
remains FIRST in FINDINGS. The whole formalization goal stays active.
'''
documents = ['NEXT-PROMPT.md', 'HANDOFF.md', 'FINDINGS.md', 'lean/README.md',
    'lean/SYSTEM.md', 'lean/API-COVERAGE.md', 'lean/COVERAGE.md',
    'lean/notes-proof-status-20261017.md', 'lean/notes-current-system-claim.md']
index = (ROOT / 'lean/restart-evidence/20261021-warm-next-packet/haskell-repair-index.md').read_text()
(HERE / 'haskell-repair-index.md').write_text(index)
for name in documents:
    original = subprocess.check_output(['git', 'show', start + ':' + name], cwd=ROOT, text=True)
    assert (ROOT / name).read_text() == original, name
    if name == 'FINDINGS.md':
        marker = '# Current formalization findings\n\n## Haskell fix handoff for external work\n\n'
        marker += index.rstrip() + '\n\n'
        assert original.startswith(marker)
        changed = marker + findings + '\n' + original[len(marker):]
        assert changed.startswith(marker + findings + '\n')
    else:
        first, rest = original.split('\n', 1)
        changed = first + '\n\n' + update + rest
        assert changed.startswith(first + '\n\n' + update)
    assert changed.replace((findings if name == 'FINDINGS.md' else update) + '\n', '', 1) == original
    (ROOT / name).write_text(changed)
(HERE / 'current-update.md').write_text(update)
(HERE / 'findings-update.md').write_text(findings)
note = ROOT / 'lean/notes-current-same-symbol-edge-forward-completion.md'
assert not note.exists()
note.write_text(focused)
print('Updated nine documents and focused note. All prior text remains.')
