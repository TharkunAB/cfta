import datetime
import hashlib
import json
import subprocess
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
SOURCE_SHA = '__H15_SOURCE_SHA__'
SOURCE_LINES = int('__H15_SOURCE_LINES__')
strict, full, audit_stem = '__H15_STRICT_STEM__', '__H15_FULL_STEM__', '__H15_AUDIT_STEM__'
metrics = {
    'actual_jobs': int('__H15_ACTUAL_JOBS__'),
    'source_jobs': int('__H15_SOURCE_JOBS__'),
    'audit_jobs': int('__H15_AUDIT_JOBS__'),
    'failed_jobs': int('__H15_FAILED_JOBS__'),
    'warned_source_exit_zero_jobs': int('__H15_WARNED_SOURCE_EXIT_ZERO_JOBS__'),
    'rejected_public_type_jobs': int('__H15_REJECTED_PUBLIC_TYPE_JOBS__'),
    'audit_build_jobs': int('__H15_AUDIT_BUILD_JOBS__'),
    'audit_dependencies': int('__H15_AUDIT_DEPENDENCIES__'),
}
start = (HERE / 'starting-head.txt').read_text().strip()
assert start == 'e8a0066c6088d87cc0b0ea9085a07ba2ff44913c'
proof = (HERE / 'proof-commit.txt').read_text().strip()
assert len(proof) == 40 and all(c in '0123456789abcdef' for c in proof)
assert subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip() == proof
assert subprocess.check_output(['git', 'branch', '--show-current'], cwd=ROOT, text=True).strip() == 'formalize'
now = datetime.datetime.now().astimezone().strftime('%Y-%m-%d %H:%M %Z')
gate = json.loads((HERE / 'selected-source-gate.json').read_text())
source_path = 'lean/MicroCFTA/SourceCurrentSameSymbolEdgeComparisonDomains.lean'
assert gate['status'] == 'ROOT_ACCEPTED' and gate['path'] == source_path
source = (ROOT / source_path).read_bytes()
assert hashlib.sha256(source).hexdigest() == gate['sha256'] == SOURCE_SHA
assert source == (HERE / gate['snapshot']).read_bytes() and len(source.splitlines()) == gate['lines'] == SOURCE_LINES
assert source == (HERE / (strict + '.source.lean')).read_bytes() and (HERE / (strict + '.log')).read_bytes() == b''
assert json.loads((HERE / (strict + '.json')).read_text())['exit_code'] == 0
raw = (HERE / (full + '.log')).read_bytes()
assert hashlib.sha256(raw).hexdigest() == '__H15_FULL_RAW_SHA__'
assert json.loads((HERE / (full + '.json')).read_text())['exit_code'] == 0
readback = json.loads((HERE / 'public-readback/same-symbol-edge-comparison-domains-full-readback.json').read_text())
assert readback['source_sha256'] == SOURCE_SHA and readback['source_lines'] == SOURCE_LINES
assert readback['log_sha256'] == hashlib.sha256(raw).hexdigest() and readback['log_bytes'] == len(raw)
assert readback['owned_public_job_exit'] == 0 and readback['no_omissions'] and len(readback['heads']) == 1
review = json.loads((HERE / 'root-full-review.json').read_text())
assert review['complete_public_type_root_review'] == review['independent_complete_public_type_review'] == 'CLEAR'
head_specs = [
    ('original_rows_complete', '__H15_TYPE_SHA__', 'public-readback/same-symbol-edge-comparison-domains-original_rows_complete-public-type.txt', 'public-readback/same-symbol-edge-comparison-domains-original_rows_complete-printed-public-type.txt', '__H15_AXIOMS_JSON__'),
]
heads = {head['head'].rsplit('.', 1)[1]: head for head in readback['heads']}
assert set(heads) == {spec[0] for spec in head_specs}
checked_types = {}
for short, type_sha, type_path, printed_path, axioms_json in head_specs:
    head = heads[short]
    assert head['head'] == 'MicroCFTA.SourceCurrentSameSymbolEdgeComparisonDomains.' + short
    assert head['check_print_type_identity'] and head['check_print_type_byte_identity'] and head['unique_complete_type_body_delimiter']
    checked = (HERE / type_path).read_bytes()
    assert checked == (HERE / printed_path).read_bytes() and hashlib.sha256(checked).hexdigest() == type_sha
    assert not any(marker in checked.decode() for marker in ['_private', '✝', '†', '‡']) and head['private_public_type_names'] is False
    assert head['actual_axioms'] == json.loads(axioms_json)
    assert head['actual_axioms_within_standard_allowed'] and set(head['actual_axioms']) <= {'Classical.choice', 'Quot.sound', 'propext'}
    checked_types[short] = checked
proof_report = json.loads((HERE / 'proof-evidence-normal.json').read_text())
assert proof_report['status'] == 'PASS' and all(proof_report[key] == value for key, value in metrics.items())
audit = (HERE / (audit_stem + '.log')).read_bytes()
assert hashlib.sha256(audit).hexdigest() == proof_report['audit_log_sha256'] == '__H15_AUDIT_SHA__'
assert json.loads((HERE / (audit_stem + '.json')).read_text())['exit_code'] == 0
assert f"Build completed successfully ({metrics['audit_build_jobs']} jobs).".encode() in audit
assert f"{metrics['audit_dependencies']} MicroCFTA theorems".encode() in audit

type_summary = '\n'.join(
    f"{short} TYPE: {len(data.splitlines())} logical lines, {data.count(bytes([10]))} LF, {len(data)} bytes, {len(data.decode())} characters.\n"
    f"{short} actual axioms: {', '.join(heads[short]['actual_axioms']) or 'none'}."
    for short, data in checked_types.items())
update = f'''## Domain history across original-row comparisons

Updated: {now}. Proof checkpoint: `{proof[:10]}`.
Start: `{start[:10]}`. Imported main remains `794903b3f`.
Read `lean/notes-current-same-symbol-edge-comparison-domains.md`.

SourceCurrentSameSymbolEdgeComparisonDomains.original_rows_complete derives an
actual comparison result and its SAME global domain allocation history.
The source, models, populated checked state and pair memo stay correlated.
Available closed OriginalInput parents and literal same-symbol rows remain explicit.
The initial domain cache, its Valid witness and actual past allocation Trace stay fixed.
One initial Room reservation derives current-call Room from the same finite inventory.
Current Good, Contextual, SemanticReady, Stable, native Idle and source history remain explicit.
The result retains all comparison outputs and the SAME initial-to-after allocation Trace.
No cache reset, new per-call history, future Room or successful run is a premise.
Ready hits have no native Receipt claim. Actual finite-scan control is not proved.

H6 constructed_node_calls remains the strongest combined semantic theorem.
Generated-parent provenance, source/model rebase, physical language iff,
public Mu/full-pass and Haskell refinement remain open. The goal is incomplete.

Preservation covers 85212 baseline files/modes, 298 baseline Haskell files
and 207 active package files. Only one Audit import and nine additive doc
prefixes may change old files. FINDINGS keeps its repair index FIRST.
The preceding e8a0066c checkpoint is LOCAL_ONLY. Remote publication remains
PENDING_USER_APPROVAL. This tool performs no push or network command.
'''
findings = update
focused = f'''# Domain history across original-row comparisons

Updated: {now}. Proof checkpoint: `{proof}`. Start: `{start}`.

original_rows_complete derives an actual comparison result and the SAME
fixed-source global domain allocation Trace through every pair-cache branch.
The requested edges are literal same-symbol rows of available closed
OriginalInput parents. Source Facts, executable guards, view, model and ranks stay fixed.
The populated caller is not reset. The initial domain cache and its Valid witness
stay fixed. The incoming Trace records actual past allocations from that cache.
Current Good, Contextual, SemanticReady, Stable, native Idle and source history remain explicit.
Let I be the domains inventory computed from the fixed source.
The initial Room profile uses source node/edge counters, initialDomains.next + I.length,
and mass 0. Trace.next_le and Room.mono derive the current-call Room.
No cache branch, future history, successful run or desired result law is a premise.

The actual execute equation uses the SAME result and full returned state.
The result is resident and has the canonical conditional contextual EdgeLaw.
The output retains Good, Contextual, SemanticReady, native-machine Extension,
Stable, native Idle, pair-table Extends, Returned and Trace I initialDomains afterDomains.
The proof retains one global history. It does not restart that history at each call.
Ready hits retain the exact checked state and assert no native Receipt.
The miss path uses its actual native receipt and the existing prefix admission theorem.
The initial reservation supports next-call Room under this retained packet.
No actual finite scan, generated Mu parent, reset, source/model rebase,
practical width bound or independent physical language iff is proved.
H6 constructed_node_calls remains the strongest combined semantic theorem.
Public Mu unfolding/kept-body, full pass, practical width, solver contracts,
convergence and Haskell refinement remain open. The goal stays incomplete.

Selected source: {SOURCE_LINES} lines, SHA `{SOURCE_SHA}`.
Selected clean strict: `{strict}`. Selected FULL: `{full}`.
Strict has a literal-empty log. Declaration limits remain unchanged.
FULL retains {len(raw)} raw bytes. Complete check/print TYPE bytes agree.
{type_summary}
Root and an independent reviewer read the complete checked public TYPE.
The printed TYPE is byte-identical. No second manual TYPE read is claimed.
All four private markers and recorded helper names are absent from TYPE.
The whole proof body is retained and checked programmatically.
No whole manual body read is claimed.

The actual ledger has {metrics['actual_jobs']} Lean/Lake commands:
{metrics['source_jobs']} source and {metrics['audit_jobs']} Audit commands,
{metrics['failed_jobs']} failures, {metrics['warned_source_exit_zero_jobs']}
warned source exit-zero commands and {metrics['rejected_public_type_jobs']}
rejected PUBLIC TYPE commands. Every actual input and raw log remains.
Metadata work creates no proof command. Audit has
{metrics['audit_build_jobs']} jobs and {metrics['audit_dependencies']} theorem
dependencies. This writer does not claim seal or publication success.

Preservation covers 85212 starting files/modes. The older non-Audit Lean
count comes from the exact start manifest. All 298 baseline Haskell files,
207 active package files, old proofs, drafts and optimized code remain.
Additional H15 Haskell archives must match baseline source bytes under H15.
Every old document has an exact inverse. The original Audit has 3120
lines and SHA fa6c433f47dca1a9b5433edd416e98f742592352920ecd5969494e0b977d4d37. Its only edit is the new module import.
FINDINGS keeps the external repair index FIRST. PR #65 and PR #97 stay fixed.
No Haskell repair or runtime change is added.

The preceding e8a0066c checkpoint is LOCAL_ONLY. Earlier automatic approval
review rejected pushes. Continuing the goal is not fresh user approval.
The local publisher keeps seal, staging and filesystem/index/HEAD checks.
It records PENDING_USER_APPROVAL and performs no network command.
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
note = ROOT / 'lean/notes-current-same-symbol-edge-comparison-domains.md'
assert not note.exists()
note.write_text(focused)
print('Updated nine documents and focused note. All prior text remains.')
