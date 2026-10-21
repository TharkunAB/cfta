import datetime
import hashlib
import json
import subprocess
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
start = (HERE / 'starting-head.txt').read_text().strip()
proof = (HERE / 'proof-commit.txt').read_text().strip()
now = datetime.datetime.now().astimezone().strftime('%Y-%m-%d %H:%M %Z')
assert json.loads((HERE / 'audit-1.json').read_text())['exit_code'] == 0
audit = (HERE / 'audit-1.log').read_text()
assert 'Build completed successfully (3620 jobs).' in audit
assert '75252 MicroCFTA theorems' in audit
selected = json.loads((HERE / 'selected-sources.json').read_text())
for name, pin in selected.items():
    assert hashlib.sha256((ROOT / name).read_bytes()).hexdigest() == pin['sha256']
    assert not (HERE / (pin['strict'] + '.log')).read_bytes()
    assert json.loads((HERE / (pin['full'] + '.json')).read_text())['exit_code'] == 0

update = f'''## Finite-round numeric reservations

Updated: {now}. Proof checkpoint: `{proof[:10]}`.
Start: `{start[:10]}`. Imported main remains `794903b3f`.
Read `lean/notes-current-finite-round-forecast.md`.

SourceCurrentPositiveQuotientCount.count_le_mass proves the unconditional
count bound for every value and every inherited constraint list.
Its candidate-path bound holds for every fuel. Mapping, filtering and
duplicate removal cannot increase the list length. The 62-line addition
preserves every byte of the original 195-line module and its public API.

SourceCurrentFiniteRoundForecast supplies stage, fuelBounds and stage_bounds.
For any finite round count, each stage joins every count/mass grid case at
that exact stage entry. Each case retains BOTH the C output and its
own-work old schedule, including both profiles and both guard alphabets.
The final profile supplies one mathematical width for all selected cases.
Finite maxima bound outer work and nodeNeed at the same stage entries.
The theorem covers stage retention, alphabet inclusion, Room and both fuels.
It includes zero rounds and endpoint ranks. The new module has 160 lines.

No C monotonicity across seeds is assumed. Keep every exact stage seed.
Do not recompute an earlier C case at the final seed. A future consumer
must obtain a completed call at its own base W, then use Adequacy stability
to identify the SAME result and full after state at a common larger fuel.
This avoids a Room premise for the schedule at that larger common fuel.

Selected strict checks and one sole FULL per module pass. Root and
independent review read all 145 public TYPE lines across four declarations.
Their complete check/print types agree. No private helper or dagger name
occurs in those TYPEs. Actual axioms are the standard three in each case.
Declaration limits remain unchanged. Audit adds only the new module import.
Audit passes: 3620 jobs /75252 theorem dependencies.
Eight actual Lean/Lake commands include three failed strict checks.
Selected strict logs are empty. Only the old Audit warning remains.
All failed sources, raw logs, exact repairs and metadata failures remain.
The finite reader needs exact directive-line counts for stage/stage_bounds.
That metadata repair causes no FULL repeat. Copies add no proof jobs.

These are pure mathematical reservations. The completed-return packet
assembler and the finite-N actual execution consumer remain unproved.
The saved source-only packet plan can use InitialActual once, its actual
Post/context and NodeCall graph, then existing stores, closure, Origins,
Ready growth and NoNewActive. It needs no extra RankResources premise.
It must retain the SAME populated caller, inventory and global memos.
The reviewed plan and exact proposed header remain restart evidence.

The strongest combined execution theorem remains the checked cold theorem:
one source-built cold node call succeeds at sufficient mathematical width
and preserves exact finite-term language relative to the guard evaluator.
Practical fixed widths, full repeated-pass composition and convergence,
solver-contract and exported-table composition, and Haskell refinement
remain open. Counts do not measure whole-library completion.

All earlier proofs, counterexamples, marked drafts and optimized interned
sources remain. Older constructor and equality work remains secondary.
No Haskell source, package, repair or runtime result changes.
FINDINGS keeps the external Haskell repair index FIRST. Work continues.
'''
findings = f'''Current proof update: {now}. Proof checkpoint: `{proof[:10]}`.
The unconditional positive quotient count is bounded by structural mass.
The finite-round forecast now proves a mathematical reservation over every
bounded count/mass case at each exact stage entry. It joins both profiles
and alphabets and supplies one width plus common work/nodeNeed ceilings.
No cross-seed C monotonicity, caller widening or future success is assumed.

The original count module is retained byte-for-byte by a 62-line append.
The new forecast module has 160 lines. Strict checks, sole FULLs, complete
public TYPE review and Audit pass: 3620 jobs /75252 dependencies.
Eight actual Lean/Lake commands include three failed strict checks.
Local lawful BEq binders repair two dedup instance mismatches. Clearing an
unused dependent bound and removing redundant dsimp calls repair the
forecast proof. Exact sources, failures and repairs remain retained.
One exact-line metadata reader repair needs no FULL repeat.
Only the old Audit warning remains. No new axiom is used.

The complete next-entry packet and actual repeated-call composition remain
open. A source-only next packet plan retains the actual after caller and
its returned inventory and memos. Practical machine bounds, convergence,
solver/API composition and Haskell correspondence remain open.
No Haskell source, package, repair or runtime result changes.
The external Haskell repair index stays FIRST.
Read `lean/notes-current-finite-round-forecast.md`.
'''
documents = ['NEXT-PROMPT.md', 'HANDOFF.md', 'FINDINGS.md', 'lean/README.md',
             'lean/SYSTEM.md', 'lean/API-COVERAGE.md', 'lean/COVERAGE.md',
             'lean/notes-proof-status-20261017.md', 'lean/notes-current-system-claim.md']
index = (ROOT / 'lean/restart-evidence/20261021-warm-return/haskell-repair-index.md').read_text()
(HERE / 'haskell-repair-index.md').write_text(index)
for name in documents:
    original = subprocess.check_output(['git', 'show', start + ':' + name], cwd=ROOT, text=True)
    assert (ROOT / name).read_text() == original, name
    if name == 'FINDINGS.md':
        marker = '# Current formalization findings\n\n## Haskell fix handoff for external work\n\n'
        marker += index.rstrip() + '\n\n'
        assert original.startswith(marker)
        changed = marker + findings + '\n' + original[len(marker):]
        assert changed.replace(findings + '\n', '', 1) == original
    else:
        first, rest = original.split('\n', 1)
        changed = first + '\n\n' + update + rest
        assert changed.replace(update + '\n', '', 1) == original
    (ROOT / name).write_text(changed)
(HERE / 'current-update.md').write_text(update)
(HERE / 'findings-update.md').write_text(findings)
note = '# Finite-round numeric reservations\n\n' + update
for name, pin in selected.items():
    raw = (HERE / (pin['full'] + '.log')).read_bytes()
    note += f"\n{name}: source SHA256 {pin['sha256']}.\n"
    note += f"Sole FULL: {len(raw)} bytes; SHA256 {hashlib.sha256(raw).hexdigest()}.\n"
(ROOT / 'lean/notes-current-finite-round-forecast.md').write_text(note)
print('Updated nine documents and focused note. All prior text remains.')
