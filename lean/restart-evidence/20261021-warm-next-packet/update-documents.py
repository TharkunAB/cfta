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
assert 'Build completed successfully (3621 jobs).' in audit
assert '75253 MicroCFTA theorems' in audit
selected = json.loads((HERE / 'selected-sources.json').read_text())
assert set(selected) == {'lean/MicroCFTA/SourceCurrentWarmNextPacket.lean'}
assert selected[next(iter(selected))]['sha256'] == '13e8373cff925aca8832a47e12514767dd94dbe3fdb8d68bd73b2cdf19246be8'
readback = json.loads((HERE / 'warm-full-readback.json').read_text())
assert readback['log_bytes'] == 717427 and readback['log_sha256'] == '68cd5d5bf82cfb8fa7d0d1877c5ec78bcd9fff18052735354ba6a61ec6cbfc48'
assert len((HERE / 'warm-node_call-public-type.txt').read_text().splitlines()) == 518
assert readback['heads'][0]['actual_standard_three_axioms']
for name, pin in selected.items():
    assert hashlib.sha256((ROOT / name).read_bytes()).hexdigest() == pin['sha256']
    assert not (HERE / (pin['strict'] + '.log')).read_bytes()
    assert json.loads((HERE / (pin['full'] + '.json')).read_text())['exit_code'] == 0

update = f'''## Warm returned-entry packet

Updated: {now}. Proof checkpoint: `{proof[:10]}`.
Start: `{start[:10]}`. Imported main remains `794903b3f`.
Read `lean/notes-current-warm-next-packet.md`.

SourceCurrentWarmNextPacket.node_call now assembles the entry facts after
one observed completed node call. It retains the SAME full after caller,
returned inventory and global memos. Its actual Post supplies the returned
Context. Frame, Fits and the guard carrier use that call's own oldSchedule
profile and alphabet. The original inherited equality value remains ready.

The packet includes all five native store laws, resource writer Origins,
NodeStored, result closure and BOTH node and edge idle conditions.
InitialActual supplies one actual NodeCall graph for the same observed
return. NoNewActive maps output evaluating cells back to forbidden input
cells. The proof composes existing completed-return laws without a new
induction, table reset, width change or private helper.

This is a completed-past result. Its premises include the actual successful
equation and the genuine initial Context, resources, stores, closed input
and both idles. It proves no next-call success or capacity. Use a base-W
return from Adequacy before applying this packet; stability already fixes
the same result and full caller at larger fuel. No larger-fuel Room is
required for that use. The actual finite-N consumer remains SOURCE-ONLY
planning work. Its stage-index invariant and common-fuel composition are
not supplied by this packet theorem.

The new source has 117 lines and one public theorem. Ordinary strict
checking passes with default declaration limits and an empty raw log.
One sole FULL passes. Root and independent review read all 518 logical
public TYPE lines (517 newline characters, final line without a newline).
Complete check/print TYPEs are byte-identical. No private or dagger name
occurs in those TYPEs. Actual axioms are the standard three.
FULL raw: 717427 bytes; SHA256
68cd5d5bf82cfb8fa7d0d1877c5ec78bcd9fff18052735354ba6a61ec6cbfc48.
Audit passes: 3621 jobs /75253 theorem dependencies.
Three actual Lean/Lake commands pass. Only the old Audit warning remains.
Source review, metadata review and copied evidence add no proof jobs.

The strongest combined cold semantic theorem remains unchanged: one
source-built cold node call succeeds at sufficient mathematical width and
preserves exact finite-term language relative to the guard evaluator.
Practical fixed-width bounds, the actual finite-N consumer, full public
pass composition and convergence, solver-contract/exported-table
composition, and Haskell refinement remain open. The new packet alone
does not prove any of those results.

All earlier proofs, counterexamples and marked drafts remain. No old proof
source is rewritten. Audit adds only the WarmNextPacket import. No Haskell
source, package, repair or runtime result changes. FINDINGS keeps the
external Haskell repair index FIRST. Work continues.
'''
findings = f'''Current proof update: {now}. Proof checkpoint: `{proof[:10]}`.
The checked WarmNextPacket.node_call assembles the SAME actual returned
caller, inventory, global memos, Context, Frame, scheduled Fits/carrier,
ready inherited value, all five native store laws, Origins, NodeStored,
closed result and BOTH outer idle conditions.

The theorem assumes one already observed successful call and the genuine
entry packet. It supplies no future success, Room or capacity. No caller
reset, width change, extra RankResources law or private helper is used.
The actual finite-N consumer remains SOURCE-ONLY planning work.

The new 117-line module has one public theorem. Default-limit strict,
sole FULL and Audit pass: 3621 jobs /75253 dependencies. Three actual
Lean/Lake commands pass. Complete check/print TYPEs are byte-identical;
all 518 logical TYPE lines and actual standard-three axioms were reviewed.
No private or dagger name occurs in the TYPEs. Only the old Audit warning
remains. The only old Lean change is one Audit import.

The strongest cold semantic theorem is unchanged. Practical machine
bounds, actual repeated-call/public-pass composition, convergence,
solver/API composition and Haskell correspondence remain open.
No Haskell source, package, repair or runtime result changes.
The external Haskell repair index stays FIRST.
Read `lean/notes-current-warm-next-packet.md`.
'''
documents = ['NEXT-PROMPT.md', 'HANDOFF.md', 'FINDINGS.md', 'lean/README.md',
             'lean/SYSTEM.md', 'lean/API-COVERAGE.md', 'lean/COVERAGE.md',
             'lean/notes-proof-status-20261017.md', 'lean/notes-current-system-claim.md']
index = (ROOT / 'lean/restart-evidence/20261021-warm-rank-grid/haskell-repair-index.md').read_text()
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
note = '# Warm returned-entry packet\n\n' + update
for name, pin in selected.items():
    raw = (HERE / (pin['full'] + '.log')).read_bytes()
    note += f"\n{name}: source SHA256 {pin['sha256']}.\n"
    note += f"Sole FULL: {len(raw)} bytes; SHA256 {hashlib.sha256(raw).hexdigest()}.\n"
(ROOT / 'lean/notes-current-warm-next-packet.md').write_text(note)
print('Updated nine documents and focused note. All prior text remains.')
