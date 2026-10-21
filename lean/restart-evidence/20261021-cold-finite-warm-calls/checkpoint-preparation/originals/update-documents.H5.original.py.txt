import datetime
import hashlib
import json
import subprocess
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
start = (HERE / 'starting-head.txt').read_text().strip()
assert start == '8adf2d4aca20ee029de027462bca2878c4c599bf'
proof = (HERE / 'proof-commit.txt').read_text().strip()
assert len(proof) == 40 and all(char in '0123456789abcdef' for char in proof)
now = datetime.datetime.now().astimezone().strftime('%Y-%m-%d %H:%M %Z')
assert json.loads((HERE / 'audit-1.json').read_text())['exit_code'] == 0
audit_raw = (HERE / 'audit-1.log').read_bytes()
assert hashlib.sha256(audit_raw).hexdigest() == 'a8c25c6823eccbec8ca6e579e2d58ebc95e00f4e36066777735b4bbd518eeffc'
audit = audit_raw.decode()
assert 'Build completed successfully (3622 jobs).' in audit
assert '75262 MicroCFTA theorems' in audit
selected = json.loads((HERE / 'selected-sources.json').read_text())
assert set(selected) == {'lean/MicroCFTA/SourceCurrentFiniteWarmCalls.lean'}
assert selected[next(iter(selected))]['sha256'] == '984f34529a1050fd015ba0fb742b39cc38e0b518eaae69801cbde1727578a6bd'
readback = json.loads((HERE / 'finite-full-readback.json').read_text())
assert readback['log_bytes'] == 2183150 and readback['log_sha256'] == 'd436796fb8f90561c1dc0c97a4c8944e24fd2ae84bd7d38027df551f6ac01393'
checked = (HERE / 'finite-node_calls-public-type.txt').read_bytes()
assert checked == (HERE / 'finite-node_calls-printed-public-type.txt').read_bytes()
assert len(checked) == 31520 and len(checked.decode()) == 31480
assert len(checked.splitlines()) == 365 and checked.count(b'\n') == 364 and not checked.endswith(b'\n')
assert hashlib.sha256(checked).hexdigest() == '176e32dc0018cc4bba9f5aad9a2d08ad09a75ef4f589e520d7afe98ebb6ff301'
head = readback['heads'][0]
assert head['actual_standard_three_axioms'] and head['check_print_type_byte_identity']
assert not head['private_public_type_names']
assert head['private_type_spellings_checked'] == ['_private', '✝', '†', '‡']
assert head['private_namespace_helpers_checked'] == ['Entry', 'advance_entry']
for name, pin in selected.items():
    assert hashlib.sha256((ROOT / name).read_bytes()).hexdigest() == pin['sha256']
    assert not (HERE / (pin['strict'] + '.log')).read_bytes()
    assert json.loads((HERE / (pin['full'] + '.json')).read_text())['exit_code'] == 0

update = f'''## Finite calls through a populated caller

Updated: {now}. Proof checkpoint: `{proof[:10]}`.
Start: `{start[:10]}`. Imported main remains `794903b3f`.
Read `lean/notes-current-finite-warm-calls.md`.

SourceCurrentFiniteWarmCalls.node_calls now proves an actual trace of any
finite number N of modeled nodeCall rounds. One mathematical width from
stage N and ten common fuel arguments are chosen before the first call.
Each next caller is the previous actual full return. The SAME arbitrary
ready inherited Value and allocation identity remain fixed in every round.

The initial genuine Context, resources, stores, closed value, Origins,
NodeStored and both idle conditions are explicit premises. There is no
future Room or success premise, caller reset or width change. Fits.stored
and actual availability bound mass. count_le_mass bounds the actual
inherited quotient count. The finite forecast supplies joined case Room
and common outer and nine lower-fuel ceilings at each exact stage seed.

Adequacy gives success at each base W and the SAME result and full after
at common outer fuel. WarmNextPacket uses only that base-W equation.
Its actual Post supplies the next inventory and global memos. A second
forecast use at i+1 promotes scheduled Fits and the guard carrier to the
exact next seed. No C monotonicity across seeds or Room for the common-F
schedule is used. One prefix induction retains the actual entry packet.

The final value is Available in the final caller's heap. Its cumulative
NodeLaw is relative to the INITIAL value and the SAME arbitrary inherited
Value. It gives unconditional language narrowing. Language equivalence
holds ONLY when the term satisfies that inherited payload. It is not an
unconditional equivalence theorem for arbitrary inherited values.

The new module has 236 lines and one public theorem. Selected ordinary
strict3 passes at default declaration limits with an empty raw log.
The sole FULL passes. Root and independent review read all 365 logical
public TYPE lines: 364 LF characters and no final newline, 31480 Unicode
characters and 31520 bytes. Complete check/print TYPEs are byte-identical.
All four private/dagger markers and Entry/advance_entry are absent from
those TYPEs. Actual axioms are the standard three.
FULL raw: 2183150 bytes; SHA256
d436796fb8f90561c1dc0c97a4c8944e24fd2ae84bd7d38027df551f6ac01393.
Audit passes: 3622 jobs /75262 theorem dependencies.

Five actual ROOT Lean/Lake commands are retained. Strict1 failed with a
type error and 46 warnings at the original source. Four private lines
fixed Entry's bits+2 type and ite lemma names. Strict2 exited zero with
15 unused-public-binder warnings. Alpha-only underscore names removed
those warnings for strict3. The old 35-line f064b85a header and corrected
35-line fa50a08f header remain. Sole FULL and Audit pass. Only the old
Audit inputs warning remains. Copies and metadata add no proof jobs.

The next cold finite source-construction wrapper is a reviewed SOURCE-ONLY
plan. It is not implemented. It must choose the final width before the
fresh caller and use one eventual finite producer invocation. The strongest
combined COLD semantic theorem still covers one constructed node call.
Practical fixed-width feasibility, the public withoutRedundantEdges pass,
convergence, solver-contract/exported-table composition and Haskell
refinement remain open. This trace theorem does not prove those results.

All old proofs, counterexamples, marked drafts and optimized core remain.
The only old Lean edit is one Audit import. All 268 Haskell files and 207
active package files remain unchanged. No Haskell fix or runtime result
is claimed. FINDINGS keeps the external Haskell repair index FIRST.
Work continues.
'''
findings = f'''Current proof update: {now}. Proof checkpoint: `{proof[:10]}`.
FiniteWarmCalls.node_calls proves N actual continuous nodeCall rounds
through the SAME populated full caller state. One stage-N mathematical
width and ten common fuels are fixed before the calls. The SAME arbitrary
ready inherited Value remains fixed. The initial genuine packet is an
explicit premise; there is no future Room, success, reset or widening.

Exact stage seeds retain actual next inventory and memos. Base-W success
and same-after stability avoid a common-F schedule Room premise. Final
Available and cumulative NodeLaw refer to the INITIAL value and SAME
inherited Value. Narrowing is unconditional; equivalence is ONLY under
that payload's Sat condition. No across-seed C monotonicity is assumed.

The 236-line module has one public theorem. Selected strict3, sole FULL
and Audit pass: 3622 jobs /75262 dependencies. Five actual ROOT commands
include one failed strict and one warned zero. The four private fixes and
15 public alpha renames are retained. All 365 logical TYPE lines were
reviewed. Complete TYPE bytes match; all four private markers and both
private helper names are absent. Actual axioms are the standard three.

The next cold finite constructor is SOURCE-ONLY, not implemented. The
strongest combined cold semantic theorem still covers one constructed
call. Practical width, public pass composition, convergence, solver/API
composition and Haskell refinement remain open. All old evidence and
optimized core remain; no Haskell source/package/fix/runtime change.
The external Haskell repair index stays FIRST.
Read `lean/notes-current-finite-warm-calls.md`.
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
        assert changed.replace(findings + '\n', '', 1) == original
    else:
        first, rest = original.split('\n', 1)
        changed = first + '\n\n' + update + rest
        assert changed.replace(update + '\n', '', 1) == original
    (ROOT / name).write_text(changed)
(HERE / 'current-update.md').write_text(update)
(HERE / 'findings-update.md').write_text(findings)
note = '# Finite calls through a populated caller\n\n' + update
for name, pin in selected.items():
    raw = (HERE / (pin['full'] + '.log')).read_bytes()
    note += f"\n{name}: source SHA256 {pin['sha256']}.\n"
    note += f"Sole FULL: {len(raw)} bytes; SHA256 {hashlib.sha256(raw).hexdigest()}.\n"
assert not (ROOT / 'lean/notes-current-finite-warm-calls.md').exists()
(ROOT / 'lean/notes-current-finite-warm-calls.md').write_text(note)
print('Updated nine documents and focused note. All prior text remains.')
