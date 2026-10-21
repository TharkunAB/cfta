import datetime
import hashlib
import json
import subprocess
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
start = (HERE / 'starting-head.txt').read_text().strip()
proof = (HERE / 'proof-commit-rank-envelope.txt').read_text().strip()
now = datetime.datetime.now().astimezone().strftime('%Y-%m-%d %H:%M %Z')
cfg = json.loads((HERE / 'checkpoint-result.json').read_text())
source_sha = 'b8401732ae63be4d2036ccd4af7997b787ced8787789a1fb9d2e354047fde5ba'
assert hashlib.sha256((ROOT / 'lean/MicroCFTA/SourceCurrentOuterRankEnvelope.lean').read_bytes()).hexdigest() == source_sha
assert not (HERE / 'rank-envelope-strict-1.log').read_bytes()
audit = (HERE / 'audit-1.log').read_text()
assert f"Build completed successfully ({cfg['audit_jobs']} jobs)" in audit
assert f"{cfg['audit_dependencies']} MicroCFTA theorems" in audit
assert {v['path'] for v in json.loads((HERE / 'components.json').read_text())} == {'rank-envelope', 'independent-review', 'rank-envelope-plan', 'rank-envelope-plan-review'}
full = (HERE / cfg['full_relative_path']).read_bytes()
assert len(full) == cfg['full_bytes'] and hashlib.sha256(full).hexdigest() == cfg['full_sha256']
update = f'''## Current finite rank envelope and entry retention

Updated: {now}. Proof checkpoint: `{proof[:10]}`.
Start: `{start[:10]}`. Imported main remains `794903b3f`.
Read `lean/notes-current-outer-rank-envelope.md`.

OuterRankEnvelope.envelope now defines a finite numeric prediction from
budget, count, mass, raw guard alphabet and numeric profile. It returns
work W, a lower-fuel maximum L, and an output alphabet/profile.
It uses strict Lex(count,mass) recursion with the seed as a further input.
Each slot evaluates every bounded smaller rank at THAT current seed.
It joins candidate outputs, then passes the joined seed to the next slot.
Each row starts with the existing Parent forecast and fixes its returned
mass as the slot count. Original mass bounds the number of numeric rows.
The row and final body use the existing raw-constructor forecast.
The function is noncomputable in Lean. No runtime evaluation is claimed.

OuterRankEnvelope.retains proves only mass+1 <= W and retention of the
ENTRY profile and alphabet. It has no physical or completion premise.
The concrete recurrence is internal; callers supply no recursive callback.
The exact eight-line public type has one definition and one theorem.
The selected source has 157 lines, below the 250-total-line stop.

The original all-stage theorem remains UNPROVED. This first result does
not prove child-work offsets, candidate-output coverage, intermediate
Parent peaks, or the lower maximum at all numeric stages. It also does
not prove correspondence with actual states or adequate outer fuel.
The preserved 42-line original proposal and exact equations specify that
next target. They are unelaborated source evidence, not a compiled API.
The original 215-265 estimate did not support its claimed 250 upper target.
The corrected two-head scope, original bytes and separate correction remain.

Selected author strict4 and root strict have empty logs. The sole complete
FULL covers BOTH declarations. Whole type identity, all eight settings,
no private names in either public type, and actual per-head axioms pass.
Audit passes: {cfg['audit_jobs']} jobs /{cfg['audit_dependencies']} dependencies.
There are {cfg['actual_jobs']} actual Lean/Lake commands and {cfg['failed_jobs']} failed commands.
The three failed strict checks and complete raw diagnostics remain.
Strict1 exposed a decider, pair eta, and a normalization timeout. The next
two checks retained the timeout. Strict4 names the ACTUAL Parent seed,
keeps its defining equality and rewrites the real retention fact with it.
This prevents deep forecast normalization. The strict proof budget did not
increase. All actual selected checks have no new warning. The old Audit
warning remains. No canonical, infrastructure, constructed, runtime or
reviewer proof job ran. Counts are not completion.

The strongest outer execution result remains DoneOrExhausted: the actual
formalized outer run returns normally or fails only with outer-fuel
exhaustion under its FULL stated initial packet and nine lower-fuel bounds.
That run erases successful output to Unit. The new pure calculation does
not strengthen this execution result yet.

The largest execution gap remains sufficient OUTER fuel jointly with
noncircular INITIAL capacity for the SAME run. A concrete numeric work
value now exists. Its adequacy remains unproved. Next prove all numeric
stage laws, then connect them to actual reached cuts under ONE original
initial packet. Retain current mass bounds after earlier sibling growth.
Cover all intermediate Parent profiles and all nested lower fuels.
Prove root-schedule domination or reserve an initial finite join and prove
its coverage. Do not assume future success or a per-future Room callback.
A child Prefix restart still needs extra unproved child-schedule Room.
Fixed-width feasibility and state widening remain separate open issues.
Existing request-coherence laws can relate a selected request to its
captured owner; key equality alone does not state full request equality.

Finite renewals, final retention, successful completion, convergence,
broader resources and Haskell refinement remain open. Whole-library
termination is not proved. The broadest semantic result remains exact
finite-term language preservation for a supported successful traversal
with empty inherited constraints. General inherited constraints give
narrowing, with exactness under inherited satisfaction.

All earlier proofs, failures and counterexamples remain. Haskell, packages,
imported main, stashes and other worktrees stay unchanged. No new Haskell
defect or repair. FINDINGS keeps its external repair index FIRST.
Work continues at the user's request.
'''
findings = f'''Current proof update: {now}. Proof checkpoint: `{proof[:10]}`.
A concrete finite rank-envelope function and entry-retention theorem now
pass Lean. The function returns W, L and an alphabet/profile from initial
numeric data. It uses genuine strict Lex(count,mass) recursion with an
evolving seed and exact chronological candidate, slot and row folds.
The theorem proves only mass+1 <= W and ENTRY profile/alphabet retention.
The exact eight-line API has one definition and one theorem. The function
is noncomputable; no runtime evaluation or Haskell behavior is claimed.

ALL-stage numeric work, output and lower-fuel coverage remain UNPROVED.
The original 42-line proposal remains a next target. The corrected first
scope preserves the original budget mistake and all original plan bytes.
Physical coverage, same-global-root resources, intermediate Parent peaks,
nested lower fuels and adequate OUTER fuel with INITIAL capacity remain
open. The strongest outer execution result remains done-or-exhausted under
its full stated packet. This pure result does not strengthen that yet.

Author strict4/root strict, sole BOTH-head FULL, independent review and
Audit pass: {cfg['audit_jobs']} jobs /{cfg['audit_dependencies']} dependencies.
{cfg['actual_jobs']} actual commands retain {cfg['failed_jobs']} failed strict checks and all full raw logs.
The selected157 source, original147/146/156/157 drafts and exact repairs
remain. The final proof abstracts the ACTUAL Parent result by its equality;
it adds no output oracle or new assumption and raises no strict proof budget.
Whole type identity, eight settings and actual per-head axioms pass.
No new warning beyond the old Audit warning. No canonical, infrastructure,
constructed, runtime or reviewer proof job ran. Counts are not completion.
No Haskell source, package, repair or runtime result changes.
Read `lean/notes-current-outer-rank-envelope.md`.
The external Haskell repair index stays FIRST.
'''
note = '# Finite rank-envelope calculation and entry retention\n\n' + update + f'''
Selected source SHA256: {source_sha}.
The sole complete two-declaration print has {cfg['full_bytes']} bytes,
SHA256 {cfg['full_sha256']}.
Printer SHA256: {cfg['printer_sha256']}.
Actual per-head axioms: {cfg['axioms_summary']}.
Root independently ran the hardened full-print reader and read the complete
checked type for BOTH public declarations. No additional print ran.

The first failed source has146 lines; the first repair has156 lines.
The controlled-unfold source has157 lines, and the final successful source
also has157 lines with a different hash. All four ACTUAL strict inputs and
complete logs remain. The original147-line namespace draft and exact
prelaunch qualification patch also remain. No source exceeded the250stop.
The original source-only plan and independent review remain immutable.
They correctly retain their historical unimplemented status. This proof
package supplies a separate actual compiled status.
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
(ROOT / 'lean/notes-current-outer-rank-envelope.md').write_text(note)
print('Updated nine documents and focused note. All prior text remains.')
