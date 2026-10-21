import datetime
import hashlib
import json
import subprocess
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
start = (HERE / 'starting-head.txt').read_text().strip()
proof = (HERE / 'proof-commit-local-faults.txt').read_text().strip()
now = datetime.datetime.now().astimezone().strftime('%Y-%m-%d %H:%M %Z')
source_sha = 'aeb5829ae30afb8ff8cbeceb4d159c1414141e2e39298cbdf55f69308aad9c4a'
assert hashlib.sha256((ROOT / 'lean/MicroCFTA/SourceCurrentOuterLocalFaults.lean').read_bytes()).hexdigest() == source_sha
assert not (HERE / 'local-faults-strict-1.log').read_bytes()
audit = (HERE / 'audit-1.log').read_text()
assert 'Build completed successfully (3614 jobs)' in audit and '75095 MicroCFTA theorems' in audit
assert {v['path'] for v in json.loads((HERE / 'components.json').read_text())} == {'local-faults', 'independent-review', 'next-fault-plan', 'next-fault-plan-review'}
full = (HERE / 'local-faults/outer-local-faults-public-1.log').read_bytes()
assert len(full) == 8844547 and hashlib.sha256(full).hexdigest() == '29f0a155d41a4e87b88d18a6a9966f501db7bdd7eb3a8e928d365db8d8376be1'
update = f'''## Current actual outer failures have five precise alternatives

Updated: {now}. Proof checkpoint: `{proof[:10]}`.
Start: `{start[:10]}`. Imported main remains `794903b3f`.
Read `lean/notes-current-outer-local-faults.md`.

OuterLocalFaults.failed_cases classifies the literal failed outer run as
exhausted, nodeMemo with busy or absent, edgeMemo, unexpectedReference,
or Parent failure. It excludes binder, inherited-error and missing-field
faults. It also proves that nodeMemo cannot carry ready/evaluate payloads.
Those payloads exist in the datatype but are never emitted by this worker.

The exact 21-line public type keeps genuine initial Context, Frame, Fits,
annotation carrier, phase Inputs and chosen-fuel forecast Room. It adds no
closure, idle-cache, native Support, History or lower-fuel premise.
One local six-phase induction retains the SAME initial packet and actual
Reached cuts. Existing InitialPrefix.reached supplies current operands
and Context at those cuts. Existing resident_rebuild forces the SAME Mu
rebuild to finish. Existing resident_finite forces the SAME descendants
prefix to return ok(some combined). Literal updated operations and failed
callers remain distinct. Completed earlier siblings supply their actual
done equations. Node demand supplies busy/absent provenance directly.
No enclosing future completion or desired output callback is assumed.

Author strict1 and root strict logs are empty. The sole complete FULL,
independent review and Audit pass: 3614 jobs /75095 dependencies.
Four actual Lean/Lake commands all pass without new warnings. The old
Audit warning remains. The selected source has 216 lines and needed no
compiler repair. The original 218-line draft and exact removal of two
unused aliases remain. All eight printer settings, whole checked/printed
type identity and actual standard three axioms pass. No private Cases
predicate occurs in the public type. No canonical, infrastructure,
constructed, runtime or reviewer proof job ran. Counts are not completion.

The next source-only plan combines this producer with the checked Parent,
edgeMemo, busy-node, reference and absent-node exclusions. Its exact
34-line public type retains the full resource and closure packet, both
initial idle laws, NodeStored/InputsClosed and all nine phaseNeed bounds.
It proposes an actual done()Caller equation OR an actual exhausted(limit)
Caller equation at the SAME chosen phase and numeric arguments. It erases
only the success value. This composition remains proposed work here.
The plan stops at 150 total source lines before any compiler or further
implementation. Later activation requires an officially compiled
LocalFaults dependency and complete root and independent source review.
Historical pending cues remain unchanged with separate later status notes.

The largest gap remains a first sufficient OUTER fuel jointly with a
noncircular INITIAL capacity envelope. The chosen phaseNeed bounds only
lower workers. Room for one fuel does not imply Room for larger fuel.
Stability of an existing success does not construct the first success.
Finite renewals, final retention, completion, convergence, broader resources
and Haskell refinement remain open. Whole-library termination is not proved.
The broadest semantic claim remains exact finite-term language preservation
for a supported successful traversal with empty inherited constraints.
General inherited constraints give narrowing, with exactness under
inherited satisfaction.

All earlier proof, failure and counterexample evidence remains. Haskell,
packages, imported main, stashes and other worktrees stay unchanged.
No new Haskell defect or repair. FINDINGS keeps its external repair index
FIRST. Work continues at the user's request.
'''
findings = f'''Current proof update: {now}. Proof checkpoint: `{proof[:10]}`.
Actual outer failures now have five precise alternatives: exhausted,
nodeMemo busy/absent, edgeMemo, unexpectedReference or Parent failure.
The new checked theorem excludes binder, inherited and missing-field
faults and proves actual nodeMemo provenance. It keeps genuine initial
Context, Frame, Fits, carrier, Inputs and chosen-fuel forecast Room.
It adds no closure, idle-cache, native Support, History or lower-fuel law.
Existing local completion results apply at the SAME actual Reached cuts.

Author/root strict, sole complete FULL, independent review and Audit pass:
3614 jobs /75095 dependencies. Four actual commands all pass. No new
warnings, compiler repairs, canonical, infrastructure, runtime, constructed
or reviewer proof job. The unchanged selected 216-line source and original
218-line source with its exact two-alias removal remain. Whole type
identity, all eight settings and actual standard axioms pass. No private
Cases predicate appears in the public type.

The next proposed composition retains all stronger initial exclusions,
both idle laws, conditional closure laws and nine lower-fuel bounds.
Its exact 34-line public type says actual done or exhausted at the chosen
fuel. The source-only plan stops at 150 total source lines before any
compiler or further implementation. This composition remains open here.
Adequate OUTER fuel and noncircular INITIAL capacity remain the largest
gap. Finite renewals, retention, completion, convergence, broader resources
and Haskell refinement remain open. Counts are not completion.
No Haskell source, runtime result or external repair changes.
Read `lean/notes-current-outer-local-faults.md`.
The external Haskell repair index stays FIRST.
'''
note = '# Actual outer failure classification from initial resources\n\n' + update + f'''
The selected source SHA256 is {source_sha}.
The sole complete public print has 8844547 bytes, SHA256
29f0a155d41a4e87b88d18a6a9966f501db7bdd7eb3a8e928d365db8d8376be1.
Its printer SHA256 is
5074d319942353e5bd5360a0b7554b0ff52596b356f891687b18d408fd252946.
The normalized public type has 9400 characters. The complete proof has
8814477 characters. Root independently ran the hardened public reader
and read the whole checked public type. All four actual Lean/Lake jobs
pass. Copied receipts do not add jobs. All older failed jobs remain.

The proof captures its original resource packet once inside the public
theorem. Each local induction argument carries an actual Reached prefix.
The descendants case obtains the exact current resident edge and inherited
Ready from Inputs. The same Context supplies Ready and admission.
resident_finite gives the literal actual prefix equation. Its returned
operation state is retained by the actual children continuation. The Mu
case obtains the same available input and probe heap. resident_rebuild
forces done at that heap. Neither case needs an additional local producer.
The node-demand case and recursive bind inversion establish real memo
fault provenance. An arbitrary observation constructor would not suffice.

The next 34-line plan and 34-line public header have twelve direct source
ranges. Its unchanged historical LocalFaults plan adds eleven sources and
seventeen ranges. Their union has seventeen live repository paths. The
pending implementation and check cues remain historical. An additive
150-total-line stop, official compiled dependency, complete source reviews
and a separate activation constrain any later implementation.
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
(ROOT / 'lean/notes-current-outer-local-faults.md').write_text(note)
print('Updated nine documents and focused note. All prior text remains.')
