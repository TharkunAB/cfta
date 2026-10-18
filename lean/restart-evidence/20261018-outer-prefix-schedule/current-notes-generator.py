import datetime
import json
from pathlib import Path
from zoneinfo import ZoneInfo

ROOT = Path('/home/tritlo/Code/mcfta')
HERE = Path(__file__).resolve().parent
checked = json.loads((HERE / 'checkpoint-validation.json').read_text())
proof = checked['proof_commit'][:8]
start = (HERE / 'starting-head.txt').read_text().strip()[:8]
now = datetime.datetime.now(ZoneInfo('Europe/Stockholm')).strftime('%Y-%m-%d %H:%M %Z')
body = (HERE / 'current-body.txt').read_text()
validation = f"""Full Audit passes {checked['audit_jobs']} jobs and {checked['audit_dependency_checks']} checks.
Three production and two constructed strict logs are empty. All
{checked['new_public_pairs']} public, {checked['constructed_pairs']} constructed and {checked['private_claim_pairs']} private statement pairs pass in {checked['groups']} groups.
The constructed pairs cover two actual calls and one pure schedule example.
All eight settings and standard axioms pass. Audit peak is
{checked['audit_peak_MiB']} MiB under 4 GiB maximum/high and zero swap.
Four selected component manifests pin {checked['component_entries']} entries. Evidence is in
`lean/restart-evidence/20261018-outer-prefix-schedule/`.
"""
remaining = """General recursive completion, all-owner collision exclusion, fresh-call
bounds, lower-worker failure classification, equality-operation accounting,
used-writer alignment, repeated convergence and public Haskell correspondence
remain open. The strongest complete ordinary outer domain is unchanged.
No Haskell patch or new production defect is added. Field-pool repair
b9219b9e remains fixed in c0cc8a05. Keep FINDINGS first. The full-library
goal stays active. Publication awaits the existing direct approval.
No push is attempted or retried.
"""
section = f"""## Current semantic and fuel bounds at unfinished outer prefixes

Updated: {now}. Proof checkpoint is `{proof}`.
Starting local checkpoint is `{start}`. Main source remains `c0cc8a05`.
Read `lean/notes-current-outer-prefix-schedule.md` for exact boundaries.

{body}
{validation}
{remaining}
"""
anchor = '## Current recursive outer correctness at successful returns\n'
for name in ['NEXT-PROMPT.md', 'HANDOFF.md', 'lean/README.md', 'lean/SYSTEM.md',
             'lean/API-COVERAGE.md', 'lean/COVERAGE.md']:
    path = ROOT / name
    text = path.read_text()
    assert text.count(anchor) == 1 and section.splitlines()[0] not in text
    path.write_text(text.replace(anchor, section + anchor, 1))
path = ROOT / 'FINDINGS.md'
text = path.read_text()
registry = '## Haskell fix handoff for external work\n\n'
assert text.count(registry) == 1
entry = f"""Current proof update: {now}. Proof checkpoint is `{proof}`.
Actual unfinished outer phase prefixes now derive full semantic Context,
Post, Frame, physical bounds and guard carriers from initial facts. Exact
seed traces also bound each reached lower-fuel ceiling by its initial
ceiling. An actual node-busy failure derives these facts at its exact
fault caller and identifies the complete evaluating request. This does
not exclude busy or cover interior states of failing lower instructions.
Equality-operation and host Int adequacy bounds remain separate obligations.
Full Audit passes {checked['audit_jobs']} jobs and {checked['audit_dependency_checks']} checks.
No Haskell patch or new executable defect is added. Field-pool repair
`b9219b9e` remains fixed in `c0cc8a05`. Read
`lean/notes-current-outer-prefix-schedule.md`. Keep this registry first.
Record each later repair with failure, executable reproducer, paths, commit,
checks and upstream status. Preserve every earlier entry below.

"""
path.write_text(text.replace(registry, registry + entry, 1))
path = ROOT / 'lean/notes-proof-status-20261017.md'
text = path.read_text()
assert 'Checked at proof checkpoint `fdd5c553`.' in text
text = text.replace('Checked at proof checkpoint `fdd5c553`.',
                    'Checked at proof checkpoint `' + proof + '`.', 1)
text = text.replace('[the current checkpoint](notes-current-outer-initial-schedule.md).',
                    '[the earlier checkpoint](notes-current-outer-initial-schedule.md).', 1)
paragraph = """Literal unfinished outer phase prefixes now derive semantic Post, current
Context, Frame, scheduled physical bounds, guard carriers and ready inputs
from their initial facts. Exact seed traces bound the remaining lower-fuel
ceiling without forecast monotonicity. Actual node-busy failures construct
their own dispatch prefix and derive those same facts at the fault caller.
This identifies the complete colliding request. It does not exclude the
collision or cover arbitrary interior lower-worker fault states. The whole
call need not succeed. General recursive completion remains open. Read
[the current checkpoint](notes-current-outer-prefix-schedule.md).

"""
anchor = '## Strongest current claim in plain technical English\n'
assert text.count(anchor) == 1
text = text.replace(anchor, paragraph + anchor, 1)
anchor = 'These are separate checked results for the implementation model. They do\n'
paragraph = """Every literal unfinished outer phase prefix also retains the required
semantic state and the initial scheduled allocation bounds. Its exact
phase history bounds the remaining lower-worker fuel ceiling. A reported
node-busy fault derives its own such prefix and complete colliding request.
These facts do not require success of the enclosing call.

"""
assert text.count(anchor) == 1
path.write_text(text.replace(anchor, paragraph + anchor, 1))
note = f"""# Initial semantic and fuel bounds at unfinished outer prefixes

Updated {now}. Proof checkpoint: `{proof}`.
Starting local checkpoint: `{start}`. Main source: `c0cc8a05`.
The full-library goal remains active.
Read [the overall proof status](notes-proof-status-20261017.md).

## Completed result

{body}
SourceCurrentOuterInitialFuel supplies Parent need, six phase recurrences,
the phase selector, five inclusion laws and two exact split laws. It uses
the frozen resource schedule at each predicted entry. It adds no success
or termination premise and proves no complete worker equation by itself.

SourceCurrentOuterInitialPrefix proves every actual Step case, then the
complete Reached induction. Node demand derives its captured ready owner
and semantic cache law. A row suffix composes completed edge and descendants
Posts. A walk suffix composes indexed descent and the completed node Post.
It retains the original combined payload and incremented index. The proof
derives remaining forecast containment and exact lower-fuel containment
separately. Profile containment alone would not prove the fuel inequality.

SourceCurrentOuterInitialBusy weakens initial structural node validity only
enough to apply the literal busy-failure dispatch producer. The prefix proof
then derives the actual current semantic Context. That context provides
valid key links and ready captured inputs. Inherited identity and resident
value identity injectivity derive complete request equality. The theorem
keeps the exact fault caller. It does not assume an initial idle table.

The actual prefix example constructs two ordinary source rows with two
constrained recursive Mu children in each row. A root call at outer fuel 4,
budget 0 and all nine lower fuels 0 completes the first row, the second
Parent and an earlier second-row child. Its walk then exhausts outer fuel.
The literal failure propagates to the original raw nodeCall. Its own initial
history, Context, Frame, Fits, carrier and readiness derive full semantic
Post and scheduled bounds at that same failure caller. The input is outside
every finite Plain Cap. Mathematical width is computed from initial Room.
No nonempty accepted finite language or practical host-width bound is claimed.

A second example explicitly demands the root request again while its own
reached body remains active. It applies the busy theorem to that separate
call. It asserts no busy failure of the fresh-root recursive traversal.
This checks that semantic Context and an evaluating owner can coexist.
A pure fuel example separately checks initial, nested and later-row Parent
needs at three exact scheduled seeds. That example is not worker execution.

## Next proof target

Construct the actual failed-call prefix that reaches the first failing outer
edge or lower Parent. Use the current prefix theorem at that reached entry.
The exact seed trace bounds its local Parent need by the initial nine-fuel
ceiling. Together with initial scheduled Room and the resident Parent
completion theorem, sufficient lower fuels can rule out lower exhaustion.
Do not infer local fuel bounds from a larger padded profile.

Retain the distinction between outer phase entries and interior lower
instruction states. Extend failure classification where needed before
claiming a full all-outcome semantic invariant. Keep reference, inherited
and binder failures explicit until their initial domain excludes them.

Then exclude every active memo-owner collision and bound fresh recursive
requests, or give a well-founded rank. The semantic invariant allows
evaluating cells and therefore does not imply notBusy. Source-anchor descent
still needs consecutive actual anchors and footprints. Parent can construct
new values. A supplied outer-fuel schedule does not prove sufficient outer fuel.

Separate equality-operation accounting, host Int adequacy, used-binder writer
alignment, repeated convergence and public Haskell correspondence remain
open. The completed ordinary outer domain and exact-size enumeration claim
are unchanged. No new executable Haskell defect is established.

## Verification and preservation

{validation}
The selected Busy strict log is direct3 and has zero bytes. Its private
helpers scope typeclass variables only where needed. Earlier direct2 omit
warnings and canonical1 unused-section warnings remain as superseded
evidence. Selected canonical3 and full Audit2 add no baseline warning.

All 28005 starting files remain present. All 3255 older non-Audit Lean
sources, 242 Haskell files and 206 active-package files retain their bytes.
Two stashes and three other worktrees retain their metadata. Audit adds
only three imports. Preservation checks 146 frozen manifests and 1016
module entries. Every earlier FINDINGS repair entry remains present.

{remaining}"""
path = ROOT / 'lean/notes-current-outer-prefix-schedule.md'
assert not path.exists()
path.write_text(note)
print(json.dumps({'proof': proof, 'updated': now}))
