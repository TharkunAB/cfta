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
Four production and three constructed strict logs are empty. All
{checked['new_public_pairs']} public and {checked['constructed_pairs']} constructed full pairs pass in {checked['groups']} groups.
The extra private pair prints the complete recursive example statement.
All eight settings and standard axioms pass. Audit peak is
{checked['audit_peak_MiB']} MiB under 4 GiB maximum/high and zero swap.
Six component manifests pin {checked['component_entries']} entries. Evidence is in
`lean/restart-evidence/20261018-outer-initial-schedule/`.
"""
remaining = """General recursive outer completion, all-owner separation, fresh-call bounds,
unfinished-prefix semantic transport, used-writer alignment, repeated
convergence and public Haskell correspondence remain open. The strongest
complete ordinary outer domain is unchanged. Recursive language preservation
is now derived at supported successful returns. No Haskell patch or new
production defect is added. Field-pool repair b9219b9e remains fixed in
c0cc8a05. Keep FINDINGS first. The full-library goal stays active.
Publication awaits the existing direct approval. No push is attempted or retried.
"""
section = f"""## Current recursive outer correctness at successful returns

Updated: {now}. Proof checkpoint is `{proof}`.
Starting local checkpoint is `{start}`. Main source remains `c0cc8a05`.
Read `lean/notes-current-outer-initial-schedule.md` for exact boundaries.

{body}
{validation}
{remaining}
"""
anchor = '## Current finite guard carriers through complete Parent\n'
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
Successful recursive outer runs now derive full semantic Reads, Post,
Frame, physical Fits and finite raw guard carriers from initial facts.
One initial scheduled Room condition covers the reached Parent calls.
Empty inherited constraints give exact language equality. Internal calls
preserve membership for terms that satisfy their inherited constraints
and never add accepted terms. General successful termination stays open.
The physical Profile does not bound equality-operation tables or host Int
identities. This is a refinement obligation, not a new executable defect.
Full Audit passes {checked['audit_jobs']} jobs and {checked['audit_dependency_checks']} checks.
No Haskell patch is added. Field-pool repair `b9219b9e` remains fixed in
`c0cc8a05`. Read `lean/notes-current-outer-initial-schedule.md`.
Keep this registry first. Record each later repair with failure, executable
reproducer, paths, commit, checks and upstream status. Preserve all earlier entries.

"""
path.write_text(text.replace(registry, registry + entry, 1))
path = ROOT / 'lean/notes-proof-status-20261017.md'
text = path.read_text()
assert 'Checked at proof checkpoint `651cb065`.' in text
text = text.replace('Checked at proof checkpoint `651cb065`.',
                    'Checked at proof checkpoint `' + proof + '`.', 1)
text = text.replace('[the current checkpoint](notes-current-parent-full-guard-carrier.md).',
                    '[the earlier checkpoint](notes-current-parent-full-guard-carrier.md).', 1)
paragraph = """The complete mutual outer traversal now derives semantic Reads, Post,
Frame, scheduled physical Fits and a finite raw guard carrier at every
supported successful return. One initial final-profile Room condition
covers reached Parent reservations. Each row and child suffix receives
the actual returned context. No future-result or reached-check oracle is
supplied. Initial semantic and physical facts and literal bounded success
remain explicit. General recursive completion stays open. Read
[the current checkpoint](notes-current-outer-initial-schedule.md).

"""
anchor = '## Strongest current claim in plain technical English\n'
assert text.count(anchor) == 1
text = text.replace(anchor, paragraph + anchor, 1)
anchor = 'These are separate checked results for the implementation model. They do\n'
paragraph = """For the general supported recursive outer traversal, successful runs now
derive language preservation from initial semantic and physical facts.
An internal result accepts no new terms and preserves membership for
terms that satisfy its inherited constraints. With empty inherited
constraints, the returned and input languages are exactly equal. The
proof also derives the semantic state invariant and scheduled physical
allocation bounds at that same return. It does not assume a future callee
result or semantic trace. It still assumes that this bounded run succeeds.

"""
assert text.count(anchor) == 1
path.write_text(text.replace(anchor, paragraph + anchor, 1))
note = f"""# Recursive outer correctness from initial scheduled resources

Updated {now}. Proof checkpoint: `{proof}`.
Starting local checkpoint: `{start}`. Main source: `c0cc8a05`.
The full-library goal remains active.
Read [the overall proof status](notes-proof-status-20261017.md).

## Completed result

{body}
SourceCurrentOuterInitialSchedule defines the six pure phase forecasts.
It proves profile growth and carrier retention at each phase. Its Parent
reservation theorem derives UniformReserved from the initial scheduled
Room condition. It does not replace exact predicted inputs with unordered
or larger inputs.

SourceCurrentOuterEdgeGuardAlphabet derives the full existing edge-body
and edge-call receipts at literal successful endpoints. A cold call uses
its exact captured request. A warm call uses the initial semantic cache
law. The chosen result and complete Checked, fourth and Merge components
agree. Independent inventory and memo witnesses are not identified by
worker-state equality.

SourceCurrentOuterRebuildGuardAlphabet combines full raw-rebuild receipts
with the uniform physical constructor profile and unchanged raw carrier.
The mutual traversal derives equal child counts from its actual graph.
It retains the complete stored guard through edge and node reconstruction.

SourceCurrentOuterInitialActual proves all six actual phases together.
The proof inverts the observed successful worker equation. Each smaller
successful equation is derived from that equation. The proof constructs
its own graph and strict Reads. It proves NodeLaw before installing the
completed node cell. Resident Mu reconstruction uses the initial probe
law. Warm node hits use the initial semantic cache law. A walk suffix
uses its original combined inherited payload at the incremented index.

The complete traversal example constructs two ordinary source rows with
two constrained recursive Mu children in each row. It proves the literal
nodeCall return at outer fuel 5, budget 0 and all nine lower fuels 0.
It computes sufficient mathematical width from the final scheduled
profile. It then applies the general theorem and derives exact language
equality for its own empty inherited constraints. Its recursive input is
outside every finite Plain Cap. The outer rows have no live own class.
The separate edge example exercises a live class and a subsequent warm
hit at all ten zero fuels. Neither example establishes a nonempty accepted
finite language or a practical fixed-width capacity bound.

## Next proof target

Extend initial semantic and scheduled physical facts to unfinished outer
prefixes and all outcomes. A successful-return proof cannot supply facts
at a prefix that eventually fails. Derive those prefix facts from initial
inputs rather than from the desired completed context.

Use the same exact pure phase order to compute one initial ceiling for
the nine lower fuels. Derive each reached Parent ceiling from its own
scheduled entry. Do not infer forecast monotonicity from profile order.
One supplied outer fuel bounds the possible schedule. It does not prove
that some outer fuel suffices for general recursive completion.

Then exclude collisions with every active memo owner and bound fresh
recursive requests, or give another well-founded measure. Existing source
anchor descent needs a producer for consecutive actual steps and their
footprints. Parent construction can create new values. Ordinary height
and positive counts that ignore unions do not prove global progress.

Separate equality-operation accounting and host Int identity adequacy
remain necessary for runtime correspondence. Used-binder source alignment,
repeated-pass convergence and concrete public Haskell adapters also remain
open. The complete ordinary outer domain is unchanged. It excludes Mu,
references and explicit unions in every descendant. The new result is a
larger recursive partial-correctness theorem, not a general completion theorem.

## Verification and preservation

{validation}
All 27781 starting files remain present. All 3251 older non-Audit Lean
sources, 242 Haskell files and 206 active-package files retain their bytes.
Two stashes and three other worktrees retain their metadata. Audit only
adds four imports. Preservation checks 145 frozen manifests and 1013
module entries. Every earlier FINDINGS repair entry remains present.

{remaining}"""
path = ROOT / 'lean/notes-current-outer-initial-schedule.md'
assert not path.exists()
path.write_text(note)
print(json.dumps({'proof': proof, 'updated': now}))
