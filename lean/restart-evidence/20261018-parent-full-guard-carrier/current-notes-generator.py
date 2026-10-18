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
All eight settings and standard axioms pass. Audit peak is
{checked['audit_peak_MiB']} MiB under 4 GiB maximum/high and zero swap.
Six component manifests pin {checked['component_entries']} entries. Evidence is in
`lean/restart-evidence/20261018-parent-full-guard-carrier/`.
"""
remaining = """General recursive outer progress, all-owner separation, fresh-call bounds,
recursive language preservation, used-writer alignment, repeated convergence
and public Haskell correspondence remain open. The strongest complete
ordinary outer domain is unchanged. No Haskell patch or new production
defect is added. Field-pool repair b9219b9e remains fixed in c0cc8a05.
Keep FINDINGS first. The full-library goal stays active. Publication awaits
the existing direct approval. No push is attempted or retried.
"""
section = f"""## Current finite guard carriers through complete Parent

Updated: {now}. Proof checkpoint is `{proof}`.
Starting local checkpoint is `{start}`. Main source remains `c0cc8a05`.
Read `lean/notes-current-parent-full-guard-carrier.md` for exact boundaries.

{body}
{validation}
{remaining}
"""
anchor = '## Current finite guard composition through edits and classes\n'
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
Complete Classes, Local and Parent now construct finite raw guard carriers
with their original full receipts and exact returned states. A finite
initial own-record/count image supplies one common Parent carrier together
with the existing common output profile and nine-fuel replay. Raw rejection
includes its actual Top sentinel. General outer composition remains open.
The physical Profile does not bound equality-operation resources. Host Int
equality identities need a separate refinement bound. This is an existing
proof obligation; no executable failure or new runtime defect is claimed.
Full Audit passes {checked['audit_jobs']} jobs and {checked['audit_dependency_checks']} checks.
No Haskell patch is added. Field-pool repair `b9219b9e` remains fixed in
`c0cc8a05`. Read `lean/notes-current-parent-full-guard-carrier.md`.
Keep this registry first. Record each later repair with failure, executable
reproducer, paths, commit, checks and upstream status. Preserve all earlier entries.

"""
path.write_text(text.replace(registry, registry + entry, 1))
path = ROOT / 'lean/notes-proof-status-20261017.md'
text = path.read_text()
assert 'Checked at proof checkpoint `92ddd8ff`.' in text
text = text.replace('Checked at proof checkpoint `92ddd8ff`.',
                    'Checked at proof checkpoint `' + proof + '`.', 1)
text = text.replace('[the current checkpoint](notes-current-parent-guard-composition.md).',
                    '[the earlier checkpoint](notes-current-parent-guard-composition.md).', 1)
paragraph = """Finite raw guard carriers now compose through complete Classes, Local and
Parent. Exact initial own-record and count cases determine a common Parent
carrier at the same full receipt, output profile and nine-fuel replay.
No future entry or guard-range callback is supplied. The remaining outer
bridge must derive semantic Context, Frame, scheduled Fits and carriers
through rows_tail and walk_tail. Equality-operation resources need a
separate account from the physical Profile. General recursive completion
and the strongest complete outer domain are unchanged. Read
[the current checkpoint](notes-current-parent-full-guard-carrier.md).

"""
anchor = '## Strongest current claim in plain technical English\n'
assert text.count(anchor) == 1
path.write_text(text.replace(anchor, paragraph + anchor, 1))
note = f"""# Initial finite guard carriers through complete Parent

Updated {now}. Proof checkpoint: `{proof}`.
Starting local checkpoint: `{start}`. Main source: `c0cc8a05`.
The full-library goal remains active.
Read [the overall proof status](notes-proof-status-20261017.md).

## Completed supporting result

{body}
ClassesGuardAlphabet keeps the complete ClassesNumeric.Receipt. Its
preparation and selected pass are constructed from initial facts. The
actual initial ambient word and actual selected sublist enter the finite
forecast by membership proofs. Each selected case uses its exact pure
preparation profile. No unordered Scan monotonicity law is assumed.

LocalGuardAlphabet derives its actual loaded precheck and handles unchanged,
empty-child and class branches. It retains the full LocalNumeric.Receipt.
ParentGuardAlphabet handles raw rejection, live field loading, the complete
local call and actual final MkEdge. Its resident producer derives the load
and input facts. ParentUniformGuardAlphabet places that exact resident
forecast in the finite initial image. The common numeric profile and fuel
come from ParentUniformEnvelope. UniformReserved remains an initial pure
condition. The earlier computed-width theorem can supply that condition.
There is no fixed host-width or practical forecast-size claim.

The constructed checks build their own constrained recursive inputs outside
every finite Plain Cap. They derive their initial semantic and numeric
facts internally and invoke the production completion theorems. These are
actual worker equations. They do not assume returned graphs or Frames.
The full Classes example leaves its Scan outcome existential. It does not
claim a specific selected pass or native instruction count.

## Next proof target

Use the successful-return boundary for one mutual outer proof over fuel
and finite phase order. At each literal successful return, derive its graph,
strict Reads, semantic law, Post, returned Frame, scheduled Fits and carrier
from initial facts. Supply the new single-Parent producer at edge bodies.
Use the existing inherited and raw-rebuild adapters at their actual entries.
At rows_tail and walk_tail, feed each returned context, inventory and memo
bundle into the original suffix. Retain the original combined inherited
payload at a walk suffix. A descended child payload is not that suffix input.

Construct the pure initial phase schedule for Parent and non-Parent work.
The Parent-call count excludes raw reconstruction and inherited operations.
Do not assume future entry resource ranges or returned semantic contexts.
Do not add a new wrapper for prefix/descent facts already proved.
Read the source-pinned map in
`restart-evidence/20261018-parent-full-guard-carrier/outer-context-next-proof-map.md`.

The four-field physical Profile does not count the equality interner,
combination cells, descent cells or inherited payload work. These are
unbounded Nat tables in the current model. A runtime resource or host
correspondence theorem needs a separate account and an Int identity
adequacy bound. This finding does not establish a new Haskell bug.

A count from supplied outer fuel does not establish sufficient outer fuel.
General recursive progress still needs all-owner separation and a fresh-call
bound or another well-founded measure. The complete ordinary outer-pass
domain and the strongest exact-size enumeration claim are unchanged.

## Verification and preservation

{validation}
All 27601 starting files remain present. All 3247 older non-Audit Lean
sources, 242 Haskell files and 206 active-package files retain their bytes.
Two stashes and three other worktrees retain their metadata. Audit only
adds four imports. Preservation checks 144 frozen manifests and 1009
module entries. Every earlier FINDINGS repair entry remains present.

{remaining}"""
path = ROOT / 'lean/notes-current-parent-full-guard-carrier.md'
assert not path.exists()
path.write_text(note)
print(json.dumps({'proof': proof, 'updated': now}))
