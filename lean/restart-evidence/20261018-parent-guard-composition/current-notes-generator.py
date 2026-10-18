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
Seven production and five constructed strict logs are empty. All
{checked['new_public_pairs']} public and {checked['constructed_pairs']} constructed full pairs pass in {checked['groups']} groups.
All eight settings and standard axioms pass. Audit peak is
{checked['audit_peak_MiB']} MiB under 4 GiB maximum/high and zero swap.
Seven component manifests pin {checked['component_entries']} entries. Evidence is in
`lean/restart-evidence/20261018-parent-guard-composition/`.
"""
remaining = """General recursive outer progress, all-owner separation, fresh-call bounds,
recursive language preservation, used-writer alignment, repeated convergence
and public Haskell correspondence remain open. The strongest complete
ordinary outer domain is unchanged. No Haskell patch or new production
defect is added. Field-pool repair b9219b9e remains fixed in c0cc8a05.
Keep FINDINGS first. The full-library goal stays active. Publication awaits
the existing direct approval. No push is attempted or retried.
"""
section = f"""## Current finite guard composition through edits and classes

Updated: {now}. Proof checkpoint is `{proof}`.
Starting local checkpoint is `{start}`. Main source remains `c0cc8a05`.
Read `lean/notes-current-parent-guard-composition.md` for exact boundaries.

{body}
{validation}
{remaining}
"""
anchor = '## Current finite Parent envelopes and outer Parent call budgets\n'
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
Finite raw guard carriers now compose through actual Force, Leaf, complete
node edits, compiled classes and their tail-first fold and pass. Supported
recursive Head exposure is included. Preparation also constructs its own
carrier. FullClasses, Local and Parent carrier composition remains open.
Local outer constructor bounds retain full guards and physical Fits.
They still need chronological outer composition and equality-cache bounds.
General recursive progress and public Haskell correspondence remain open.
Full Audit passes {checked['audit_jobs']} jobs and {checked['audit_dependency_checks']} checks.
No Haskell patch or new production defect is added. Field-pool repair
`b9219b9e` remains fixed in `c0cc8a05`. Read
`lean/notes-current-parent-guard-composition.md`. Keep this registry first.
Record each later repair with failure, executable reproducer, paths, commit,
checks and upstream status. Preserve every earlier repair entry below.

"""
path.write_text(text.replace(registry, registry + entry, 1))
path = ROOT / 'lean/notes-proof-status-20261017.md'
text = path.read_text()
assert 'Checked at proof checkpoint `e43db322`.' in text
text = text.replace('Checked at proof checkpoint `e43db322`.',
                    'Checked at proof checkpoint `' + proof + '`.', 1)
text = text.replace('[the current checkpoint](notes-current-parent-uniform-envelope.md).',
                    '[the earlier checkpoint](notes-current-parent-uniform-envelope.md).', 1)
paragraph = """Finite raw guard carriers now accompany actual complete node edits and
class folds and passes, including supported recursive Head exposure.
Preparation returns its own carrier. FullClasses, Local and Parent still
need their carrier composition. Non-Parent constructor bounds now retain
the same carrier and physical profile at each local entry. Their whole
outer schedule and equality-cache bounds remain open. General recursive
completion and the strongest complete outer domain are unchanged. Read
[the current checkpoint](notes-current-parent-guard-composition.md).

"""
anchor = '## Strongest current claim in plain technical English\n'
assert text.count(anchor) == 1
path.write_text(text.replace(anchor, paragraph + anchor, 1))
note = f"""# Finite guard composition through edits and classes

Updated {now}. Proof checkpoint: `{proof}`.
Starting local checkpoint: `{start}`. Main source: `c0cc8a05`.
The full-library goal remains active.
Read [the overall proof status](notes-proof-status-20261017.md).

## Strongest complete claims

For a validated finite graph, the exact-size model enumerates exactly the
distinct accepted finite terms. Counts are correct. Ranking and unranking
are inverses in the specified order. Cyclic graphs are included. Correct
finite yes/no solver replies and the declared ordering laws are explicit.
An unknown solver reply can instead stop a query with an error.

The supported closed resident Original recursive intersection has exact
intersection semantics. A complete finite ordinary constrained outer pass
preserves the full guarded language. That outer-pass domain excludes Mu,
references and explicit unions in every descendant. These are separate
results for the implementation model. Public Haskell correspondence and
general recursive simplification are not complete.

## New supporting results

{body}
The node bound adds a leaf allowance and two scalar widths per trie level.
The actual row and child scans preserve their smaller returned Fits.
The public node producer proves the internal NodeComplete hypothesis.
Its recursive branch derives closedness from the supported selected edit
domain, constructs Head, then runs the ordinary phase. The exact guard
carrier is flat. It does not imply a hereditary ordinary domain.

The class producer starts its own target state. The tail-first class fold
uses each actual returned profile, alphabet, inventory and memo bundle.
The final pass also retains empty propagation and six independently larger
fuel replays. A constructed source has nested paths [0,0] and [0,1],
repeated classes, a selected closed constrained Mu and an open unselected
sibling. Its selected recursive value lies outside every finite Plain Cap.
The fixture derives its own source, semantic facts, Frame, Fits and Room.

Preparation uses complete ordered initial words. It does not assume that
Scan is monotone under unordered alphabet inclusion. Its numeric Scan
receipt aligns with the complete preparation return by worker uniqueness.
Required then preserves the same raw carrier without adding Top.

The local outer bounds derive original widths from stored mass and actual
successful child and row worker lengths. They require physical entry facts,
not a supplied replacement-width bound. The constructed raw rebuild runs
after two resident Mu cleanups and allocates exactly one new edge record.
It retains the full symbol, guard and ordered children. Descent and prefix
can change equality caches although their constructor heap stays equal.

## Next proof target

Compose PreparationGuardAlphabet with ClassGuardAlphabet through
FullClasses, Local and Parent. Enumerate the finite initial record
selections. Use the exact preparation profile and class fold count for
each selection. Align the full returned state, receipt, Frame, Fits and
alphabet. Do not assume future entry ranges or capacity callbacks.

Then compose Parent and non-Parent steps through the bounded outer phase
tree. Derive the semantic entry facts through rows_tail and walk_tail.
Account for equality-operation caches separately from physical heap fields.
A count from supplied outer fuel does not establish sufficient outer fuel.
General recursive progress needs all-owner separation and a fresh-call
bound or another well-founded measure.

## Verification and preservation

{validation}
All 27317 starting files remain present. All 3240 older non-Audit Lean
sources, 242 Haskell files and 206 active-package files retain their bytes.
Two stashes and three other worktrees retain their metadata. Audit only
adds seven imports. Preservation checks 143 frozen manifests and 1005
module entries. Every earlier FINDINGS repair entry remains present.

{remaining}"""
path = ROOT / 'lean/notes-current-parent-guard-composition.md'
assert not path.exists()
path.write_text(note)
print(json.dumps({'proof': proof, 'updated': now}))
