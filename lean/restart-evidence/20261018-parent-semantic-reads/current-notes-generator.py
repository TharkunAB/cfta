import datetime
import json
from pathlib import Path
from zoneinfo import ZoneInfo

ROOT = Path('/home/tritlo/Code/mcfta')
HERE = Path(__file__).resolve().parent
result = json.loads((HERE / 'checkpoint-validation.json').read_text())
proof = result['proof_commit'][:8]
now = datetime.datetime.now(ZoneInfo('Europe/Stockholm')).strftime('%Y-%m-%d %H:%M %Z')
entries = result['component_entries']
section = f'''## Current semantic context at actual Parent and outer edge returns

Updated: {now}. Proof checkpoint is `{proof}`.
Starting local checkpoint is `002f0a7d`. Main source remains `c0cc8a05`.
Read `lean/notes-current-parent-semantic-reads.md` for exact boundaries.

Initial numeric Parent support now derives the full semantic receipt at
any literal successful Parent return. Uniqueness identifies the complete
edge Value, Checked state, fourth memo and Merge memo. The outer body
adapter also derives strict Reads on its supplied actual graph.

An actual successful outer edge call now derives its complete old receipt,
Post, returned Frame/Fits, language law and strict Reads from initial entry
support. The observed success excludes the initial busy alternative.
No notBusy or observed-fuel lower-bound premise is supplied. Both cold
captured-owner evaluation and warm returned cells are included.

Parent numeric completion already derives the internal precheck, Scan,
Required and class contexts and selected domains. No future class Reads,
whole-forest closure, finite ordinary domain or finite Cap is added.
Initial full semantic Context, Frame/Fits, warm laws and pure numeric
reservation remain explicit. Weak physical Good does not imply these laws.

This supplies the semantic endpoint for one actual rows_edge summary.
The general induction across rows_tail and walk_tail remains open.
Mu cleanup already returns at the unchanged complete caller. It is not
the first missing Frame transition. A future-entry range callback does
not establish a genuinely initial general recursive resource schedule.

Full Audit passes 3234 jobs and 70904 checks. Two production and one
constructed strict logs are empty. All 3 public and 1 constructed full
pairs pass in 3 groups with all eight settings and standard axioms.
Audit peak is {result['audit_peak_MiB']} MiB under 4 GiB maximum/high and zero swap.
Four component manifests pin {entries} entries. Evidence is in
`lean/restart-evidence/20261018-parent-semantic-reads/`.

General recursive progress, all-owner separation, fresh-call bounds,
recursive language preservation, used-writer alignment, repeated convergence
and public Haskell correspondence remain open. The strongest complete
ordinary outer domain is unchanged. No Haskell patch or new production
defect is added. Field-pool repair b9219b9e remains fixed in c0cc8a05.
Keep FINDINGS first. The full-library goal stays active. Publication awaits
the existing direct approval. No push is attempted or retried.

'''
anchor = '## Current semantic reads at actual target and class returns\n'
for name in ['NEXT-PROMPT.md', 'HANDOFF.md', 'lean/README.md', 'lean/SYSTEM.md',
             'lean/API-COVERAGE.md', 'lean/COVERAGE.md']:
    path = ROOT / name
    text = path.read_text()
    assert section.splitlines()[0] not in text and text.count(anchor) == 1
    path.write_text(text.replace(anchor, section + anchor, 1))
path = ROOT / 'FINDINGS.md'
text = path.read_text()
registry = '## Haskell fix handoff for external work\n\n'
assert text.count(registry) == 1
entry = f'''Current proof update: {now}. Proof checkpoint is `{proof}`.
Initial numeric support now derives complete Parent and outer edge receipts
at actual returned endpoints. Parent alignment identifies the edge, Checked,
fourth and Merge components. Actual body graphs retain their own strict Reads.
Actual outer edge success excludes busy without a notBusy premise and
derives the returned full Frame/Post. Internal class contexts follow from
the existing Parent producer. No finite ordinary domain, finite Cap or
future semantic read law is added. Initial semantic Context/Frame/Fits and
pure reservations remain explicit. General outer summaries and recursive
progress remain open. Full Audit passes 3234 jobs and 70904 checks.
No Haskell patch or new production defect is added. Field-pool repair
`b9219b9e` remains fixed in `c0cc8a05`. Read
`lean/notes-current-parent-semantic-reads.md`. Keep this registry first.
Record each later repair with failure, executable reproducer, paths, commit,
checks and upstream status. Preserve every earlier repair entry below.

'''
path.write_text(text.replace(registry, registry + entry, 1))
path = ROOT / 'lean/notes-proof-status-20261017.md'
text = path.read_text()
assert 'Checked at proof checkpoint `af9a413d`.' in text
text = text.replace('Checked at proof checkpoint `af9a413d`.',
                    'Checked at proof checkpoint `' + proof + '`.', 1)
text = text.replace('[the current checkpoint](notes-current-actual-semantic-reads.md).',
                    '[the earlier checkpoint](notes-current-actual-semantic-reads.md).', 1)
anchor = '## Strongest current claim in plain technical English\n'
paragraph = '''Initial numeric Parent support now derives semantic receipts at literal
successful Parent and outer edge-body returns. All four Parent components
align. An actual outer edge success also derives its complete receipt,
Frame/Fits and Post without a notBusy or fuel lower-bound premise. The
existing Parent producer derives its internal class contexts and domains.
This supplies the endpoint for an actual rows_edge summary from supported
initial entry facts. General rows_tail/walk_tail semantic transport and
initial recursive resource schedules remain open. Mu cleanup is already
unchanged. No finite ordinary domain or finite Cap is added. General
recursive completion and the strongest complete outer domain are unchanged.
Read [the current checkpoint](notes-current-parent-semantic-reads.md).

'''
assert text.count(anchor) == 1
path.write_text(text.replace(anchor, paragraph + anchor, 1))
note = f'''# Semantic context at actual Parent and outer edge returns

Updated {now}. Proof checkpoint: `{proof}`.
Starting local checkpoint: `002f0a7d`. Main source: `c0cc8a05`.
This is verified progress. The full-library goal remains active.

## Strongest complete statement

For a validated finite explicit graph, including cycles, the checked model
lists exactly the distinct accepted finite terms at each node-count size.
Its counts are correct. Rank and unrank follow the specified order and are
inverses at valid indexes. Correct finite yes/no guard replies and the stated
ordering laws give these successful results. Finite unknown replies can
instead return an error. Supported closed resident Original operands have
exact recursive native intersection semantics. Initial resources construct
those executions. A complete finite ordinary constrained outer pass preserves
the full guarded language. That outer domain excludes Mu, references and
explicit unions in every descendant. These are implementation-model results.
The intended public contracts and concrete Haskell correspondence remain
the target. Read `notes-proof-status-20261017.md` for the whole-library scope.

## Actual Parent and body returns

ActualParentSemanticReads.parent applies ParentNumeric.complete from initial
Context, Frame/Fits, live inputs and the pure initial Parent reservation.
It constructs its own receipt. Successful-return uniqueness identifies all
four returned components with a literal successful Parent call: full edge
Value, Checked state, fourth memo and Merge memo. The receipt includes the
actual graph, strict Reads, physical stores, language law, Post, Frame/Fits
and replay. The observed nine fuels need no comparison with the forecast.

edge_body applies the resident numeric producer to an actual completed
outer EdgeBody graph. Its worker completion theorem supplies a literal
Parent equation. Full outer worker uniqueness aligns the result and entire
caller. Proof irrelevance then retains strict Reads on the supplied actual
graph. This consumes a completed graph, not an unfinished prefix.

## Actual outer edge return

ActualEdgeCallSemanticReads.edge_call uses the initial EdgeCall reservation
for the exact captured owner. It applies EdgeCallNumeric.finite_or_busy.
The supplied literal success excludes the initial busy failure internally.
The constructed return agrees on the result and entire caller through
edgeCall_done_unique. Its complete receipt therefore supplies semantic
Post, full Frame/Fits, strict Reads, warm cache laws and the candidate's
inherited-conditioned language law at that exact observed endpoint.
No notBusy or observed-fuel lower-bound premise is supplied. Cold owner
evaluation and warm returned hits remain included. Initial warm cells need
Sound, whose returned entries already contain their semantic result laws.
Weak physical residency alone does not provide those laws.

## Actual entry boundary

The first missing summary in the physical outer prefix induction was
rows_edge. The new adapter supplies its semantic destination facts from
supported initial entry facts. Existing Parent/local numeric completion
already derives the internal precheck, Scan, Required and class contexts,
selected domains and historical target receipts. No future class Reads,
whole-forest closure, finite ordinary domain or finite Cap is introduced.

Mu reconstruction already returns exact cleanup at the unchanged complete
caller. Demand operations retain Checked, Merge and fourth components.
Ordinary raw rebuild numeric producers retain full Frame and updated Fits.
The remaining general summary includes completed earlier ordinary nodes
at walk_tail and the combined work at rows_tail. A complete proof must
derive a genuinely initial resource schedule and retain returned owner
laws. A callback that assumes capacity at every future entry does not
discharge that obligation.

## Constructed integration

The source-built integration constructs a resident outer row with two
constrained recursive children. Both children are selected by the live own
class at paths [0] and [1]. The actual precheck enters its classes branch.
The selected recursive value is outside every finite Cap. Initial Context,
Frame/Fits and pure reservations are derived internally. Nine independently
increased computed fuels F through F+8 supply the observed Parent and body
returns. The two completions start from the same initial caller. Both
adapters produce full receipts at those exact endpoints. The witness proves
the classes precheck branch. It asserts no particular Scan-kept class or
positive final constructor. This is computed numeric completion and replay
alignment. It is not an independent small-fuel evaluation or a public
Haskell pipeline execution.

## Remaining work

General outer semantic prefix transport, recursive progress, all-owner
separation, fresh-call bounds, recursive outer language preservation,
used-writer alignment, repeated convergence, concrete adapters and public
Haskell correspondence remain open. The strongest complete ordinary outer
domain is unchanged. Proof totals do not give a completion percentage or
reliable completion date.

## Verification and preservation

Full Audit passes 3234 jobs and 70904 dependency checks. Only the unchanged
ClosedCompletion warning remains. Two production and one constructed strict
logs are zero bytes. All 3 public and 1 constructed pairs have complete
signatures, proofs and standard axiom reports in 3 groups. All eight required
options are enabled. Effective maximum/high memory limits are 4 GiB.
Swap maximum is zero. Audit peak is {result['audit_peak_MiB']} MiB. Four component
manifests pin {entries} entries. All attempts and raw output remain present
in `restart-evidence/20261018-parent-semantic-reads/`.

All 26889 starting files remain present. All 3231 older non-Audit Lean sources,
242 Haskell files and 206 active-package files retain their bytes. Two stashes
and three other worktrees retain their metadata. Audit only adds two imports.
The preservation report checks 140 frozen manifests and 991 module entries.
Root FINDINGS retains every earlier repair entry. No Haskell patch or new
production defect is added. Field-pool repair b9219b9e remains fixed in main
c0cc8a05. Publication awaits the existing direct approval. No push is attempted.
'''
path = ROOT / 'lean/notes-current-parent-semantic-reads.md'
assert not path.exists()
path.write_text(note)
print(json.dumps({'proof': proof, 'updated': now, 'new_note': str(path.relative_to(ROOT))}))
