import datetime
import json
from pathlib import Path
from zoneinfo import ZoneInfo

ROOT = Path('/home/tritlo/Code/mcfta')
HERE = Path(__file__).resolve().parent
result = json.loads((HERE / 'checkpoint-validation.json').read_text())
proof = result['proof_commit'][:8]
now = datetime.datetime.now(ZoneInfo('Europe/Stockholm')).strftime('%Y-%m-%d %H:%M %Z')
public = result['new_public_pairs']
constructed = result['constructed_pairs']
groups = result['groups']
entries = result['component_entries']
section = f'''## Current Parent origins and finite positive continuation chains

Updated: {now}. Proof checkpoint is `{proof}`.
Starting local checkpoint is `1145bcd0`. Main source remains `c0cc8a05`.
Read `lean/notes-current-parent-native-lineage.md` for exact boundaries.

The actual Parent worker now retains indexed complete source rows and exact
unselected continuation children. Literal local returns derive intermediate
physical facts. Both raw and checked rejection derive the Empty sentinel.
Raw rejection needs no input child availability. Initial raw guard footprints
and successful worker equations remain explicit. No future row law is supplied.

A fixed-index positive continuation relation is now well-founded. Each next
anchor is the exact preserved child of a positive linked row. Reconstructed
results can differ arbitrarily from their anchors. Final anchor mass plus
chain length is at most initial anchor mass. Such a chain cannot be infinite.
This conditional result needs no initial-source occurrence map.

Actual outer execution still needs a producer for those consecutive chain
steps. It first dispatches the reconstructed node. A later Parent uses that
node's row child at its actual slot. Source-built evidence proves that an
enclosing guard footprint does not imply the nested row guard footprint.
Other indexes, plain rows, sibling work and native reconstruction remain.
This is a proof boundary, not a new Haskell defect or an infinite execution.

Full Audit passes 3223 jobs and 70834 checks. Two production and three
constructed strict logs are empty. All {public} public and {constructed} constructed
full pairs pass in {groups} groups with all eight settings and standard axioms.
Audit peak is 392 MiB under 4 GiB maximum/high and zero swap. Four component
manifests pin {entries} entries. Evidence is in
`lean/restart-evidence/20261018-parent-native-lineage/`.

Next derive actual consecutive anchor handoff and the needed row footprints,
or establish another well-founded global rank. General recursive completion,
all-owner separation, fresh-call bounds, recursive language preservation,
used-writer alignment, repeated convergence and public Haskell correspondence
remain open. The strongest complete finite ordinary outer domain is unchanged.
No Haskell patch is added. Field-pool repair b9219b9e remains fixed in c0cc8a05.
Keep the FINDINGS repair registry first. The full-library goal stays active.
Publication awaits the existing direct approval. No push is attempted.

'''
anchor = '## Current selected local row origins and immediate descent\n'
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
Actual Parent now derives indexed full-row origins through its literal local
worker and checked construction. Both rejection paths derive Empty. A fixed
positive continuation chain strictly decreases mass and cannot be infinite.
Its consecutive exact anchors remain explicit. Actual full outer execution
still needs that chain producer. Source-built coherent nested guards prove
that an enclosing footprint is not hereditary. This is not a Haskell defect.
General recursive completion, fresh-call bounds, all-owner separation,
recursive language preservation, used-writer alignment, convergence and
full public Haskell correspondence remain open. Full Audit passes 3223 jobs
and 70834 checks. No Haskell patch or new production defect is added.
Field-pool repair `b9219b9e` remains fixed in `c0cc8a05`. Read
`lean/notes-current-parent-native-lineage.md`. Keep this registry first.
Record each later repair with failure, executable reproducer, paths, commit,
checks and upstream status. Preserve every earlier repair entry below.

'''
path.write_text(text.replace(registry, registry + entry, 1))
path = ROOT / 'lean/notes-proof-status-20261017.md'
text = path.read_text()
assert 'Checked at proof checkpoint `479741b4`.' in text
text = text.replace('Checked at proof checkpoint `479741b4`.',
                    'Checked at proof checkpoint `' + proof + '`.', 1)
text = text.replace('[the current checkpoint](notes-current-selected-local-lineage.md).',
                    '[the earlier checkpoint](notes-current-selected-local-lineage.md).', 1)
anchor = '## Strongest current claim in plain technical English\n'
paragraph = '''Actual Parent construction now retains the local indexed row relation or
returns the Empty sentinel. A fixed positive continuation chain is
well-founded even when intermediate containing nodes are reconstructed.
Its next anchor must be the exact retained child. The full outer worker
still needs a producer for those exact consecutive steps and footprints.
A source-built closed example proves that guard footprints are not
hereditary over nested rows. No general recursive domain is enlarged.
Read [the current checkpoint](notes-current-parent-native-lineage.md).

'''
assert text.count(anchor) == 1
path.write_text(text.replace(anchor, paragraph + anchor, 1))
note = f'''# Parent row origins and finite positive continuation chains

Updated {now}. Proof checkpoint: `{proof}`.
Starting local checkpoint: `1145bcd0`. Main source: `c0cc8a05`.
This is local proof progress. The full-library goal remains active.

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
explicit unions in every descendant.

These are separate implementation-model results. The family of intended
public contracts and complete Haskell correspondence remain the target.
Read `notes-proof-status-20261017.md` for that target and its support rule.
A support predicate must concern initial inputs and resource limits. It
must not assume successful completion.

## Actual Parent construction

ActualParentRowOrigins.reject_children derives exactly [Empty] from initial
Good. Input child availability is not needed. build_children uses the actual
checked constructor and initial physical facts to derive either its exact
input children or [Empty]. It needs no complete semantic inventory.

The edge theorem handles the literal Parent worker. The live field lookup
and actual local return derive the reached physical facts and equality
readiness. Accepted construction retains those exact children. Rejected
construction returns Empty, which has no surviving row. The conclusion
retains the complete indexed source row and its exact unselected child.
Original raw footprints, initial physical facts and the successful call
equation remain explicit. No supplied Root, compiler absence, future semantic
read, desired output relation or future child completion is required.

The constructed live Parent fixture changes one child while preserving its
positive row's exact recursive continuation. It invokes the production edge
theorem and Link.positive. Another fixture executes both rejection branches
with zero lower-worker fuels. Raw contradiction skips a proven unavailable
input child. Checked rejection follows a live own guard and contradictory
inherited input. Both give the actual Top sentinel with one Empty child.

## Conditional finite chains

PositionalOriginChain.Below selects a positive row of a result linked to an
explicit anchor. Its next anchor is exactly that row's retained child at
the fixed child index. Result values can be arbitrary reconstructions.
Each step strictly decreases complete structural mass between anchors.
The relation is well-founded. Final anchor mass plus chain length is at most
initial anchor mass. Positive value mass excludes an infinite such chain.
This conditional argument needs no initial-source occurrence map.

The constructed chain fixture builds its initial source and physical facts.
Actual Required preparation and two class edits derive the Link. It creates
the positive chain witness and invokes mass decrease, a one-step budget and
well-foundedness. It does not assume a future Link as a public premise.

## Remaining full-execution obligation

The actual worker first dispatches a Parent's reconstructed child. A later
ordinary body runs its selected row's own Parent before it walks that row's
children. Exact anchor handoff therefore crosses those actual calls. Fixed
(1,1) has compatible indexes. Each next row still needs its own footprint.

A separate source-built closed example has a plain enclosing row and a
positive nested row with one coherent class [0]=[1]. The enclosing footprint
holds. The nested row fails the (1,1) footprint because [1] is an ancestor
of [1,1]. Thus footprint inheritance cannot be assumed. This is a checked
input-domain obstruction. It is not an infinite trace or a Haskell defect.

Construct a producer for actual consecutive chain steps, including positive
fields, footprints, slots, earlier prefixes and physical keys. Handle other
child indexes, plain phases and sibling work. Complete native used-binder
and earlier-writer transport. Derive all-owner separation and a finite
fresh-call bound, or supply another global well-founded measure. Complete
recursive language preservation, repeated convergence, public adapters and
Haskell correspondence. The strongest complete ordinary outer domain is
unchanged. The proof counts give no completion percentage or time estimate.

## Verification and preservation

Full Audit passes 3223 jobs and 70834 dependency checks. Only the unchanged
ClosedCompletion unused-variable warning remains. Two production and three
constructed strict logs have exactly zero bytes. All {public} public and
{constructed} constructed pairs have full signatures, proofs and axiom reports in
{groups} groups. All eight required settings are enabled. Only standard axioms
occur. Effective maximum/high memory limits are 4 GiB. Swap maximum is zero.
The Audit peak is 392 MiB. Four component manifests pin {entries} entries.
All numbered drafts, warnings, failures and raw output files remain present.
Evidence is in `restart-evidence/20261018-parent-native-lineage/`.

All 26150 starting files remain present. All 3220 older non-Audit Lean sources,
242 Haskell files and 206 active-package files retain their bytes. Two stashes
and three other worktrees retain their metadata. Audit only adds two imports.
The preservation report checks 135 frozen module manifests and 980 module
entries. Root FINDINGS retains every earlier repair entry. No Haskell patch
or new production defect is added. Field-pool repair b9219b9e remains fixed
in main c0cc8a05. Publication awaits the existing direct approval.
No push is attempted or retried.
'''
(ROOT / 'lean/notes-current-parent-native-lineage.md').write_text(note)
print(json.dumps({'proof_commit': proof, 'updated_at': now, 'authority_documents': 8}))
