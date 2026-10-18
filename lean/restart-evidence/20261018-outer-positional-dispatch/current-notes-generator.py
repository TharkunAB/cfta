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
section = f'''## Current outer memo origins and exact indexed dispatch

Updated: {now}. Proof checkpoint is `{proof}`.
Starting local checkpoint is `61c6891e`. Main source remains `c0cc8a05`.
Read `lean/notes-current-outer-positional-dispatch.md` for exact boundaries.

Actual cold outer edge calls now derive the indexed Parent relation and
store it at their exact evaluating handle. Warm hits recover the actual
returned cell and its complete captured request. Ready equality identities
and coherent resident edge identity derive request equality. Initial empty
tables need no supplied result law. Actual completed node calls and unfinished
prefixes preserve the memo-origin invariant from those initial tables.

The literal indexed walk now exposes its exact earlier sibling calls,
inherited descent, selected node call, returned slot, suffix and reached
prefix. Actual Parent and live walk calls compose this dispatch with the
indexed origin. A positive row of that dispatched input has an exact
continuation child below its explicit source anchor in structural mass.
Source footprints, positivity and successful worker equations stay explicit.
This is one actual scheduled step. General consecutive chains remain open.

A checked raw guard example refutes unrestricted closure of effective-own
footprints under conjunction. Its first input is also checked rejected at
arity two. It is not an accepted-input counterexample or a Haskell defect.
Actual global footprint producers and mixed-index progress remain open.

Full Audit passes 3225 jobs and 70857 checks. Two production and three
constructed strict logs are empty. All {public} public and {constructed} constructed
full pairs pass in {groups} groups with all eight settings and standard axioms.
Audit peak is 396 MiB under 4 GiB maximum/high and zero swap. Four component
manifests pin {entries} entries. Evidence is in
`lean/restart-evidence/20261018-outer-positional-dispatch/`.

Next derive consecutive actual anchor steps with their needed footprints,
or another global well-founded measure. Handle other indexes, plain rows,
sibling work and native earlier writers. General recursive completion,
all-owner separation, fresh-call bounds, recursive language preservation,
used-writer alignment, repeated convergence and public Haskell correspondence
remain open. The strongest complete ordinary outer domain is unchanged.
No Haskell patch is added. Field-pool repair b9219b9e remains fixed in c0cc8a05.
Keep FINDINGS first. The full-library goal stays active. Publication awaits
the existing direct approval. No push is attempted or retried.

'''
anchor = '## Current Parent origins and finite positive continuation chains\n'
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
Cold and warm outer edge calls now derive indexed full-row origins for their
actual captured requests. Initial empty tables and actual completed calls
or unfinished prefixes produce the memo invariant. Literal walks derive the
exact selected source slot, inherited descent, node call, prefix and suffix.
A positive row of that dispatched input supplies a strict source-anchor
continuation step. General consecutive execution and global progress remain
open. A checked raw accessor footprint fails conjunction closure, but the
same witness proves rejection of its first checked input. No accepted-input
counterexample or Haskell defect is claimed. Full Audit passes 3225 jobs and
70857 checks. No Haskell patch or new production defect is added.
Field-pool repair `b9219b9e` remains fixed in `c0cc8a05`. Read
`lean/notes-current-outer-positional-dispatch.md`. Keep this registry first.
Record each later repair with failure, executable reproducer, paths, commit,
checks and upstream status. Preserve every earlier repair entry below.

'''
path.write_text(text.replace(registry, registry + entry, 1))
path = ROOT / 'lean/notes-proof-status-20261017.md'
text = path.read_text()
assert 'Checked at proof checkpoint `e1b8b58e`.' in text
text = text.replace('Checked at proof checkpoint `e1b8b58e`.',
                    'Checked at proof checkpoint `' + proof + '`.', 1)
text = text.replace('[the current checkpoint](notes-current-parent-native-lineage.md).',
                    '[the earlier checkpoint](notes-current-parent-native-lineage.md).', 1)
anchor = '## Strongest current claim in plain technical English\n'
paragraph = '''Actual cold and warm outer edge calls now retain indexed Parent origins
for their exact captured request. Empty initial tables, completed node calls
and unfinished prefixes produce that memo invariant. Literal walks identify
the exact dispatched value, inherited descent, earlier siblings and suffix.
A positive row of that input supplies a strict source-anchor continuation
step under the original raw footprint. A general consecutive execution
producer and global progress remain open. The checked raw conjunction
counterexample has a rejected first input. No accepted-input closure claim
or Haskell defect follows. Read
[the current checkpoint](notes-current-outer-positional-dispatch.md).

'''
assert text.count(anchor) == 1
path.write_text(text.replace(anchor, paragraph + anchor, 1))
note = f'''# Outer memo origins and exact indexed dispatch

Updated {now}. Proof checkpoint: `{proof}`.
Starting local checkpoint: `61c6891e`. Main source: `c0cc8a05`.
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
explicit unions in every descendant.

These are separate implementation-model results. Complete public contracts
and Haskell correspondence remain the target. The full-library support rule
must concern initial inputs and resource limits. It must not assume success.
Read `notes-proof-status-20261017.md` for that target and the remaining work.

## Actual outer result cells

OuterPositionalOrigins.EdgeLink retains the Parent indexed row relation
at every present input/output child slot under that source guard's footprint.
Origins records EdgeLink in each actual returned edge cell. Empty initial
tables need no prior result-origin premise. A cold call derives its relation
from the literal Parent call and initial physical facts. It finishes only
the actual evaluating handle. A warm call recovers the real returned cell.
Canonical ready equality identities and coherent resident edge identity
identify its complete captured request with the queried request. Numeric
key equality alone is not used as complete request equality.

The actual node/row/child induction retains Origins through earlier successful
calls. Existing physical and guard-heap producers supply each intermediate
state. Mu reconstruction and raw rebuilding leave outer edge tables unchanged.
The public node_done and reached laws produce the invariant for completed
node calls and unfinished prefixes. Initial Good, ready operands, the causal
Plain heap and initial memo provenance remain explicit. No future row law,
future child completion or completed call graph is supplied.

The cold/warm fixture builds the initial source and resident parent row.
It derives fresh caller Good, readiness, probe facts, causal heap and empty
Origins. It executes the cold outer call. Actual effects derive the next
call's inputs. The warm call has all eleven execution bounds zero and returns
the same result and full caller at handle zero. Both production edge_call
applications retain the indexed positive row and its exact recursive child.

## Exact actual child dispatch

OuterPositionalDispatch.walk_indexed starts from a literal completed walk.
It returns the actual earlier sibling walk, selected node call, inherited
descend operation, selected output slot and later suffix. It retains the
full caller states and exact fuel relation. Its reached prefix enters that
same node call. No graph or intended future schedule is an input.

edge_dispatch combines an actual cold or warm edge call with its live
inherited prefix and literal walk. It derives EdgeLink from initial facts.
A positive row of the exact dispatched input retains a child below the
explicit source anchor in structural mass. The actual reached prefix starts
at rows and passes through Parent, inherited combination and the live walk.
The dispatched containing node is not equated with the smaller continuation.
Original source footprints, positive fields and successful equations remain
premises. This theorem proves one actual scheduled step. It does not identify
all requests with consecutive Below steps or prove successful completion.

The dispatch fixture constructs a finite equal-leaf source with a positive
pair child. It derives initial physical facts and Origins, executes Parent
and the walk, and invokes edge_dispatch for the exact selected node call.

## Guard-footprint boundary and remaining work

The review checks an unrestricted guard-algebra counterexample. Two Cached
stored fields have effective own footprints at (1,1). One accessor returns
contradiction and hides a stored class. Their actual conjunction has an
unsupported positive residual, so the accessor falls back to the stored
field. It exposes one coherent class [0]=[1], which violates that footprint.
The same checked witness proves accepted first 2 is false. No native Trace
or accepted public execution is constructed. No accepted-input closure
counterexample or closure theorem is asserted. This is not a Haskell defect.

Derive all needed guard footprints from actual valid inputs and generated
rows. Do not assume that an accessor-only predicate is closed under raw
conjunction, or that an enclosing guard implies its nested row guard.
Produce consecutive actual anchor steps. Handle mixed indexes, plain phases
and sibling work. Complete native used-binder and earlier-writer transport.
Prove all-owner separation and a finite fresh-call bound, or provide a global
well-founded measure. Complete recursive outer language preservation,
repeated convergence, concrete adapters and Haskell correspondence.
The complete ordinary outer domain is unchanged. Counts give no completion
percentage or time estimate.

## Verification and preservation

Full Audit passes 3225 jobs and 70857 dependency checks. Only the unchanged
ClosedCompletion unused-variable warning remains. Two production and three
constructed strict logs have exactly zero bytes. All {public} public and
{constructed} constructed pairs have complete signatures, proofs and axiom reports
in {groups} groups. All eight required options are enabled. Only standard axioms
occur. Effective maximum/high memory limits are 4 GiB. Swap maximum is zero.
The Audit peak is 396 MiB. Four component manifests pin {entries} entries.
All numbered drafts and raw output remain present. Evidence is in
`restart-evidence/20261018-outer-positional-dispatch/`.

All 26300 starting files remain present. All 3222 older non-Audit Lean sources,
242 Haskell files and 206 active-package files retain their bytes. Two stashes
and three other worktrees retain their metadata. Audit only adds two imports.
The preservation report checks 136 frozen manifests and 982 module entries.
Root FINDINGS retains every earlier repair entry. No Haskell patch or new
production defect is added. Field-pool repair b9219b9e remains fixed in main
c0cc8a05. Publication awaits the existing direct approval. No push is attempted.
'''
(ROOT / 'lean/notes-current-outer-positional-dispatch.md').write_text(note)
print(json.dumps({'proof_commit': proof, 'updated_at': now, 'authority_documents': 8}))
