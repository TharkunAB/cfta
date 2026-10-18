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
section = f'''## Current selected class dispatch and literal native leaf events

Updated: {now}. Proof checkpoint is `{proof}`.
Starting local checkpoint is `6ce48bcd`. Main source remains `c0cc8a05`.
Read `lean/notes-current-selected-edit-events.md` for exact boundaries.

Every present slot of an actual coherent active class now supplies its
exact input, earlier siblings, selected call and later siblings. The slot
is unchanged, executes its whole-slot leaf, or edits below it. A whole-slot
callback retains the exact complete original path. No unselected guard
footprint or future semantic read law is supplied.

Actual shared leaves derive their target force, native intersection request,
intermediate state and literal final advance. A target hit retains the full
state. A miss derives the actual target call and store. Initial physical
facts derive intermediate and final validity and residency. The native steps
are raw execution steps. Semantic traces and historical writer origins
remain separate obligations. Successful worker equations stay explicit.

A checked closed source passes actual primary selection and Parent reduction.
Its ordinary child height rises from 1 to 3 when unions count as zero.
The analogous positive count rises from 0 to 1. This refutes those proposed
measures at an accepted selected operation. It establishes no infinite
execution or Haskell defect. General recursive progress remains open.

Full Audit passes 3227 jobs and 70874 checks. Two production and three
constructed strict logs are empty. All {public} public and {constructed} constructed
full pairs pass in {groups} groups with all eight settings and standard axioms.
Audit peak is 404 MiB under 4 GiB maximum/high and zero swap. Four component
manifests pin {entries} entries. Evidence is in
`lean/restart-evidence/20261018-selected-edit-events/`.

Next derive semantic read and writer facts along the literal selected
schedule. Complete the recursive below-edit case and chronological target
writers. Establish all-owner separation and a fresh-call bound or a global
well-founded measure. General recursive completion, recursive language
preservation, used-writer alignment, repeated convergence and public Haskell
correspondence remain open. The strongest complete ordinary outer domain
is unchanged. No Haskell patch is added. Field-pool repair b9219b9e remains
fixed in c0cc8a05. Keep FINDINGS first. The full-library goal stays active.
Publication awaits the existing direct approval. No push is attempted.

'''
anchor = '## Current outer memo origins and exact indexed dispatch\n'
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
Actual selected class slots now derive exact prefix/call/suffix schedules
without a guard footprint or future semantic read law. Whole-slot callbacks
retain the original path. Actual leaves derive target hit or miss, native
request and full intermediate state. Initial physical facts derive validity
and residency. Raw steps do not assert semantic traces or writer origins.
An accepted source-built Parent operation raises ordinary height from 1 to 3
and positive count from 0 to 1 when unions count as zero. These are failed
candidate measures, not a Haskell defect or infinite execution. General
recursive progress and concrete Haskell correspondence remain open.
Full Audit passes 3227 jobs and 70874 checks. No Haskell patch or new
production defect is added. Field-pool repair `b9219b9e` remains fixed in
`c0cc8a05`. Read `lean/notes-current-selected-edit-events.md`.
Keep this registry first. Record each later repair with failure, executable
reproducer, paths, commit, checks and upstream status. Preserve every earlier
repair entry below.

'''
path.write_text(text.replace(registry, registry + entry, 1))
path = ROOT / 'lean/notes-proof-status-20261017.md'
text = path.read_text()
assert 'Checked at proof checkpoint `1fde7bb0`.' in text
text = text.replace('Checked at proof checkpoint `1fde7bb0`.',
                    'Checked at proof checkpoint `' + proof + '`.', 1)
text = text.replace('[the current checkpoint](notes-current-outer-positional-dispatch.md).',
                    '[the earlier checkpoint](notes-current-outer-positional-dispatch.md).', 1)
anchor = '## Strongest current claim in plain technical English\n'
paragraph = '''Actual coherent active classes now derive every present slot's exact
input and prefix/call/suffix schedule. Whole-slot callbacks retain complete
original paths. Literal leaves derive their target force, native request,
full intermediate state and raw steps without a future semantic read law.
Initial physical facts derive midpoint and final validity and residency.
Semantic traces and historical writer origins remain open at this boundary.
An accepted source-built operation also refutes ordinary height and positive
count measures that treat unions as opaque. General recursive completion
and the complete ordinary outer domain are unchanged. Read
[the current checkpoint](notes-current-selected-edit-events.md).

'''
assert text.count(anchor) == 1
path.write_text(text.replace(anchor, paragraph + anchor, 1))
note = f'''# Selected class dispatch and literal native leaf events

Updated {now}. Proof checkpoint: `{proof}`.
Starting local checkpoint: `6ce48bcd`. Main source: `c0cc8a05`.
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
and concrete Haskell correspondence remain the target. A support predicate
must describe initial inputs and resource limits. It must not assume success.
Read `notes-proof-status-20261017.md` for the target and remaining work.

## Exact selected class slots

ActualClassDispatch.compiled_leaf identifies a compiled callback's complete
natural source path and its signed encoding. children_indexed follows every
present output slot of the literal loop. It produces the exact original
input, completed earlier siblings, selected operation and completed suffix.
An absent lookup retains the complete value and state. A present lookup
supplies the actual recursive call at that input and its two states.

class_dispatch applies this schedule to an actual completed coherent active
runClass call. Each slot is unchanged, executes a whole-slot leaf, or edits
below that slot. A whole-slot callback has path [forestIndex] in the original
record. Both edited cases require positive edit fuel. No unselected guard
footprint, future row law or semantic read receipt is an input. The successful
worker equation, compiler coherence and nontrivial class remain explicit.

## Literal leaf events and physical state

ActualSharedLeafEvents.force distinguishes an exact prior slot hit from a
miss. A hit returns the same full state. A miss supplies the actual target
worker and exact store equation. target_leaf and leaf derive the real target
force, checked native intersection request, intermediate full state, final
advance, retained target slots and retained merge memo. A finite raw Steps
trace follows from the completed native equation. It does not assert the
per-step semantic Inputs facts of the stronger checked Trace relation.

physical derives intermediate and final SharedGood, growth effects and
resident target, input and output from initial physical facts. It does not
infer native semantic key safety or historical writer origins from weak
physical validity. Those facts must follow the actual chronological calls.

One constructed case builds a nonempty class and source, derives the initial
physical state, and executes a cold leaf followed by a warm leaf. The warm
force has zero target-worker bounds and retains the same full state. A second
case builds a positive-own ordinary source with plain recursive children.
Its actual class call supplies the exact first leaf and later sibling
schedule. The production observers then derive its target miss, store,
native steps and physical midpoint. Neither fixture supplies semantic Reads.

## Accepted-operation rank boundary

A separate closed source has two ordinary wrapper operands. Each wrapper
contains an explicit union of a common finite constrained pair and a
different closed plain recursive value. Initial allocation history
derives the full Scan Ready state. The actual primary call returns false
unchanged. The actual Parent call completes and keeps its full guard.

When Mu and union count as zero, each original wrapper has ordinary height
1. The returned children have maximum ordinary height 3. The analogous
maximum positive ordinary count rises from 0 to 1. Native intersection can
expose a finite alternative below a union boundary. These facts refute those
proposed scalar bounds at an accepted selected operation. They do not prove
an infinite outer execution or identify a Haskell defect. The selected
endpoints satisfy the primary gate. No constrained Mu endpoint is required.

## Remaining proof work

Compose actual selected calls with semantic Inputs checks and native writer
history. Extend that composition through below edits and chronological target
writers. Derive the footprints needed for every consecutive continuation
step, or prove another global well-founded measure. Handle mixed indexes,
plain phases and sibling work. Prove all-owner separation and a finite bound
on fresh recursive requests. Complete recursive outer language preservation,
used-binder writer alignment, repeated convergence, concrete adapters and
public Haskell correspondence. The complete ordinary outer domain is
unchanged. Theorem counts do not give a completion percentage or time estimate.

## Verification and preservation

Full Audit passes 3227 jobs and 70874 dependency checks. Only the unchanged
ClosedCompletion unused-variable warning remains. Two production and three
constructed strict logs have exactly zero bytes. All {public} public and
{constructed} constructed pairs have complete signatures, proofs and axiom reports
in {groups} groups. All eight required options are enabled. Only standard axioms
occur. Effective maximum/high memory limits are 4 GiB. Swap maximum is zero.
The Audit peak is 404 MiB. Four component manifests pin {entries} entries.
All numbered drafts and raw output remain present. Evidence is in
`restart-evidence/20261018-selected-edit-events/`.

All 26449 starting files remain present. All 3224 older non-Audit Lean sources,
242 Haskell files and 206 active-package files retain their bytes. Two stashes
and three other worktrees retain their metadata. Audit only adds two imports.
The preservation report checks 137 frozen manifests and 984 module entries.
Root FINDINGS retains every earlier repair entry. No Haskell patch or new
production defect is added. Field-pool repair b9219b9e remains fixed in main
c0cc8a05. Publication awaits the existing direct approval. No push is attempted.
'''
(ROOT / 'lean/notes-current-selected-edit-events.md').write_text(note)
print(json.dumps({'proof_commit': proof, 'updated_at': now, 'authority_documents': 8}))
