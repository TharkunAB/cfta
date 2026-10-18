import json
import re
import subprocess
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]


def read(name):
    return json.loads((HERE / name).read_text())


stamp = subprocess.check_output(['date', '+%Y-%m-%d %H:%M %Z'], text=True).strip()
proof = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip()
(HERE / 'proof-commit.txt').write_text(proof + '\n')
counts = read('expected-counts.json')
audit = read('selected-audit.json')
components = read('component-manifests.json')
entries = sum(len(read(name).get('entries', read(name).get('files', []))) for name in components)
section = f'''## Current stored Empty transport and cold union preparation

Updated: {stamp}. Proof checkpoint is `{proof[:8]}`.
Starting checkpoint is `4df4242f`. Main source remains `c0cc8a05`.
Read `lean/notes-current-stored-empty-transport.md`.

For the same original stored value, equal resolved physical Empty tests
on its original free names imply equal actual returned Empty tests.
Replacement records, entry heaps and returned heaps can differ. The proof
restricts both maps to original free support before comparing the full
encoded plan. Internal bound names need no external map agreement.

Arbitrary nonempty replacements on original free names now preserve the
original physical Empty test. Positive occurrence costs prove identity
retention through the full stored plan. Actual Mu unfolding therefore has
the same physical Empty test as its stored body. This result includes
arbitrary open nested Mu values. Physical Empty is the constructor test.
It is not the semantic claim that the accepted finite language is empty.

Generated pairs and lexical Inputs now transport through actual Keeps
growth. Their original historical receipts remain unchanged. Every warm
source, filter and stored call replays at the later reader. This proves
membership transport, not observation equality or Directed simulation.

Actual historical union calls now recover complete availability of all
original raw source members at a Ready reader. Finite preparation runs
each member filter and stored call, then the parent calls. It derives
the final Keeps, availability and warm replays. No initial warm subgroup
filter or caller-supplied child schedule is required. The generated
relation still requires historical build-to-filter adjacency. The new
forward schedules alone do not supply that receipt.

The strongest broad statement remains conditional partial correctness:
under the stated initial semantic, heap and resource assumptions, a
successful checked model traversal with an empty list of inherited
constraints accepts exactly the same finite trees as its input. General termination and full
public Haskell correspondence remain open. General source/filter/stored
fusion and changing-capture binder simulation remain the main local gap.
Initial operands, active-owner exclusion, fresh bounds, repeated
convergence, equality resources and host Int adequacy remain separate.

Full Audit passes {audit['jobs']} jobs and {audit['dependency_checks']} dependency checks.
All {counts['pairs']['new-public']} new public and {counts['pairs']['constructed']} constructed heads pass full
statement, proof and standard-axiom checks. Eight selected strict logs
are empty. All four canonical builds are warning-free. Audit retains
only the existing ClosedCompletion warning. Five manifests pin {entries}
entries. Independent review checks the nonempty replacement proof.
Evidence is in `lean/restart-evidence/20261018-stored-empty-transport/`.

No Haskell patch or new executable defect is added. FINDINGS retains the
repair registry first. Field-pool repair b9219b9e remains fixed in c0cc8a05.
Publication awaits the existing direct approval. No push is retried.
The full-library goal remains active.

'''
authorities = ['NEXT-PROMPT.md', 'HANDOFF.md', 'lean/README.md', 'lean/SYSTEM.md',
               'lean/API-COVERAGE.md', 'lean/COVERAGE.md', 'lean/notes-proof-status-20261017.md']
marker = '## Current source Empty abstraction and derived child schedules\n'
for name in authorities:
    path = ROOT / name
    text = path.read_text()
    assert marker in text and section.splitlines()[0] not in text, name
    text = text.replace(marker, section + marker, 1)
    if name == 'lean/notes-proof-status-20261017.md':
        text = re.sub(r'Checked at proof checkpoint `[0-9a-f]+`\.',
                      f'Checked at proof checkpoint `{proof[:8]}`.', text, count=1)
    path.write_text(text)

entry = f'''Current proof update: {stamp}. Proof checkpoint is `{proof[:8]}`.
The same original stored value now preserves actual output Empty under
resolved Empty agreement on original free names. Nonempty replacements
preserve its original physical Empty test. Actual Mu unfolding retains
the stored body's test. Generated memberships transport through Keeps.
Actual union history recovers complete original-member availability and
constructs cold member filter/stored schedules with final warm replays.
Historical filter adjacency, general semantic fusion and changing-capture
binder simulation remain open. These are proof results, not executable
Haskell repair requests. Full Audit passes {audit['jobs']} jobs and {audit['dependency_checks']}
checks. No Haskell patch or new executable defect is added. Field-pool
repair `b9219b9e` remains fixed in `c0cc8a05`. Read
`lean/notes-current-stored-empty-transport.md`. Keep this registry first.
Record later repairs with failure, executable reproducer, paths, commit,
checks and upstream status. Preserve every earlier entry.

'''
path = ROOT / 'FINDINGS.md'
text = path.read_text()
header = '## Haskell fix handoff for external work\n\n'
assert text.startswith('# Current formalization findings\n\n' + header)
path.write_text(text.replace(header, header + entry, 1))

note = '# Stored Empty transport and cold union preparation\n\n' + section.split('\n\n', 1)[1]
note = note.replace('Read `lean/notes-current-stored-empty-transport.md`.\n', '')
note += '''## Strongest broad statement and target

SourceCurrentOuterInitialActual.node_call proves the law for a successful
bounded nodeCall. Its premises retain initial Context, Frame, Fits,
Carrier, inherited readiness, input availability and scheduled Room.
SourceCurrentAllocatedPartialMemoSound.NodeLaw states that the result adds
no accepted finite term. It also preserves each input term that satisfies
the inherited constraint. Empty inherited constraints give exact finite
language equality. These are explicit theorem premises. They are not all
constructed from arbitrary public Haskell inputs by the present proof.
The initial empty list is request.inherited.payload = some []. A payload
of none denotes contradiction.

Initial Context includes semantic correctness of completed memo entries.
Frame includes recursive heap observations and stored query laws. These
are semantic premises, in addition to valid identities and numeric bounds.
The proof does not establish all of them for every source-built recursive
input. General binder correspondence supplies part of that missing step.
In particular, Frame.context.guards requires agreement between each
stored Mu body's and ordinary probe's guard-depth observations. Frame.initial
still takes this certificate as a premise. General changing-capture and
retained used-Mu initialization must supply it from source construction.

The full target remains the intended semantics of the complete library
and correspondence with its public implementation. The recursive checked
worker needs its remaining initial and semantic instances, supported
execution and resource bounds. General recursive completion, repeated
convergence, equality-operation resources and host Int adequacy remain.
Passing builds and theorem totals do not supply those connections.

## Original free-name Empty congruence

SourceCurrentStoredEmptyCongruence.execute_same uses one original value,
two Ready entry heaps, input and replacement availability, and two literal
completed execute calls. Only the resolved physical Empty flags on the
original free names must match. The returned heaps can be arbitrary.
The maps first restrict to the original free names through the repaired
execute_restrict law. Internal bound reference leaves therefore receive
the same defaults. SourceEmptyAbstraction compares the same full encoded
plan. The concrete integration uses an open used Mu and distinct available
ordinary replacement records. Both actual returned values are nonempty.

## Nonempty replacement and unfolding

SourceCurrentStoredNonemptyReplacement.execute_nonempty starts from an
actual completed execute call and Ready input data. Every resolved map
value at an original free name must be physically nonempty. The result's
physical Empty Bool equals the original value's Bool. The replacements
can contain arbitrary available records. They need no free occurrence.

The internal identity proof supplies the original captured shapes and
actual occurrence costs to InternedStoredCostRetention.encode_retains.
Canonical slot readback gives exact closed and reference inputs. Coherent
free-name support supplies occurrence support. Positive identity meanings
retain nonempty original plans through arbitrary nested open Mu records.
Empty original values use the literal closed shortcut. A complete actual
identity call and execute_same then supply the arbitrary replacement law.

The unfold_mu theorem applies that law to actual replacement by the Mu
record itself. Unfolding preserves the stored body's physical Empty test.
It does not claim that every Mu's finite language is nonempty or that
different stored encodings have the same behavior. Earlier equal-shape
counterexamples remain valid. Their full stored bodies differ.

## Forward readers and union calls

SourceCurrentGeneratedGrowth.generated and inputs replay the original
historical receipts at a later Keeps reader. Keeps supplies complete
availability transport and retained Ready data. Each source, filter and
stored replay has its original successful equation. No desired semantic
output relation is assumed. Membership is not itself a simulation proof.

SourceCurrentGeneratedUnionPreparation.source_members inverts the actual
historical union build. It recovers the original ordered raw source
members, their intermediate heap, the actual makeUnion equation and
source-indexed historical and warm calls. Resident nonprimitive records
use retained reader cache payloads to recover full recursive availability.
Primitive references use the raw parent's free-name support. This avoids
an invalid inference about hidden bound names from parent free support.

FilteredCalls records the actual sequential member filter and stored
calls. prepare constructs that trace from initial Ready data. Parent
filtering and execution follow it. All values and literal warm replays
are available at the final reader. The cold-subgroup integration checks
that the parent filter was already warm while its first source subgroup
filter still allocated. Preparation retains that actual cold interval.

The Generated.filtered constructor requires its historical filter at the
historical raw-build return. New subgroup preparation occurs at a later
reader. Those two receipts are not automatically interchangeable. Complete
the union composition by deriving the needed historical receipt or by
proving a justified generator extension with the intervening history.
Do not silently assume lexical Context at the later filter entry.

General source/filter/stored Empty fusion remains open for distinct raw
values and encodings. So do row survival, union semantic composition,
nested used-binder simulation and arbitrary open-Mu reader preparation.
Retain each selected earlier writer's actual body and causal history.

## Verification and preservation

All 31801 starting tracked files remain. All 3325 older non-Audit Lean
sources, 242 Haskell files and 206 active package files retain their bytes.
Two stashes and three other worktrees retain their metadata. Preservation
extends 167 frozen manifests with four modules. Every earlier proof,
repair, counterexample, failed attempt, draft and optimized core remains.

Selected checks use Lean 4.34.1 and five-minute caps. Inner readback verifies
memory.max and memory.high 4294967296 and memory.swap.max 0. Complete public
and constructed probes use all eight required printer and linter options.
Only propext, Classical.choice and Quot.sound are permitted axioms. All
failed attempts remain unselected. No Haskell file changes, so Haskell
formatters and tests are not needed for this batch.
'''
(ROOT / 'lean/notes-current-stored-empty-transport.md').write_text(note)
(HERE / 'ROOT-SCOPE.md').write_text(note)
(HERE / 'NEXT.md').write_text('''# Next proof work

Read NEXT-PROMPT.md, HANDOFF.md and FINDINGS.md. Preserve the full-library
goal, all earlier work and the optimized core. Publication awaits direct
approval. Do not retry a push without that approval.

Use original-free-name Empty congruence for the SAME original stored
value. Nonempty replacements preserve its physical Empty test. Actual
Mu unfolding preserves its stored body's physical Empty test. Physical
Empty is not semantic finite-language emptiness. The main remaining
fusion compares distinct actual source/filter/stored values and plans.

Generated and Inputs transport through Keeps. Actual historical union
calls recover complete raw member availability without all lexical inputs
at the reader. Cold member preparation supplies actual sequential calls,
final Keeps and literal warm replays. It does not supply the historical
build-to-filter adjacency required by Generated.filtered. Resolve that
receipt before claiming complete union composition. Do not assume a
later lexical Context merely from four-table Grows.

Complete general generated Empty fusion and the reference, row and
epsilon Local clauses. Retain nested used binders, changing captures,
actual earlier writer bodies and causal histories. Do not assume the
desired output law or infer Directed from membership alone. Continue
arbitrary open-Mu reader support, initial operands, active-owner exclusion,
fresh bounds, recursive completion, repeated convergence, equality
resources, host Int adequacy and public Haskell correspondence.

Record every actual Haskell fix first in root FINDINGS, with failure,
executable reproducer, paths, commit, checks and upstream status. No
Haskell fix is added in this batch.
''')
print(json.dumps({'proof': proof, 'component_entries': entries, 'strict_logs': 8}))
