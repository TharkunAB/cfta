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
section = f'''## Current semantic reads at actual target and class returns

Updated: {now}. Proof checkpoint is `{proof}`.
Starting local checkpoint is `6a01228d`. Main source remains `c0cc8a05`.
Read `lean/notes-current-actual-semantic-reads.md` for exact boundaries.

Initial numeric target completion now aligns its own semantic Reads and
full receipt with any literal successful target call. Uniqueness identifies
the complete Value, Checked state and Merge memo. The observed fuel tuple
needs no lower bound from the forecast. A historical target can then produce
the full semantic SlotReceipt with explicit later Keeps and Merge Extends.

Whole-class and tail-first fold adapters now derive semantic Reads, full
receipts, returned Frame/Fits and length at the literal worker endpoints.
Initial causal native history also derives the actual selected-call relation
with ordered prefix/suffix reads and histories. No future Reads are supplied.
The whole-class route derives historical target contexts internally.

Initial Frame/Fits, semantic warm-cache and global validity, selected
ForestClosed domains, physical storage and pure numeric reservations stay
explicit. Frame includes idle native execution at entry. Warm returned and
suspended entries are permitted. Untouched roots can stay open. No finite
input Cap is added. Target receipts give one-way common-subterm inclusion.
They do not assert exact target intersection language.

Full selected Audit2 passes 3232 jobs and 70901 checks. Two production and
two constructed strict logs are empty. All {public} public and {constructed} constructed
full pairs pass in {groups} groups with all eight settings and standard axioms.
Selected Audit peak is 87 MiB under 4 GiB maximum/high and zero swap.
The earlier 360 MiB Audit is retained. Four component manifests pin {entries}
entries. Evidence is in `lean/restart-evidence/20261018-actual-semantic-reads/`.

Next establish this semantic context and reservation at the actual outer
class/fold entry. Then compose the produced selected/native lineage.
General recursive progress, all-owner separation, fresh-call bounds,
recursive language preservation, used-writer alignment, repeated convergence
and public Haskell correspondence remain open. The strongest complete
ordinary outer domain is unchanged. No Haskell patch is added. Field-pool
repair b9219b9e remains fixed in c0cc8a05. Keep FINDINGS first. The full-library
goal stays active. Publication awaits the existing direct approval.
No push is attempted or retried.

'''
anchor = '## Current target-slot writers and initial native admission\n'
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
Initial numeric completion now derives target, class and fold semantic
Reads at literal successful worker endpoints. Full Value/forest, Checked
and Merge equality aligns all states without an observed-fuel lower bound.
A historical target yields its full semantic SlotReceipt. Initial class
context also derives selected-call Reads and histories. Initial semantic
Frame/global/selected-domain/reservation facts remain explicit. The whole
class route derives historical target contexts internally. General outer
entry context transport and recursive progress remain open. Full selected
Audit passes 3232 jobs and 70901 checks. No Haskell patch or new production
defect is added. Field-pool repair `b9219b9e` remains fixed in `c0cc8a05`.
Read `lean/notes-current-actual-semantic-reads.md`. Keep this registry first.
Record each later repair with failure, executable reproducer, paths, commit,
checks and upstream status. Preserve every earlier repair entry below.

'''
path.write_text(text.replace(registry, registry + entry, 1))
path = ROOT / 'lean/notes-proof-status-20261017.md'
text = path.read_text()
assert 'Checked at proof checkpoint `99a1ddb3`.' in text
text = text.replace('Checked at proof checkpoint `99a1ddb3`.',
                    'Checked at proof checkpoint `' + proof + '`.', 1)
text = text.replace('[the current checkpoint](notes-current-selected-read-producers.md).',
                    '[the earlier checkpoint](notes-current-selected-read-producers.md).', 1)
anchor = '## Strongest current claim in plain technical English\n'
paragraph = '''Initial numeric completion now produces target/class/fold semantic Reads
at literal successful worker endpoints. Complete value, Checked and Merge
uniqueness aligns all states without a forecast lower-bound premise on the
observed fuels. Historical semantic SlotReceipt and actual class-selected
reads/histories then follow from initial supported contexts. Selected path
closure permits open untouched roots; no finite input Cap is added. Frame,
semantic caches, valid globals and numeric reservations remain explicit.
The next general bridge is that context at the actual outer class entry.
General recursive completion and the complete ordinary outer domain are
unchanged. Read [the current checkpoint](notes-current-actual-semantic-reads.md).

'''
assert text.count(anchor) == 1
path.write_text(text.replace(anchor, paragraph + anchor, 1))
note = f'''# Semantic reads at actual target and class returns

Updated {now}. Proof checkpoint: `{proof}`.
Starting local checkpoint: `6a01228d`. Main source: `c0cc8a05`.
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
Complete public contracts and concrete Haskell correspondence remain the
target. Read `notes-proof-status-20261017.md` for the whole-library scope.

## Semantic target alignment

ActualTargetSemanticReads.target invokes TargetNumeric.complete from its
initial Frame/Fits, available originals, selected domains, physical Stored,
semantic CacheCovers, valid globals and initial numeric TargetReserved.
It constructs its own graph, TargetReads and full receipt. Successful-return
uniqueness aligns the complete Value, Checked state and Merge memo with
the literal supplied return. All five observed fuels can differ from the
forecast fuel. No lower-bound premise on those successful fuels is needed.
No future semantic read or desired target language is an input.

slot_receipt applies this alignment to the exact record operandPaths at a
historical writer. Path membership and later heap Keeps and Merge Extends
remain explicit. The result is the full existing semantic SlotReceipt,
including its historical graph, Reads, receipt and reader transport.
Its language contract preserves common subterms in one direction. The
target can accept additional terms. Exact intersection language is not
claimed by this slot contract.

## Whole-class and fold alignment

ActualClassSemanticReads.class_reads and fold_reads use the existing
ClassNumeric and ClassPassNumeric producers. Their own Class/Fold graphs
and Reads align to the observed complete ordered forest, Checked state
and Merge memo through successful-return uniqueness. They also return
full receipts, the same returned inventory Frame, final Fits and length.
The tail-first class order is unchanged. class_selected combines the
produced Reads with initial causal native history to derive the exact
selected child schedule, intermediate readiness and histories. No future
ClassReads, FoldReads or desired final history is a premise.

The whole-class route supplies each reached historical target context
internally. It avoids separate Frame reconstruction for every warm slot.
The standalone historical target route still needs its writer entry support.
Target-only History does not itself transport those semantic entry facts.

## Initial support and constructed scope

Frame contains Ready, semantic cache admission, causal guard context,
conditional joint cache laws and captured origins. Ready includes native
Idle. Warm suspended and returned native entries remain permitted. This
is stronger than weak physical cells. Fits bounds counters and stored mass.
Room and Reserved are pure functions of initial profiles, paths and record
counts. They inspect no future returned forest or desired completed graph.
Only selected ForestClosed paths are required. Untouched roots can be open.
No finite input Cap or whole-input closure is introduced.

The target fixture builds its own source, allocated tables, Frame/Fits
and finite numeric room. Its class has three source paths. The captured
forest has an open unselected root. A literal unequal-fuel target call
8/16/64/16/128 supplies the observed result and states. Both target and
slot_receipt produce semantic evidence at those endpoints. Ready.store
and a warm lookup recover availability and closedness. An all-zero force
returns the installed value and the same full state.

The class fixture builds a constrained recursive source outside every
finite Cap and retains an open unrelated depth root. Initial context and
room construct numeric completion. Six independently increased successful
fuel replays then supply the observed class call. The fixture consumes
class_reads and class_selected without an input Reads or Selection law.
This is computed completion and replay alignment. It is not an independent
small-fuel evaluation or a retained Scan/public pipeline execution.

## Remaining work

Establish the full initial semantic context and pure reservation at the
actual outer class/fold entry. Carry semantic warm-cache admission, globals,
selected domains and native history through actual earlier outer work.
Then compose the produced selected/native lineage with global progress.
General recursive completion, all-owner separation, fresh-call bounds,
recursive language preservation, used-writer alignment, convergence,
concrete adapters and public Haskell correspondence remain open. Logical
global memo receipts do not establish concrete Haskell memo lookup or
forcing schedules. The complete ordinary outer domain is unchanged.
Theorem counts do not give a completion percentage or time estimate.

## Verification and preservation

Selected Audit2 passes 3232 jobs and 70901 dependency checks. Only the
unchanged ClosedCompletion warning remains. Two production and two
constructed strict logs are zero bytes. All {public} public and {constructed}
constructed pairs have complete signatures, proofs and standard axiom
reports in {groups} groups. All eight required options are enabled. Effective
maximum/high memory limits are 4 GiB. Swap maximum is zero. Selected Audit
peak is 87 MiB. The earlier 360 MiB Audit before a whitespace correction is
retained. Four component manifests pin {entries} entries. All attempts and
raw output remain present in `restart-evidence/20261018-actual-semantic-reads/`.

All 26757 starting files remain present. All 3229 older non-Audit Lean sources,
242 Haskell files and 206 active-package files retain their bytes. Two stashes
and three other worktrees retain their metadata. Audit only adds two imports.
The preservation report checks 139 frozen manifests and 989 module entries.
Root FINDINGS retains every earlier repair entry. No Haskell patch or new
production defect is added. Field-pool repair b9219b9e remains fixed in main
c0cc8a05. Publication awaits the existing direct approval. No push is attempted.
'''
(ROOT / 'lean/notes-current-actual-semantic-reads.md').write_text(note)
print(json.dumps({'proof_commit': proof, 'updated_at': now, 'authority_documents': 8}))
