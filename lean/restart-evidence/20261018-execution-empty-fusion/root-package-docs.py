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
section = f'''## Current source Empty abstraction and derived child schedules

Updated: {stamp}. Proof checkpoint is `{proof[:8]}`.
Starting checkpoint is `58ab02d5`. Main source remains `c0cc8a05`.
Read `lean/notes-current-execution-empty-fusion.md`.

The physical Empty result of one full source expression now depends only
on its ordered lexical Empty tests. A pure projection makes external roots
opaque and retains every fresh binder local. Its proof covers all source
constructors. Actual source calls derive returned Empty agreement from
initial Contexts and matching input tests. No alias premise is needed.
This law compares the same full source expression, not different encodings.

A pure stored Empty interpreter now evaluates the complete encoded plan.
Actual execution derives its exact physical Empty result. Closed literals,
resolved references and open-Mu smart reconstruction have explicit rules.
The checked equal-shape example has different predicted Empty results.
Decoded original shape is not substituted for the full stored plan.

The filtered variable case now derives both Generated memberships and
physical Empty agreement. Its Empty hypothesis applies only to the
selected resolved reference pair. Fixed unions and open Mu captures need
no output-law hypothesis. Scoped self tests derive equal actual filters.

Historical parent node calls now derive indexed source rows, opposite raw
row survival, all warm child source calls, both stored row schedules and
ordered mutual Generated child memberships. The proof derives fresh
filter absence from available raw results and historical live support.
It needs no reader-wide lexical availability or supplied child schedules.
Survival of the opposite stored row still needs the general Empty proof.

General source/filter/stored Empty fusion, union subgroup preparation and
nested used-binder simulation remain open. The proof must retain the
actual earlier writer's body and causal history. Membership alone is not
Directed. Automatic arbitrary open-Mu reader support remains open.

The strongest broad claim is unchanged: a supported successful top-level
model traversal with empty inherited constraints, initial semantic facts
and scheduled resources preserves exactly the accepted finite terms.
General termination and complete public Haskell correspondence remain
open. Initial query operands, active-owner exclusion, fresh bounds,
repeated convergence, equality resources and host Int adequacy remain.

Full Audit passes {audit['jobs']} jobs and {audit['dependency_checks']} dependency checks.
All {counts['pairs']['new-public']} new public and {counts['pairs']['constructed']} constructed heads pass complete
statement, proof and standard-axiom checks. Eight selected strict logs
are empty. All four canonical builds are warning-free. Audit retains
only the existing ClosedCompletion warning. Five component manifests pin
{entries} entries. Independent source-abstraction review finds no material
issue. Evidence is in `lean/restart-evidence/20261018-execution-empty-fusion/`.

No Haskell patch or new executable defect is added. FINDINGS retains the
repair registry first. Field-pool repair b9219b9e remains fixed in c0cc8a05.
Publication awaits the existing direct approval. No push is retried.
The full-library goal remains active.

'''
authorities = ['NEXT-PROMPT.md', 'HANDOFF.md', 'lean/README.md', 'lean/SYSTEM.md',
               'lean/API-COVERAGE.md', 'lean/COVERAGE.md', 'lean/notes-proof-status-20261017.md']
marker = '## Current generated lexical, node and union cases\n'
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
One full source expression now preserves physical Empty under equal
ordered lexical Empty tests. Actual calls derive this law from initial
Contexts. Full stored encodings have an exact pure Empty interpreter.
The filtered variable case derives mutual membership and its selected
reference Empty case. Historical node calls derive all indexed child
source and stored schedules without reader-wide lexical availability.
General stored row survival, source/filter/stored fusion and nested
used-binder simulation remain open. Full Audit passes {audit['jobs']} jobs and
{audit['dependency_checks']} checks. No Haskell patch or new executable defect is added.
Field-pool repair `b9219b9e` remains fixed in `c0cc8a05`. Read
`lean/notes-current-execution-empty-fusion.md`. Keep this registry first.
Record later repairs with failure, executable reproducer, paths, commit,
checks and upstream status. Preserve every earlier entry.

'''
path = ROOT / 'FINDINGS.md'
text = path.read_text()
header = '## Haskell fix handoff for external work\n\n'
assert text.startswith('# Current formalization findings\n\n' + header)
path.write_text(text.replace(header, header + entry, 1))

note = '# Source Empty abstraction and actual node schedules\n\n' + section.split('\n\n', 1)[1]
note = note.replace('Read `lean/notes-current-execution-empty-fusion.md`.\n', '')
note += '''## Pure source abstraction

SourceCurrentSourceEmptyAbstraction.same_empty compares arbitrary profile
environments, including different external name types. Their ordered
Empty test lists must be equal. The source expression is the same on both
sides. The result compares its evaluated Empty tests. This is a general
syntax induction, not a finite example or a replacement-name map alone.

The internal projection accepts a partial name map. A discarded external
root becomes an opaque nonempty alternative. It is not deleted. The
lifted projection keeps the fresh local. Projection commutes with source
union, node survival and binder lowering. Forgetting every external name
therefore gives the same profile whenever the lexical Empty tests match.
The actual source corollary derives both returned Contexts, availability
and profile laws from initial Contexts and literal successful calls.

The constructed integration supplies a bare Depth reference to one call
and a closed ordinary capture to another. Both input tests are nonempty.
The same source returns two distinct used Mu values. Actual sequential
calls and Keeps remain explicit. The theorem derives Empty agreement.
A third actual call with an Empty capture returns literal Empty.

## Full stored plans

SourceCurrentStoredEmptyInterpreter.test evaluates the full source plan
produced by encode(leaves value, [], value). Its lexical profiles use the
actual optional replacement environment. execute_test derives the exact
physical Empty Bool from actual execution, Ready, input availability and
replacement availability. It permits allocation and a different final heap.

Closed records remain captured literals. References use optional resolved
values. Open Mu records evaluate their full stored body under a smart
binder and a fresh symbolic local. The equations retain the actual body
and do not replace it with the original Mu's decoded shape. A checked
source-built example has two used Mu values with equal decoded shapes.
The pure tests differ, in agreement with their actual stored executions.
The original closed root keeps its nonempty test. This exercises the
closed and open paths. It does not prove the general source/filter fusion.

## Filtered variables

SourceCurrentGeneratedVariableFilter.variable_call uses actual variable
builds, actual warm root filters and actual warm stored calls. It needs
only the selected first raw value's availability. It does not require all
lexical inputs at the reader. Exact scoped self tests are retained.

A reference slot returns its existing resolved mutual Generated pair.
The Empty induction hypothesis applies only to those selected resolved
references. An identical nonreference capture has equal actual filters:
the own names are equal, or both names are absent from its free names.
Filtering adds no free name. Equal maps on raw free names therefore give
equal stored outcomes for the filtered capture. This covers unions and
arbitrary open Mu captures. No desired fixed-capture output law is assumed.
The constructed integration checks both a nontrivially filtered fixed
union and two varying references whose supplied values are Empty.

## Derived node schedules

SourceCurrentGeneratedNodeSchedules.historical_pair retains the original
source Contexts and builds. Returned tables grow into one Ready reader.
The raw results are available there. Actual source free-name agreement
transfers fresh-name absence to the live source Scope. This derives the
historical and warm identity filters. Raw builds replay at the reader.
Actual stored calls then generate both result directions. Unused captures
need not all be available at that reader.

The node theorem starts with two actual historical source-node calls and
actual warm stored parent calls. It selects one physical raw row. Actual
constructor inversion gives its original source index and complete row
fields. The same index on the other side has the same raw survival test.
The proof constructs both historical RowCall receipts, their real prefix,
child, edge and suffix heaps, and both raw rows' reader availability.

Available physical raw parents supply their selected children's reader
availability. Historical source receipts derive every child's original
Context and warm replay. Live source support supplies each child alias
relation. Actual parent execution derives both stored RowCalls, including
all child calls before row-survival filtering. Ordered child outputs have
mutual Generated membership. The theorem does not assume child schedules,
child Generated memberships, child Empty laws or parent output semantics.

The constructed integration starts from source-built Ready data. Two
sequential cold source-node calls contain a live union child and a dead
row with an unused captured alias. Sequential stored parent calls retain
the actual allocation growth. The new node theorem supplies the indexed
child schedules and ordered memberships. The full false guard remains.
The opposite stored row's survival remains separate proof work.

## Remaining obligations and preservation

The source abstraction compares one fixed expression. The stored test
uses one complete encoded plan. The main fusion must connect different
plans produced by actual source construction and filtering. A binder may
select an earlier writer with different source syntax. Use that writer's
actual body, callback history and common forward reader. Do not replace
this obligation with assumed output Empty agreement, Same or BodyIH.

The warm-parent/cold-subgroup counterexample remains valid. Union proofs
must retain the actual subgroup allocation or derive needed preparation.
The equal-original-shape counterexample also remains valid. Raw decoded
shape equality does not imply stored-substitution Empty agreement.
Neither counterexample refutes the full intended generated relation.

The strongest broad claim remains supported conditional partial
correctness. NodeLaw excludes added accepted terms and retains inherited-
satisfying input terms. Empty inherited constraints give exact finite
language equality. Initial semantic facts and scheduled resources remain
explicit. General termination and full public Haskell correspondence are
not supplied by the audit. Initial operand ancestry, active-owner
exclusion, fresh bounds, repeated convergence, equality resources, host
Int adequacy and arbitrary open-Mu reader support remain separate work.

All 31562 starting tracked files remain. All 3321 older non-Audit Lean
sources, 242 Haskell files and 206 active package files retain their bytes.
Two stashes and three other worktrees retain their metadata. Preservation
extends 166 frozen manifests with these four modules. All earlier proofs,
repairs, counterexamples, failed attempts, drafts and optimized core remain.

Selected runs use Lean 4.34.1 with five-minute caps. Inner readback verifies
memory.max and memory.high 4294967296 and memory.swap.max0. Complete public
and constructed probes use all eight printer and linter options. The only
permitted axioms are propext, Classical.choice and Quot.sound. All failed
attempts remain unselected. Root reviews every new module. A separate
independent review covers the source abstraction. No Haskell file changes,
so Haskell formatters and tests are not needed for this batch.
'''
(ROOT / 'lean/notes-current-execution-empty-fusion.md').write_text(note)
(HERE / 'ROOT-SCOPE.md').write_text(note)
(HERE / 'NEXT.md').write_text('''# Next proof work

Read NEXT-PROMPT.md, HANDOFF.md and FINDINGS.md. Preserve the full-library
goal, every earlier proof and the optimized core. Publication awaits the
existing direct approval. Do not retry a push without that approval.

Use SourceEmptyAbstraction for SAME complete source syntax with equal
ordered lexical Empty flags. It covers arbitrary captured records and
nested binders. It does not identify different stored encodings.
StoredEmptyInterpreter gives the exact pure Empty test for each actual
stored call. Its open Mu equation retains the full encoded body. The
closed shortcut remains literal. The equal-original-shape boundary still
rules out replacing that body by the original Mu's decoded metadata.

GeneratedVariableFilter closes the filtered variable case from the selected
resolved-reference Empty hypothesis. Fixed captures derive exact outcomes
from self tests and map agreement; they need no desired output law.
GeneratedNodeSchedules derives exact indexed source and stored child
schedules from parent calls and historical Contexts. It needs only raw
result availability at the reader, not every unused lexical capture.
All ordered child Generated directions are derived. The remaining node
survival proof needs the general generated child Empty law.

Prove the source/filter/stored Empty fusion for actual generated pairs.
Then complete the reference, row and epsilon Local clauses. Keep nested
used binders and changing outer captures. A selected earlier writer can
have different syntax. Preserve its actual body and chronology. Do not
assume the desired output law or infer Directed from membership alone.
Check the reachable-reader restriction needed for the global theorem.
Context and four-table Grows do not contain a chronological writer path.

For unions, keep the bare-self exception and actual intermediate heaps.
A warm parent does not imply a warm filtered subgroup. Derive preparation
where needed, including general open-Mu support. Continue initial operand
ancestry, active-owner exclusion, fresh bounds, recursive completion,
repeated convergence, equality resources, host Int adequacy and complete
public Haskell correspondence. Record actual Haskell fixes first in root
FINDINGS with reproducer, paths, commit, validation and upstream status.
No Haskell fix is added in this batch.
''')
print(json.dumps({'proof': proof, 'component_entries': entries, 'strict_logs': 8}))
