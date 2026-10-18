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
stricts = counts['modules'] + counts['constructed_strict']
section = f'''## Current generated lexical, node and union cases

Updated: {stamp}. Proof checkpoint is `{proof[:8]}`.
Starting checkpoint is `c1346edb`. Main source remains `c0cc8a05`.
Read `lean/notes-current-generated-local-rules.md`.

The generated lexical spine now supplies the ordered resolved slot
relation. Actual variable reconstruction derives both Generated directions
and equal output heaps. It does not include root self filtering.

Actual warm source and stored calls now derive both Generated directions
with fresh absent root filters. An actual live source-node row derives
each selected child's aliases and membership from its own actual calls.
No child observation or parent output relation is assumed. General row
survival and the complete node Local law remain open.

Actual union selection, exact bare-self retention and warm stored calls
preserve literal inclusion. A source-built counterexample has a warm
parent filter and a child union whose filter still allocates at the same
Ready reader. A separate source-built example has two available used Mu
values with equal decoded shapes. One substitution returns Empty; the
other does not. These are proof-contract boundaries. They do not refute
Generated or establish a Haskell defect.

The main recursive obligation remains source/filter/stored Empty fusion
and the local reference, row and epsilon rules, including nested used
binders and changing captures. Raw shape equality does not supply this
fusion. Earlier writer provenance and common reader support remain
necessary proof work. No general Generated simulation is claimed.

The strongest broad claim remains conditional partial correctness of the
checked implementation model. A supported successful top-level traversal
with empty inherited constraints, initial semantic facts and scheduled
resources preserves exactly the accepted finite terms. General termination
and complete public Haskell correspondence remain open. The required
source semantic instances remain explicit.

Full Audit passes {audit['jobs']} jobs and {audit['dependency_checks']} dependency checks.
All {counts['pairs']['new-public']} new public and {counts['pairs']['constructed']} constructed heads pass complete
statement, proof and standard-axiom checks. All {stricts} selected strict
logs are empty. All three canonical builds are warning-free. Audit
retains only the existing ClosedCompletion warning. {len(components)} component
manifests pin {entries} entries. Independent review finds no material issue.
Evidence is in `lean/restart-evidence/20261018-generated-local-rules/`.

No Haskell patch or new executable defect is added. FINDINGS retains the
repair registry first. Field-pool repair b9219b9e remains fixed in c0cc8a05.
Publication awaits the existing direct approval. No push is retried.
The full-library goal remains active.

'''
authorities = ['NEXT-PROMPT.md', 'HANDOFF.md', 'lean/README.md', 'lean/SYSTEM.md',
               'lean/API-COVERAGE.md', 'lean/COVERAGE.md', 'lean/notes-proof-status-20261017.md']
marker = '## Current source-generated binder pairs\n'
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
Actual lexical execution and live node-child calls now derive generated
memberships without desired output observations. Actual union filtering
and reconstruction preserve exact literal inclusion. Source-built examples
show a warm parent with an allocating child filter and equal decoded Mu
shapes with different physical Empty results after substitution. These
are proof-contract boundaries, not executable Haskell defects or repair
requests. General source/filter/stored Empty fusion, nested used-binder
simulation and recursive completion remain open. Full Audit passes
{audit['jobs']} jobs and {audit['dependency_checks']} checks. No Haskell patch or new executable
defect is added. Field-pool repair `b9219b9e` remains fixed in `c0cc8a05`.
Read `lean/notes-current-generated-local-rules.md`. Keep this registry first.
Record later repairs with failure, executable reproducer, paths, commit,
checks and upstream status. Preserve every earlier entry.

'''
path = ROOT / 'FINDINGS.md'
text = path.read_text()
header = '## Haskell fix handoff for external work\n\n'
assert text.startswith('# Current formalization findings\n\n' + header)
path.write_text(text.replace(header, header + entry, 1))

note = '# Generated source cases and physical Empty obligations\n\n' + section.split('\n\n', 1)[1]
note += '''## Strongest broad statement

SourceCurrentOuterInitialActual.node_call derives NodeLaw from an actual
successful bounded nodeCall. Context, Frame, Fits, Carrier, inherited
readiness, input availability and scheduled Room remain inputs.
SourceCurrentAllocatedPartialMemoSound.NodeLaw states that the result adds
no accepted finite term. It retains every input term that satisfies the
inherited constraint. Empty inherited constraints therefore give exact
language equality. This is partial correctness of the supported model.
It does not supply all initial semantic source instances or prove that
every call finishes. It does not prove equivalence with all public Haskell.

The full target includes the complete library and intended behavior,
followed by correspondence with the live implementation. Initial query
operand ancestry, active node-owner exclusion, fresh-call bounds, general
recursive completion, repeated convergence, equality resources, host Int
adequacy and complete public Haskell correspondence remain separate work.
No completion percentage or time estimate follows from theorem counts.

## Lexical and node generators

SourceCurrentGeneratedLexicalCases.paired follows the lexical spine in
source order. Reference slots already contain both resolved Generated
directions. Fixed reference captures use equal free-name bindings. Other
fixed captures retain the same complete value and equal free-name maps.
variable_call consumes actual variable build and stored execution calls.
It derives both memberships and equal returned heaps. The returned heaps
need not equal the initial reader. Root filtering is outside this rule.

SourceCurrentGeneratedNodeCases.warm_pair derives fresh-name absence from
issued bounds and availability. The next interned identity occurs in no
live input or raw result. Both root filters are therefore identity calls.
Ready supplies the actual source contexts. The existing filtered source
constructor then gives both generated output directions. The rule needs
actual warm source and stored calls, aliases, paired lexical inputs and
available replacements. It assumes no desired output observation law.

live_child uses an actual source row whose raw children contain no Empty.
Its profile interpreter proves that this row contributes live support.
Each child therefore inherits the parent's scoped alias relation. Its own
actual warm calls give both generated directions. Dead source rows do
not imply these child aliases. The rule does not prove physical Empty
agreement for arbitrary generated pairs or the complete parent Local law.
Both rules require available complete lexical input lists at the reader.
The older Generated.filtered constructor retains historical Context and
raw/filter growth. It does not itself supply these reader-wide lexical
availability facts. The global proof must derive the needed availability
and actual warm child schedules before applying these new rules.

## Union normalization and an allocating subgroup

SourceCurrentGeneratedUnionCases.execute_below transports exact literal
inclusion through actual warm stored calls under one map. Literal atoms
and full rows use the existing execution-parts theorem. Mu remains a full
opaque atom in this inclusion relation. filter_below retains inclusion
under the exact condition member != reference own or parent = reference
own. A bare self member survives alone but is removed from a larger union.
retained_member composes actual makeUnion membership, actual filtering
and actual warm execution. It derives the needed output availability.

The checked subgroup example builds a raw binder from
union[union[self,leaf0,leaf1],leaf2]. The child source union and parent filter
are warm at its actual Ready reader. Filtering the child union still
allocates a new ordinary node. The reader contains the flattened parent
result but need not contain every possible filtered subgroup result.
Warm parent filtering therefore does not imply warm member filtering.
The law does not infer a new Generated.filtered member from missing calls.
Keep the actual intermediate allocation or prepare the needed reader.

## Empty fusion remains open

The checked shape example uses two actual available used Mu values from
one source-built graph. Their decoded shapes are equal, and both physical
roots are nonempty. One stored substitution returns physical Empty. The
other returns a nonempty result. Both actual calls preserve Ready through
Keeps, and the replacement values are available. The example shows that
decoded shape equality alone cannot decide stored-substitution Empty.
It does not establish the same-source Generated premises for those values.

Raw source Empty and profile theorems stop before stored reconstruction.
Stored encoding retains closed Mu values but reconstructs open Mu values
with smart binders. A general proof must connect the actual source,
self-filter and stored calls. It must preserve resolved lexical cases,
scoped aliases, exact self tests and actual selected writer provenance.
The current Generated constructor has Context and growth receipts but
does not itself contain a causal Path from empty. The final semantic law
must retain the needed reachable-reader restriction or derive the needed
writer facts. No counterexample to the full Generated law is claimed.

## Preservation and validation

All 31380 starting tracked files remain. All 3318 older non-Audit Lean
sources, 242 Haskell files and 206 active package files retain their bytes.
Two stashes and three other worktrees retain their metadata. The frozen
manifest chain gains these three production modules. All prior proofs,
repairs, counterexamples, failed attempts, drafts and optimized core remain.

Selected checks use Lean 4.34.1 with five-minute caps. Inner readback
verifies memory.max and memory.high 4294967296 and memory.swap.max0.
Complete public and constructed probes use all eight printer and linter
options. Only propext, Classical.choice and Quot.sound are permitted.
All failed attempts remain unselected. Independent reviews cover the
lexical and node modules. Root reviews both modules and the union laws.
Audit totals are component evidence, not whole-library correctness.
There is no Haskell edit, so Haskell formatters and tests are not needed.
'''
(ROOT / 'lean/notes-current-generated-local-rules.md').write_text(note)
(HERE / 'ROOT-SCOPE.md').write_text(note)
(HERE / 'NEXT.md').write_text('''# Next proof work

Read NEXT-PROMPT.md, HANDOFF.md and FINDINGS.md. Preserve the full library
target, all previous work and the optimized core. Publication awaits the
existing direct approval. Do not retry a push without that approval.

Prove source/filter/stored physical Empty fusion from actual calls and
resolved lexical cases. Do not infer it from decoded shape or raw source
Empty alone. The generated-empty boundary has equal source-built used-Mu
shapes but different post-substitution Empty results. It does not refute
Generated. Retain the same-source relation hypotheses and writer ancestry.

Generated.filtered itself has Context and growth but no Path from empty.
Check whether a reachable common reader supplies all earlier-writer facts
needed by the global theorem. Do not assume a semantic law for arbitrary
Ready records or conclude that such a counterexample has been proved.

Use GeneratedLexicalCases for actual unfiltered variable reconstruction.
GeneratedNodeCases derives mutual child memberships with fresh absent
root-filter names. Use only actual live source rows to inherit aliases.
Derive actual child schedules and row-survival alignment before claiming
the complete node Local clause. Membership alone is not Directed.
Both complete lexical input lists must be available at the reader. Do not
infer that fact from historical Context and raw/filter Grows alone.

GeneratedUnionCases preserves literal Below through actual filtering and
warm reconstruction. Keep its exact bare-self retention condition. The
checked warm-parent/cold-subgroup example rules out automatic warm member
filter extraction. Retain the real intermediate heap or derive preparation.
Do not assume every subgroup normalization is resident at the parent heap.

The complete local source relation must cover reference, row and epsilon
clauses, nested used binders and changing captures. Use directional
normalization chains only after proving each relation's simulation law.
Continue common reader support, initial operand ancestry, active-owner
exclusion, fresh bounds, recursive completion, repeated convergence,
equality resources, host Int adequacy and public Haskell correspondence.
Record every actual Haskell fix first in root FINDINGS with its reproducer,
paths, commit, validation and upstream status. No Haskell fix is added here.
''')
print(json.dumps({'proof': proof, 'component_entries': entries, 'strict_logs': stricts}))
