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
audit = read('selected-audit.json')
components = read('component-manifests.json')
entries = sum(len(read(name).get('entries', read(name).get('files', []))) for name in components)
section = f'''## Current recursive Empty fusion and exact union coverage

Updated: {stamp}. Proof checkpoint is `{proof[:8]}`.
Starting checkpoint is `0b1a176b`. Main source remains `c0cc8a05`.
Read `lean/notes-current-filtered-empty-fusion.md`.

Actual source builds, root filters and stored calls now derive physical
Empty agreement under nonempty resolved replacements. The publication
and binder endpoints recover the selected earlier writer and derive
Empty agreement for its actual body and ordinary reconstructions. They
retain the real calls, Keeps, availability and both Generated directions.
The used-Mu example selects an earlier writer with different source syntax.

Node reconstruction now derives opposite stored-row survival and parent
Empty agreement from fusion of strict source children. The complete row
symbol, guard and ordered child Empty tests are retained. Child schedules
and live aliases come from the actual parent calls. The proof needs no
reader-wide lexical availability or desired parent output law.

An actual source return followed by Keeps now derives the original
lexical Context at the later reader. Union preparation retains that
Context and all adjacent source, filter and stored calls at its final
heap. The existing Generated.filtered constructor is used unchanged.
An unused issued capture and a cold subgroup filter are checked. Plain
Grows still does not supply the older writer's issued-name suffix.

Filtered union reconstruction now has exact literal-atom and full-row
coverage by retained original source members. The parent is physically
Empty exactly when every retained member reconstruction is Empty. A bare
self member is retained only when the entire parent is that bare self.
A source-built example has an Empty parent and an excluded self member
whose reconstruction is a nonempty used Mu. Both new laws are applied.

The strongest broad theorem remains conditional finite-language
preservation for a successful supported checked-model traversal with an
empty list of inherited constraints. Initial semantic cache and recursive
heap assumptions, plus computed resource bounds, remain explicit. General
two-sided source/filter/stored fusion and changing-capture simulation
remain open. So do arbitrary older-writer issued-history transport,
recursive completion, repeated convergence and public Haskell correspondence.

Full Audit passes {audit['jobs']} jobs and {audit['dependency_checks']} dependency checks.
All 10 new public and 4 constructed heads pass full statement, proof and
standard-axiom checks. Eight selected strict logs are empty. All four
canonical builds are warning-free. Audit retains only the existing
ClosedCompletion warning. Five selected manifests pin {entries} entries.
Independent union-coverage review finds no material issue. Evidence is
in `lean/restart-evidence/20261018-filtered-empty-fusion/`.

No Haskell patch or new executable defect is added. FINDINGS retains the
repair registry first. Field-pool repair b9219b9e remains fixed in c0cc8a05.
Publication awaits the existing direct approval. No push is retried.
The full-library goal remains active.

'''
authorities = ['NEXT-PROMPT.md', 'HANDOFF.md', 'lean/README.md', 'lean/SYSTEM.md',
               'lean/API-COVERAGE.md', 'lean/COVERAGE.md', 'lean/notes-proof-status-20261017.md']
marker = '## Current stored Empty transport and cold union preparation\n'
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
Actual selected-writer binder reconstructions now derive physical Empty
agreement. Node rows derive opposite survival and parent Empty from strict
source child fusion. Actual Keeps supplies the original lexical Context
and adjacent prepared union-member calls. Exact filtered-union coverage
derives the parent Empty criterion with the bare-self exception. The
checked Empty-parent/nonempty-excluded-self example is expected behavior,
not a Haskell defect. General fusion, changing-capture simulation and the
older writer's issued suffix remain open. Full Audit passes {audit['jobs']} jobs
and {audit['dependency_checks']} checks. No Haskell patch or new executable defect is added.
Field-pool repair `b9219b9e` remains fixed in `c0cc8a05`. Read
`lean/notes-current-filtered-empty-fusion.md`. Keep this registry first.
Record later repairs with failure, executable reproducer, paths, commit,
checks and upstream status. Preserve every earlier entry.

'''
path = ROOT / 'FINDINGS.md'
text = path.read_text()
header = '## Haskell fix handoff for external work\n\n'
assert text.startswith('# Current formalization findings\n\n' + header)
path.write_text(text.replace(header, header + entry, 1))

note = '# Recursive Empty fusion and exact filtered-union coverage\n\n' + section.split('\n\n', 1)[1]
note = note.replace('Read `lean/notes-current-filtered-empty-fusion.md`.\n', '')
note += '''## Actual nonempty replacement and binder calls

SourceCurrentFilteredNonemptyFusion.filtered compares two actual builds
of the same full source expression with symbolic lexical inputs. Varying
reference inputs are physically nonempty. Fixed captures are identical.
The source Empty abstraction therefore gives matching raw tests. Existing
InternedFilterEmptiness.filter_empty_iff retains each test through its
actual root filter. Nonempty stored replacement then gives output Empty
agreement. The source and stored entry heaps can differ. Initial stored
availability and replacement availability remain explicit.

The publication endpoint uses actual raw callback schedules and initial
availability of the selected complete Mu. Single self-replacement maps
resolve to the physically nonempty Mu or to a literal reference. The
binder endpoint recovers the actual selected writer through causal Path.
It retains the selected record, Written witness, sequential and warm
unfold/ordinary calls, Keeps, output availability and both Generated
directions. It adds derived Empty agreement. The integration has a used
earlier author and a later requester with different source syntax.

This closes the physical Empty obligation for those actual binder maps.
It does not prove all finite observations, guard-depth profile agreement,
the Local simulation clauses or arbitrary changing-capture substitution.

## Node Empty from strict source children

SourceCurrentGeneratedNodeEmpty.Fusion states the unfiltered two-sided
actual source/stored Empty law. It retains historical Contexts, actual
source calls and Grows into one Ready reader. Actual raw inputs and
replacement records must be available there. Scoped aliases and paired
lexical Inputs remain explicit. The predicate assumes no output law.

The row endpoint uses Fusion only for strict children of indexed source
rows. The earlier NodeSchedules producer supplies opposite raw-row
survival, original RowCall receipts and all stored child schedules. Live
source support supplies each child alias relation. Actual stored rows are
aligned by deterministic child and edge calls. Ordered child Empty tests
then give opposite stored-row survival, with the same full symbol and
guard. The node endpoint applies both directions and derives parent Empty.

No global Generated-to-Empty hypothesis is assumed. No whole lexical
availability at the reader is assumed. The cold-node integration contains
a dead row and two surviving rows. It derives strict child fusion for its
closed leaf and Empty children and invokes both row and node endpoints.
It does not claim a varying-capture or nested-Mu integration.

## Genuine adjacent calls after union preparation

SourceCurrentGeneratedHistoricalContext.replay combines the actual source
call's issued history with a real subsequent Keeps. It derives complete
availability of the original lexical inputs, their Context at the reader,
whole Keeps from the original entry and exact source replay. The stronger
union_prepare endpoint derives raw parent availability from the actual
call. It retains the prepared original member schedule and parent calls,
plus Context for the original lexical list at the final reader and all
indexed source builds there. Each final source, filter and stored call can
use the same literal final heap as every historical endpoint.

The integration retains an unused interned reference whose issued key
comes from actual source construction. The first subgroup filter starts
cold. At the final heap it applies the unchanged Generated.filtered
constructor with the derived original Context and literal adjacent calls.
It uses no reflexive generator shortcut for that membership.

This requires actual issued-name retention. The general Generated witness
and the older writer's Written suffix retain only four-table Grows. That
does not imply preservation of unused issued captures. Derive a genuine
issued suffix from actual chronology before using this producer there.
Do not silently strengthen Grows or assume a later lexical Context.

## Exact filtered union coverage

SourceCurrentFilteredUnionCoverage.parts starts with actual warm
makeUnion, parent filter and stored calls, plus available original raw
members and available replacements. Each original member has an actual
warm filter and stored call. Finite preparation supplies those calls.
A warm parent alone does not imply their existence at the initial reader.

The result characterizes every literal atom and complete ordinary row of
the parent output by an actual retained original member output. A member
is retained when it is not the bare own reference, or when the complete
parent is itself that bare reference. The parent-bare case derives both
literal uniqueness and absence of ordinary rows before applying bare_iff.
The row case retains actual RowCalls and the full live-child test. Mu
atoms remain complete opaque records at this literal layer.

The empty_iff endpoint derives output availability and uses normalized
root parts to characterize physical Empty. The parent is Empty exactly
when every retained actual member output is Empty. The integration builds
a used Mu from source, then a two-reference raw union. Its own reference
maps to the Mu and the other reference maps to Empty. Actual preparation
supplies the calls. The parent filter removes own and the parent output
is Empty. The excluded bare-own member independently returns that nonempty
Mu. Both parts and empty_iff are invoked on the derived final schedules.
Omitting the retention exception would make this example a counterexample.

## Remaining full-system obligations

Combine the strict-child node law, filtered variable law, actual binder
Empty result and exact union coverage into general two-sided fusion.
Union composition must align the retention conditions under the scoped
alias and self tests. The relation still needs the reference, row and
epsilon Local clauses before membership gives a Directed simulation.
Keep selected earlier writer bodies and actual chronological support.
General changing-capture observation and guard-depth profile agreement
remain open. Those semantic instances are needed for initial recursive
heaps, beyond valid identities and numeric resource bounds.

SourceCurrentOuterInitialActual.node_call remains the strongest broad
conditional traversal result. With initial semantic cache/recursive-heap
invariants and the computed resource bound, a successful call started
with inherited payload some [] preserves exactly the input finite-tree
language. Payload none denotes contradiction. The proof does not construct
all these premises from arbitrary source inputs or public Haskell calls.

Preserve the full remaining scope: initial query operands and public source
ancestry, active-owner exclusion, fresh bounds, arbitrary open-Mu reader
support, recursive completion, repeated convergence, equality-operation
resources, host Int adequacy and full public Haskell correspondence.

All 32031 starting tracked files remain. All 3329 older non-Audit Lean
sources, 242 Haskell files and 206 active package files retain their bytes.
Two stashes and three other worktrees retain their metadata. Preservation
extends 168 frozen manifests with four modules. Every earlier proof,
counterexample, repair, draft, failed attempt and optimized core remains.

Selected runs use Lean 4.34.1 with five-minute caps. Inner readback verifies
memory.max and memory.high 4294967296 and memory.swap.max 0. Complete public
and constructed probes use all eight required printer and linter options.
Only propext, Classical.choice and Quot.sound are permitted axioms. Every
failed or warning attempt remains unselected. No Haskell file changes,
so Haskell formatters and tests are not needed for this batch.
'''
(ROOT / 'lean/notes-current-filtered-empty-fusion.md').write_text(note)
(HERE / 'ROOT-SCOPE.md').write_text(note)
(HERE / 'NEXT.md').write_text('''# Next proof work

Read NEXT-PROMPT.md, HANDOFF.md and FINDINGS.md. Preserve the full-library
goal and all prior work. Publication awaits existing direct approval.
Do not retry a push without that approval. Keep Haskell fixes first in
root FINDINGS with reproducer, paths, commit, checks and upstream status.

Reuse FilteredNonemptyFusion.filtered/publication/binder. Actual selected
writer body and ordinary reconstructions now have derived physical Empty
agreement under their actual nonempty self maps. General observation and
guard-depth profile agreement remain separate. Do not redo root-filter
Empty preservation; InternedFilterEmptiness already proves it.

GeneratedNodeEmpty gives Fusion for source nodes from strict child Fusion,
plus exact opposite stored-row survival. GeneratedHistoricalContext uses
actual issued history and Keeps to derive original lexical Context and
adjacent final source/filter/stored calls. Its constructed example applies
unchanged Generated.filtered despite a cold subgroup and unused issued
capture. Arbitrary Grows and the older writer's suffix do not supply the
needed issued-name retention. Derive it from actual chronological events.

FilteredUnionCoverage supplies exact literal atoms/full rows and the
physical Empty criterion for all retained original member outputs. Reuse
actual finite preparation for its warm member calls. Retain the exception:
bare self contributes only when the entire parent is bare self. A checked
Empty-parent/nonempty-excluded-own-Mu example requires this condition.

Complete general two-sided source/filter/stored Empty fusion and Local
reference, row and epsilon clauses. Align union retention under live
aliases/self tests. Use actual earlier writer bodies for changing captures.
Do not replace the desired laws by assumed Same, Empty or BodyIH. Continue
the full initial-operand, open-Mu support, active-owner, fresh-bound,
completion, convergence, equality-resource, host-Int and Haskell scope.
No new Haskell fix is added in this batch.
''')
print(json.dumps({'proof': proof, 'component_entries': entries, 'strict_logs': 8}))
