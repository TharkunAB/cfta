import json
import re
import subprocess
from pathlib import Path

ROOT = Path('/home/tritlo/Code/mcfta')
HERE = ROOT / 'lean/restart-evidence/20261018-open-binder-source-induction'


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
section = f'''## Current recursive unfolding and finite-tree language

Updated: {stamp}. Proof checkpoint is `{proof[:8]}`.
Starting checkpoint is `7f2fdb63`. Main source remains `c0cc8a05`.
Read `lean/notes-current-open-binder-source-induction.md`.

Actual node and union source clauses now derive the strict publication
body hypothesis. Node clauses use indexed strict-child alignment. Union
clauses use indexed strict-member raw root matching, with actual entry
and return heaps and growth. The general active binder clause remains open.

An actual selected Mu writer now constructs its original-reader unfolding
and the sequential ordinary reconstruction. Strict body cases derive
finite agreement. Cases at every depth give one fixed actual schedule
with agreement at all depths. A node writer derives its case from indexed
children. Physical Empty agreement applies to the two reconstructed
results. It is not claimed between a Mu and its unfolding.

A new directional simulation keeps one relation direction through epsilon
steps and mutual membership at ordered row children. Mutual roots give
all finite observations. An actual closed source constructs two canonical
grouped unions with identical observations. No relation containing that
pair satisfies both old global Forward laws. The same pair has a checked
positive instance of the new directional rule. This is a proof-interface
limit. The old conditional theorem remains sound.

Finite observations through a tree's height now determine exact acceptance
for every guard interpretation. Symbols, full guards and child order
remain present. Epsilon paths use actual unfolding at the same reader.
The actual nested-Mu writer example gives one fixed stored schedule whose
ordinary result accepts exactly the same finite trees as the Mu. Its
later requester has different syntax. Its nested used child is closed.
It does not prove general changing-capture binder alignment.

A checked open active-binder counterexample refutes unrestricted separate
readers. All four source and stored calls are warm at one Ready execution
heap. Paired leaf replacements agree at depth zero. The separate reader
has Valid identity caches but explicitly lacks Coherent and Ready. Its
changed node payload makes only one result expose a bare reference. This
does not refute a supported Ready-reader rule or prove that rule sufficient.

The next source proof must construct the directional relation and its
reader support. It must handle nested used binders with changing outer
captures without assuming their desired same-depth result. Earlier writer
syntax stays separate from current requester syntax. Preparation for closed
values does not supply general open support or cold-reader equivalence.

The strongest broad claim concerns the checked implementation model.
A supported successful top-level traversal, empty inherited constraints,
initial semantic facts and scheduled resources give exact equality of the
input and returned finite tree languages. This is partial correctness.
General recursive termination and complete public Haskell correspondence
remain open. Initial query-operand ancestry, all active node-owner
exclusions, fresh-call bounds, repeated convergence, equality resources
and host Int adequacy remain separate obligations.

Full Audit passes {audit['jobs']} jobs and {audit['dependency_checks']} dependency checks.
All {counts['pairs']['new-public']} new public and {counts['pairs']['constructed']} constructed heads pass complete
statement, proof and standard-axiom checks. All {stricts} selected strict
logs are empty. Four canonical builds have no warnings. The boundary
canonical build and Audit retain only the existing ClosedCompletion
warning. {len(components)} component manifests pin {entries} entries. Independent
review finds no material issue. Evidence is in
`lean/restart-evidence/20261018-open-binder-source-induction/`.

No Haskell patch or new executable defect is added. FINDINGS retains the
external repair registry first. Field-pool repair b9219b9e remains fixed
in c0cc8a05. Publication awaits the existing direct approval. No push is
retried. The full-library goal remains active.

'''
authorities = ['NEXT-PROMPT.md', 'HANDOFF.md', 'lean/README.md', 'lean/SYSTEM.md',
               'lean/API-COVERAGE.md', 'lean/COVERAGE.md', 'lean/notes-proof-status-20261017.md']
marker = '## Current filtered finite source reconstruction\n'
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
Actual source node and union cases derive strict publication body cases.
Selected Mu writers construct actual finite unfolding equations at the
original reader. All finite observations now imply exact guarded finite-tree
language. The checked nested writer example derives that language equation.
Actual canonical unions refute the old two-way simulation interface and
admit the new directional rule. A separate Valid but explicitly incoherent
reader refutes unrestricted reader alignment. These are proof-interface
limits, not Haskell defects. General changing-capture binder alignment,
source simulation, reader support and recursive completion remain open.
Full Audit passes {audit['jobs']} jobs and {audit['dependency_checks']} checks. No Haskell patch
or new executable defect is added. Field-pool repair `b9219b9e` remains
fixed in `c0cc8a05`. Read `lean/notes-current-open-binder-source-induction.md`.
Keep this registry first. Record each later repair with failure, executable
reproducer, paths, commit, checks and upstream status. Preserve earlier entries.

'''
path = ROOT / 'FINDINGS.md'
text = path.read_text()
header = '## Haskell fix handoff for external work\n\n'
assert text.startswith('# Current formalization findings\n\n' + header)
path.write_text(text.replace(header, header + entry, 1))
note = '# Recursive unfolding equations and guarded finite-tree language\n\n' + section.split('\n\n', 1)[1]
note += '''The production modules are SourceCurrentPublicationBodySourceCases,
SourceCurrentRetainedMuFiniteUnfoldEquation,
SourceCurrentOpenPreorderSimulation, SourceCurrentOpenObservationLanguage
and SourceCurrentOpenBinderObservationBoundary. Audit adds only these
five imports. All 30595 starting tracked files remain. All 3305 older
non-Audit Lean sources, 242 Haskell files and 206 active package files
retain their bytes. Two stashes and three other worktrees retain their
metadata. Preservation checks 162 frozen manifests with 1068 module
entries. All earlier proofs, repairs, counterexamples, drafts and the
optimized core remain unchanged.

The actual grouped-union fixture uses u=union[MuA,MuB,z] and
v=union[merge(A,B),z]. Both are canonical outputs of actual source calls.
The bare reference z prevents the flat makeUnion[A,B,z] fast path from
merging A and B. Do not replace the checked grouped schedule with that
flat schedule. Actual unfolds of MuA and MuB expose A and B at the same
reader. Exact reachable sets prove both the old obstruction and the new
positive directional instance. The relation need not be transitive.

The retained-writer fixture has an actual used outer Mu, a self child,
and a closed nested used Mu. Every indexed source child has a proper
reference or closed-source proof. A later reordered and duplicated body
selects the same earlier writer. The finite language theorem aligns all
depth-specific schedules by equality of actual outcomes. It keeps the
original reader. No cold-to-prepared equality or changing-capture source
instance follows from this fixture.

The separate-reader counterexample starts with a closed two-leaf source.
Actual open source builds, two stored calls and one unfold construct its
Ready execution heap. Replay gives all four warm calls there. The tested
source is binder true(node[2 false[var0,var1]]). Only the separate view's
node payload is changed. Cache identity validity remains, but payload
coherence and Ready fail explicitly. This is not a Haskell repair request.

Selected jobs use pinned Lean 4.34.1, 4 GiB maximum and high limits,
zero swap and five-minute caps. Complete public probes use all eight
printer and linter settings. The only allowed axioms are propext,
Classical.choice and Quot.sound. Failed attempts remain unselected and
preserved. Component checks do not establish whole-library correctness.
'''
(ROOT / 'lean/notes-current-open-binder-source-induction.md').write_text(note)
(HERE / 'ROOT-SCOPE.md').write_text(note)
(HERE / 'NEXT.md').write_text('''# Next proof work

Read NEXT-PROMPT.md, HANDOFF.md and FINDINGS.md first. Preserve full
library scope and all earlier work. Publication awaits direct approval.

Construct a source-derived relation for OpenPreorderSimulation.Directed.
Use actual paired source and stored execution endpoints. Seed mutual
self membership from actual binder endpoints before proving the local
simulation law. Do not assume Same for the pair being proved. Ordered
matched row children need mutual membership. Epsilon intermediate states
need only the directional relation. The old global two-way Forward
interface cannot cover the checked canonical grouped-union example.

Construct the actual reader support required by that source instance.
The unrestricted arbitrary-view AlignedAt binder clause is false. The
checked counterexample is explicitly noncoherent and nonReady. It does
not establish a counterexample at a supported Ready reader, or prove
that Ready alone suffices. Closed-value preparation supplies support only
at its final reader. It does not transport input observations from a cold
reader or automatically cover open values.

PublicationBodySourceCases.node derives BodyIH from indexed strict-child
alignment. Its union rule requires indexed strict-member raw RootMatch,
actual contexts and raw-return growth into the execution heap. Mu atom
execution remains a full-depth obligation. A lower-depth row-child case
does not discharge it. General nested used binders with changing outer
captures remain the main source clause to prove.

RetainedMuFiniteUnfoldEquation constructs the real original-reader unfold
and sequential ordinary reconstruction from strict body cases. Its node
corollary derives the body case from children. all_depths fixes one actual
schedule. OpenObservationLanguage.finite/all_depths turn those observations
into exact guarded finite-tree language. Do not infer physical Empty
agreement between a Mu and its unfolding. Earlier writer syntax can differ
from the current requester. Each writer bridge uses its own source body.

Initial query-operand ancestry, all active node-owner exclusions, fresh-call
bounds and general recursive completion remain open. Repeated convergence,
equality resources, host Int adequacy and public Haskell correspondence
retain separate contracts. The broad outer theorem is partial correctness
for a supported successful run from initial facts and scheduled resources.

Use verify-checkpoint.py and verify-preservation.py. After a clean local
commit, run verify-closure.py with output outside this directory. Preserve
all attempts and marked drafts. Record actual Haskell repairs first in
root FINDINGS with failure, executable repro, paths, commit and validation.
''')
print(json.dumps({'proof': proof, 'components': len(components), 'component_entries': entries,
                  'counts': counts, 'audit': audit}))
