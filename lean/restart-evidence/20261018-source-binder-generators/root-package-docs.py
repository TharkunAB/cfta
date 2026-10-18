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
section = f'''## Current source-generated binder pairs

Updated: {stamp}. Proof checkpoint is `{proof[:8]}`.
Starting checkpoint is `9f6230d5`. Main source remains `c0cc8a05`.
Read `lean/notes-current-source-binder-generators.md`.

An actual source binder and causal reader history now derive both
comparison-generator directions for the selected earlier writer's body
and ordinary reconstruction. Generated contains equality and genuine
filtered source calls. It assumes no desired output Same, Directed or
BodyIH law. Its lexical reference slots retain both generated directions.
Historical contexts, live aliases, self-filter tests, actual calls,
availability, forward growth and warm replay remain explicit. The earlier
writer can have different syntax from the requester.

An actual node-body Mu unfold now extends WarmSupport from indexed strict
original stored-child support. Each child must return old support or the
same recursive Mu. The producer constructs the unfolding, final Keeps,
availability and warm replay. A checked source-built open used Mu with
positive stored-plan depth grows the node cache and gains this support.
This does not prepare arbitrary open Mu records or solve all child cases.

Finite reflexive transitive closure and disjunction preserve genuine
Directed simulations. Complete guards and ordered mutual child relations
remain present. These closure laws do not prove an unproved generator.

A productive source-built example uses two distinct equivalent captures.
The same open binder source returns distinct used outer Mu values at one
Ready reader. Each nested used Mu captures its own distinct outer Mu.
A finite actual simulation proves all finite observations for both input
captures and returned values. It gives exact finite language for every
guard interpretation. A nullary accepted tree proves productivity. This
is one example, not a general changing-capture source theorem.

The main remaining proof must establish local source and self-filter
simulation rules for Generated, including physical row-survival alignment
and nested used binders. Membership extraction alone is not Directed.
Automatic arbitrary open-Mu support remains open. General termination,
initial query operands, active-owner exclusion, fresh-call bounds,
repeated convergence, equality resources, host Int adequacy and complete
public Haskell correspondence remain separate obligations.

The strongest broad claim remains conditional partial correctness of the
checked implementation model. A supported successful traversal with
empty inherited constraints, initial semantic facts and scheduled
resources preserves exactly the accepted finite trees. The required
source semantic instances remain explicit.

Full Audit passes {audit['jobs']} jobs and {audit['dependency_checks']} dependency checks.
All {counts['pairs']['new-public']} new public and {counts['pairs']['constructed']} constructed heads pass complete
statement, proof and standard-axiom checks. Seven selected strict logs
are empty. All four canonical builds are warning-free. Audit replays only
the existing ClosedCompletion warning. Six component manifests pin
{entries} entries. Independent review finds no material issue. Evidence is
in `lean/restart-evidence/20261018-source-binder-generators/`.

No Haskell patch or new executable defect is added. FINDINGS retains the
repair registry first. Field-pool repair b9219b9e remains fixed in c0cc8a05.
Publication awaits the existing direct approval. No push is retried.
The full-library goal remains active.

'''
authorities = ['NEXT-PROMPT.md', 'HANDOFF.md', 'lean/README.md', 'lean/SYSTEM.md',
               'lean/API-COVERAGE.md', 'lean/COVERAGE.md', 'lean/notes-proof-status-20261017.md']
marker = '## Current supported source simulation\n'
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
Actual selected writer source calls now derive both reconstruction-generator
directions. The relation assumes no desired output observation law. Both
lexical reference directions, live aliases and exact self-filter tests
remain explicit. Actual node-Mu unfoldings gain reader support from strict
original-child support. A source-built open positive-depth used Mu checks
this producer. A productive nested example with distinct equivalent
captures has all finite observations and exact guarded finite language.
Finite closure preserves genuine Directed simulations. General generated
local rules, row-survival alignment, changing-capture binder congruence
and arbitrary open-Mu preparation remain open. These are proof results,
not executable Haskell repair requests. Full Audit passes {audit['jobs']} jobs and
{audit['dependency_checks']} checks. No Haskell patch or new executable defect is added.
Field-pool repair `b9219b9e` remains fixed in `c0cc8a05`. Read
`lean/notes-current-source-binder-generators.md`. Keep this registry first.
Record later repairs with failure, executable reproducer, paths, commit,
checks and upstream status. Preserve every earlier entry.

'''
path = ROOT / 'FINDINGS.md'
text = path.read_text()
header = '## Haskell fix handoff for external work\n\n'
assert text.startswith('# Current formalization findings\n\n' + header)
path.write_text(text.replace(header, header + entry, 1))

note = '# Source-generated binder pairs and actual open support\n\n' + section.split('\n\n', 1)[1]
note += '''The production modules are SourceCurrentDirectedClosure,
SourceCurrentCommonReaderBinderSupport, SourceCurrentRetainedMuDirectedCase
and SourceCurrentChangingCaptureBinderExample. Audit adds only these
four imports. Public counts are eight, one, eight and one. The three
separate constructed probes cover actual normalization closure, an open
positive-depth used Mu, and a genuinely used earlier writer selected by
different requester syntax. The production changing-capture example is
counted once as a public head. It is not counted as another constructed
probe.

All 31120 starting tracked files remain. All 3314 older non-Audit Lean
sources, 242 Haskell files and 206 active package files retain their bytes.
Two stashes and three other worktrees retain their metadata. Preservation
checks 164 frozen manifests with 1076 module entries. All earlier proofs,
repairs, counterexamples, failed attempts, drafts and optimized core remain.

## Generated comparison pairs

Generated is mutually inductive with a lexical Inputs spine. Equality
supplies reflexive membership. The filtered constructor retains one source
syntax and two symbolic lexical instantiations. Its recursive reference
slots contain Generated membership in both directions. Identical opaque
captures retain equal bindings on free names. This does not assert that
all generated outputs already satisfy physical Empty agreement.

The constructor also retains actual historical source Context values,
scoped alias correspondence, exact live self-filter tests, two raw builds,
two actual filters, forward raw and filtered growth, ready final data,
available filtered values, replacement availability, warm source/filter
replays and actual effect-free stored executions. No arbitrary pair or
output-equivalence constructor is added. Positivity uses the explicit
mutual lexical spine. Failed direct attempts remain preserved.

The binder producer starts with a real source binder call, its initial
Context, forward Keeps into the reader and a causal Path from empty.
RetainedProbeSchedule recovers the full selected record and one actual
prior writer event. Its own raw callbacks and source expression supply
the filtered generator. Live ordinary and reserved-name freshness derive
the self tests. Actual shared replacements derive paired lexical inputs
by reflexivity. Both output membership directions follow at the actual
final reconstruction heap. Missing publication, four path cuts, exact
selected payloads, original-reader and final-reader epsilon membership,
actual unfolds and warm reconstruction calls remain explicit. Earlier
writer syntax is not equated with current requester syntax.

A general proof must now derive the local reference, row and epsilon
clauses for these constructors. Reference inputs have the needed mutual
membership. Row survival still needs physical Empty alignment. Nested
used Mu and literal root filtering retain their full obligations. Do not
infer Directed from Generated merely because the selected writer pair
has generator membership. Do not add Same or BodyIH for the target pair.

## Reader support

The node-Mu support theorem constructs a real stored unfolding from Ready
and availability. Actual row-call expansion and survivor inversion recover
the original stored child for each returned row child. Its support premise
uses that strict original child, a later Keeps extension and the actual
warm child execution. It allows old support or the same recursive Mu.
The final enlarged support includes the old support, Mu and returned
ordinary node. Replay derives settlement. Existing support moves forward
through WarmSupport.grows. No whole successor-support oracle is assumed.

The open example starts from an actual source binder with self and an
external primitive marker. It derives Ready, availability, nonempty free
names, positive stored-plan depth and usesLocal=true. Literal reference
executions discharge both strict-child cases. Its cold unfold allocates
a new node. The final support and warm replay therefore extend the prior
zero-depth preparation result. General arbitrary nested open-Mu support
still requires its actual strict-child induction proof.

## Productive changing captures

The input captures are a nullary ordinary node A and a raw closed unused
Mu around A. They are physically unequal but have all finite observations
at the actual common reader. One open source binder uses either capture.
The returned outer Mu values differ. Their nested used Mu values differ
as well, and their actual unfolding rows contain their own corresponding
outer Mu. This is a real change to an outer capture beneath a used binder.

The actual reader follows the source build and five unfoldings. A finite
relation contains equality and five explicit pairs in both directions.
Every complete physical row and actual epsilon step has a checked clause.
Inner row children retain the ordered inner, outer and input-capture
pairs. This establishes Directed before deriving finite observations or
language. All four used-local facts, exact warm source calls, input/output
availability, distinctness and the inner outer-capture children are in
the public witness. Nullary symbol2 acceptance proves finite productivity.
The language theorem quantifies over every interpretation of the complete
Boolean guard. The example does not prove the general generated relation.

## Validation and continuation

All selected checks use Lean 4.34.1 under a five-minute cap. Inner readback
verifies memory.max and memory.high 4294967296 and memory.swap.max0.
Every selected complete probe has the eight required printer and linter
options. Only propext, Classical.choice and Quot.sound are allowed.
The full Audit checks private theorem dependencies too. Seven strict logs
have exactly zero bytes. All failed or interrupted attempts remain intact
and unselected. The root executable diagnostic hit its time cap; the
kernel-checked final example passes. Audit totals are component evidence,
not a proof of whole-library Haskell correspondence or termination.

Root independently reviews the complete directional closure and retained
source generator. Separate frozen reviews cover the node-Mu support and
the changing-capture certificate. The six component manifests retain
explicit source and receipt pins. Read root-reviewed-components.md for
the complete root review boundary. Preserve all earlier work and record
actual Haskell fixes first in FINDINGS. No Haskell fix is added here.
'''
(ROOT / 'lean/notes-current-source-binder-generators.md').write_text(note)
(HERE / 'ROOT-SCOPE.md').write_text(note)
(HERE / 'NEXT.md').write_text('''# Next proof work

Read NEXT-PROMPT.md, HANDOFF.md and FINDINGS.md first. Preserve full library
scope and all earlier work. Publication awaits the existing direct approval.

Prove the local source and literal self-filter clauses for the actual
RetainedMuDirectedCase.Generated relation. It contains equality and genuine
filtered source reconstruction receipts, not desired output observations.
Inputs.reference retains both resolved Generated directions. Actual writer
source callbacks derive both body/probe generator memberships. Keep that
writer's own expression, actual path and selected complete record.

Derive physical row-survival alignment along with the needed source clauses.
Do not assume physical Empty agreement for arbitrary normalization pairs.
Node source cases already derive Local from strict source-child calls.
Union and root-filter cases need exact literal parts, full guards, ordered
children and actual execution endpoints. General nested used-Mu source
simulation remains the main missing clause. Membership alone is not Directed.

DirectedClosure.directed composes only genuinely proved Directed relations.
Its disjunction law likewise needs both genuine simulations. These rules
permit later normalization chains; they do not prove an unproved source
generator automatically. Literal Below can be directional. Keep both
source-child directions where row comparison requires them.

CommonReaderBinderSupport.node constructs an actual node-body Mu unfold
and final WarmSupport from strict original-child support-or-self cases.
Its positive-depth open example is checked. General open-Mu preparation
still needs the actual child induction. The prior Ready-only counterexample
lacks a compared output at its separate reader. It does not refute a common
supported later heap or full output availability.

ChangingCaptureBinderExample.witness is a real productive nested example
with distinct equivalent input captures and distinct outer/inner used Mu
values. It proves all finite observations and exact guarded finite language
at its constructed common reader. It is not the general source theorem.

Keep initial query operands, active-owner exclusion, fresh-call bounds,
recursive termination, repeated convergence, equality resources, host Int
adequacy and public Haskell correspondence in scope as separate contracts.
The broad traversal theorem remains conditional partial correctness with
explicit initial semantic facts, resources and empty inherited constraints.

Use verify-checkpoint.py and verify-preservation.py. After the local
checkpoint commit, run verify-closure.py with output outside this directory.
Preserve every failed attempt and marked draft. Keep Haskell repairs first
in FINDINGS with executable repro, paths, commit, checks and upstream status.
''')
print(json.dumps({'proof': proof, 'components': len(components), 'component_entries': entries,
                  'counts': counts, 'audit': audit}))
