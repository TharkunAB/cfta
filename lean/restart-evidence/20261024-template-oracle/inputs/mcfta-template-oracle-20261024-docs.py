import hashlib
import json
from pathlib import Path

root=Path('/home/tritlo/Code/mcfta')
area=Path('/tmp/mcfta-template-oracle-20261024')
(root/'lean/notes-current-template-oracle.md').write_text('''# Concrete template oracle observations

Updated: 2026-10-24. Start: `b6ab4f035cc7fd5f98f447e1d0cbc9446d29c2f7`.
Proof: `eae961a679a76ce4c94cea3cad3fd90ae99eb404`.
Imported main: `0db62d26b87e8e55b6c2719f6312ece6f93ed31b`.

## Checked source model

SourcePruningTemplates reuses the existing full source alphabet:
SourceObservations.Label FullSyntax.Formula. It keeps complete names and
refinements in patterns, terms, fixed-head keys and returned checks. The
ordinary app, filter and arrow literals require their exact top refinement.
The model adds no symbol, pattern or term datatype. The existing executable
formula equality supplies full-label comparison. Preliminary String drafts
are retained as history. They are not the installed alphabet.

The pure helpers retain the actual program traversal, raw template and term
spines, structural early-template conversion, fragment view, match production,
check combination and raw pending-ID expansion order. The indexed catalog
uses original position tags, generic and fixed-head finite buckets, left-biased
lookup union and ascending original positions. Unknown heads retain the exact
original catalog. Repeated templates and interleaved generic entries remain.
Known/unknown equations expose this exact finite-map observation model.
Native IntMap/Map implementation, Text/interning realization and bounded Int
positions or spine counts remain separate correspondence obligations.

SourcePruningOracle instantiates the existing Oracle type with this alphabet
and the list of pending checks. It preserves all source branch priorities.
A Right event returns false and the original checks without a state read.
An early-rejected Left fragment returns true and the original checks. With no
pending checks, a concrete root outside ordinary app/4 and filter/2 returns
false and no checks. An unresolved hole does not take that concrete fast path.

The remaining branch first executes the existing partial renderer. It then
runs the complete ordered traversal of actual Pruning.resume actions. Only
after those reads does it combine resumed checks and new indexed matches.
Resumed results precede started results. Each new program precedes the matches
for later programs, with templates in catalog order. A failed match is dropped.
A completed match sets the prune flag. Other nonempty checks remain, in order
and with duplicates, even when the returned flag is true. Neither result skips
later stateful reads. All supplied raw IDs and the raw current remain explicit.

## Observation guarantees

oracle_inr states the literal pre-expansion action equation. oracle_frame
preserves the complete modeled compression Frame after every successful call.
It retains the counter, values, obligations, both ancestry fields, and every
root representative with its exact stored size. Parent paths can differ.

oracle_agrees gives exact result equality and a complete final frame for
successful calls from framed inputs at independent bounds. The graph, catalog,
event, current and pending input are the same. Left forest totality is explicit.
The complete frame derives totality at each related intermediate state.

oracle_transport constructs a finite matching callback from one actual left
success. Right success is not a premise. It constructs the actual right render
endpoint, then every ordered resume endpoint. Raising both stages to the sum
of their finite bounds keeps those exact endpoints. Pure branches use zero.
oracle_moreFuel retains the exact result and complete final state.

No Safe, Finished, canonical-current, encoding-validity, desired-output,
arbitrary matcher or arbitrary candidate-selector premise is supplied.
Totality alone does not prove that an arbitrary partial render terminates.
The theorem does not compare bounded error rows, callback traces, complete
result streams or native machine states.

## Remaining work

This result covers callback observations. It does not prove pruning soundness,
that early marker erasure is safe for every encoding, or that the producer's
templates describe redundant programs. The source caller's app/4 type-constructor
guard and the LPO producer repairs still need their semantic composition.
A finite-map observation model is not a verified native-container extraction.

Next model recordTypes and typedTypes, including type-position bookkeeping,
openProgram, the actual typing update, and ordered unexpanded-node reads.
Retain the source open-hole order, both ancestry fields and actual intermediate
states. Then compose the concrete callbacks with canonical mutation histories,
selected-current protection and the cached enumeration driver. General pruning,
typing, phase-4 and whole-pipeline correctness remain open.

H6 SourceCurrentColdFiniteWarmCalls.constructed_node_calls remains strongest
combined. Its covered closed construction, valid allocation history, formal
guards and sufficient mathematical width/fuel supply finite repeated node calls
with exact finite-tree language preservation. It excludes withoutRedundantEdges
and does not assert convergence. Complete resources, practical-width and
Haskell/solver correspondence remain open. H23 is still queued. The full goal
is active and incomplete.

## Validation and preservation

Pinned Lean 4.34.1 checked both final sources with warnings as errors and all
linters. The helper's first check needed the generated fragmentTerm equation
instead of reflexivity. The callback's first check reported deprecated
conditional-lemma names and an unused private existential binder. The repairs
change no executable definition or public statement. All attempts remain.
The complete preliminary drafts and exact full-symbol correction patches remain.
An author-review line citation extends beyond Pruning.hs; the independent
review records the correct fragmentTerm lines 348 to 350. Code is unaffected.

The installed aggregate Audit passed: 3675 jobs and 75838 dependency checks.
It replayed the older unused-variable warning at
InternedFreshOrdinaryClosedCompletion.lean:24. No new-source warning occurs.
All 27 public signatures and 13 axiom reports were read in full. Their axiom
sets use only propext, Classical.choice and Quot.sound. These are standard
Lean core axioms. Two empty-list lemmas have no axioms. No project axiom or
proof-limit override is introduced.

The initial pull passed. Main remains 0db62d26b and is incorporated. No Haskell
source changed, so no Haskell tests or formatter checks were repeated. FINDINGS
keeps the external repair index first and the merged LPO status unchanged.
Evidence is in restart-evidence/20261024-template-oracle. The verifier checks
every original baseline file and permits only the nine exact status insertions
and one Audit import. Earlier proofs, repairs, counterexamples, marked drafts,
optimized interned code and sealed evidence remain. This record precedes the
evidence commit and authorized push to formalize.
''')
prefix='''
## Concrete template oracle observation proof

Updated: 2026-10-24. Proof: `eae961a679a76ce4c94cea3cad3fd90ae99eb404`.
Start: `b6ab4f035cc`. Main remains `0db62d26b` and is incorporated.
Read `lean/notes-current-template-oracle.md`.

The actual templateOracle callback now has checked frame, agreement, fuel
retention and finite-transport proofs. Its pure fast paths and actual partial
render followed by every ordered resume read retain the source branch order.
The result keeps exact prune flags, ordered checks, raw IDs and duplicates.
Full labels retain refinements. Candidate buckets use original positions and
the ascending generic/fixed union. No arbitrary matcher or selector is supplied.
No Safe, completion, canonical-current or desired right-success premise is added.

Both final sources passed strict Lean checks. Audit passed: 3675 jobs and
75838 dependency checks, one older warning and no new-source warning.
All 27 public signatures and 13 axiom reports were read. Only the existing
core axioms propext, Classical.choice and Quot.sound occur. Earlier drafts,
full-symbol corrections and both failed check attempts remain in the evidence.
No Haskell source changed. FINDINGS keeps the external repair index FIRST.
Both recorded LPO repairs remain merged. General order/pruning proofs stay open.

Next, model recordTypes and typedTypes and their ordered node observations.
Complete canonical mutation histories, selected-current protection and the
cached-driver bridge remain open. H6 remains strongest combined; H23 is queued.
Full-pipeline, resources, practical width, Haskell/solver, phase-4 and convergence
remain open. The full goal is ACTIVE and incomplete. This precedes the push.

'''
names=['NEXT-PROMPT.md','HANDOFF.md','FINDINGS.md','lean/README.md','lean/SYSTEM.md',
       'lean/API-COVERAGE.md','lean/COVERAGE.md','lean/notes-proof-status-20261017.md',
       'lean/notes-current-system-claim.md']
changes={}
for name in names:
    path=root/name;before=path.read_text();assert '## Concrete template oracle observation proof' not in before
    position=before.index('\n## Ordered pruning resume') if name=='FINDINGS.md' else before.index('\n')+1
    after=before[:position]+prefix+before[position:];path.write_text(after)
    changes[name]=dict(insertion_character=position,inserted=prefix,before_sha256=hashlib.sha256(before.encode()).hexdigest(),after_sha256=hashlib.sha256(after.encode()).hexdigest())
(area/'document-changes.json').write_text(json.dumps(changes,indent=2)+'\n')
print(json.dumps(dict(documents=names,prefix_lines=len(prefix.splitlines()))))
