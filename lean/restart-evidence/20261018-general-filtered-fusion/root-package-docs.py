import json,re,subprocess
from pathlib import Path
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[2]
read=lambda name:json.loads((HERE/name).read_text())
stamp=subprocess.check_output(['date','+%Y-%m-%d %H:%M %Z'],text=True).strip()
proof=subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip()
(HERE/'proof-commit.txt').write_text(proof+'\n')
audit=read('selected-audit.json')
entries=sum(len(read(name).get('entries',read(name).get('files',[]))) for name in read('component-manifests.json'))
section=f'''## Current general filtered source cases and binder-free composition

Updated: {stamp}. Proof checkpoint is `{proof[:8]}`.
Starting checkpoint is `6b7e1261`. Main source remains `c0cc8a05`.
Read `lean/notes-current-general-filtered-fusion.md`.

One general Fusion contract now uses independent historical raw source
Contexts and actual warm root filters and stored calls at the reader.
Varying reference slots need only equal resolved physical Empty tests.
Fixed captures retain equal replacement maps on their free names.
Scoped aliases and self tests remain explicit. Empty and variable cases
are proved. Nonempty replacement maps derive a separate full-source law.

Node fusion now follows from strict source child Fusion under that same
contract. Actual indexed rows derive both child schedules and opposite
stored-row survival. Union fusion follows from strict source members.
Finite actual preparation derives cold subgroup calls at a later reader.
Exact bare-self parity gives equal retention decisions. No parent output
law, lexical Generated-to-Empty law or reader-wide lexical availability
is assumed. Original historical source Contexts remain unchanged.

Strong induction composes all four cases for every BinderFree source
expression. This restriction applies to source syntax. Fixed captured
values can still contain arbitrary open nested Mu values. General new
source binder fusion and changing-capture observations remain open.

The strongest broad claim concerns the checked Lean model. Given the
stated initial semantic cache and recursive-heap invariants and computed
resource bounds, a successful constraint-reduction traversal adds no
finite tree and loses no input tree that satisfies inherited constraints.
With inherited payload some [], its output accepts exactly the input
finite-tree language. Payload none denotes contradiction. Initial cache
soundness and guard-profile agreement are substantive remaining premises.
General termination and full public Haskell correspondence remain open.

Full Audit passes {audit['jobs']} jobs and {audit['dependency_checks']} dependency checks.
All 8 new public and 4 constructed heads pass complete statement, proof
and standard-axiom checks. Eight selected strict logs are empty. All four
canonical builds are warning-free. Audit retains only its existing
ClosedCompletion warning. Six manifests pin {entries} entries. Independent
node and binder-free review finds no material issue. Both adversarial
searches timed out. Zero paired cases completed. No counterexample or
general binder validation is claimed from those searches. Evidence is in
`lean/restart-evidence/20261018-general-filtered-fusion/`.

No Haskell patch or new executable defect is added. FINDINGS retains the
repair registry first. Field-pool repair b9219b9e remains fixed in c0cc8a05.
Publication awaits the existing direct approval. No push is retried.
The full-library goal remains active.

'''
for name in ['NEXT-PROMPT.md','HANDOFF.md','lean/README.md','lean/SYSTEM.md','lean/API-COVERAGE.md','lean/COVERAGE.md','lean/notes-proof-status-20261017.md']:
 p=ROOT/name;s=p.read_text();marker='## Current recursive Empty fusion and exact union coverage\n'
 assert marker in s and section.splitlines()[0] not in s,name
 s=s.replace(marker,section+marker,1)
 if name=='lean/notes-proof-status-20261017.md':s=re.sub(r'Checked at proof checkpoint `[0-9a-f]+`\.',f'Checked at proof checkpoint `{proof[:8]}`.',s,count=1)
 p.write_text(s)
entry=f'''Current proof update: {stamp}. Proof checkpoint is `{proof[:8]}`.
General reader-filtered Empty fusion now has empty, variable, node and
union cases. Strong induction proves the full BinderFree source fragment.
Fixed captured open Mu values remain permitted. The general source
binder case and changing-capture observations remain open. Full Audit
passes {audit['jobs']} jobs and {audit['dependency_checks']} checks. Source-built integrations
check distinct raw parents, resolved Empty row removal and cold subgroup
preparation. Both adversarial searches timed out with zero completed
paired cases. They establish no counterexample or Haskell defect.
No Haskell patch or new executable defect is added. Field-pool repair
`b9219b9e` remains fixed in `c0cc8a05`. Read
`lean/notes-current-general-filtered-fusion.md`. Keep this registry first.
Record later repairs with failure, executable reproducer, paths, commit,
checks and upstream status. Preserve every earlier entry.

'''
p=ROOT/'FINDINGS.md';s=p.read_text();header='## Haskell fix handoff for external work\n\n';assert header in s;p.write_text(s.replace(header,header+entry,1))
note='# General filtered source fusion and exact current claim\n\n'+section.split('\n\n',1)[1]
note=note.replace('Read `lean/notes-current-general-filtered-fusion.md`.\n','')
note+='''## Exact broad theorem and its limits

SourceCurrentOuterInitialActual.node_call proves NodeLaw for an actual
successful bounded nodeCall. Context supplies semantic facts about warm
outer memo results, merge coverage, emptiness answers and native admission.
Frame supplies recursive stored-Mu guard-depth profile agreement. Fits,
Carrier, EqReady, Available and the computed Schedule Room remain explicit.
These assumptions are not derived for every public Haskell entry state.

NodeLaw states two facts for every ambient reference language and finite
term. Membership in the result implies membership in the input. If the
term satisfies the inherited payload, result membership is equivalent to
input membership. This is partial correctness of constraint reduction.
It is not a claim that the whole intersection API is now verified.
For payload some [], every term satisfies the inherited constraints, so
the two finite-tree languages are equal. Payload none means contradiction.

## General source contract

SourceCurrentFilteredSourceFusion.Fusion quantifies one full source
expression under two symbolic lexical instantiations. The two raw builds
retain their own initial Contexts and literal historical calls. Their
return heaps grow into one Ready reader. Each raw result and replacement
record is available there. Both root filters and both stored calls have
literal warm equations at that reader. Scope aliases and self tests retain
the precise binders and names. Paired compares only resolved physical
Empty flags for reference slots. Fixed values are identical and their
replacement maps agree on each free name.

The empty and variable cases derive the full contract. The variable case
uses its selected slot only. Fixed captures use scoped equal filters and
actual execute congruence. The nonempty_maps endpoint covers all source
syntax when resolved replacement values on filtered free support are
nonempty. It needs no historical filter adjacency or whole unused lexical
availability at the reader. It uses the full source Empty abstraction,
existing filter Empty preservation and stored nonempty replacement.

## Node, union and complete source fragment

SourceCurrentFilteredNodeFusion.row derives an opposite actual surviving
stored row. It retains the complete symbol and guard and ordered child
Empty flags. The child hypothesis is Fusion only for strict children of
actual source rows. Original row indexes and both RowCall histories are
derived from actual raw construction. Physical raw child availability
and reader freshness supply absent child self filters. The node theorem
then derives the complete parent Fusion contract in both directions.

SourceCurrentFilteredUnionFusion.union uses strict source-member Fusion.
Two finite actual preparations supply all cold child filters and stored
calls at one later Ready reader. Original source Contexts stay at their
historical entry heaps. Warm parent filters and outputs replay unchanged.
Live scopes give the child alias and self tests. Actual source bare-self
parity gives equal retention selectors. Exact filtered union Empty criteria
then derive parent agreement. No desired parent output law is assumed.

SourceCurrentFilteredBinderFreeFusion.source uses explicit strong
induction on source syntax. Existing BinderFree, ManyBinderFree and
EdgesBinderFree define the fragment. It contains empty, variable, node and
union source expressions of arbitrary finite nesting. It excludes new
source binder expressions. It does not constrain the depth or recursive
content of fixed captured values. The common fixed-slot map agreement
still applies. The integration applies this complete endpoint to actual
distinct raw parents whose changing references both resolve to Empty.

## Evidence and next obligations

The actual source integrations derive Contexts, Ready, available values,
Paired, aliases, self tests and literal completed calls. The variable
example resolves to a used Mu on one side and a distinct nonempty bare
reference on the other. The node example removes the same row from two
distinct raw nodes. Its dead edge was allocated by a real source seed.
The union example has warm parent calls while a proper subgroup filter
is still cold at that reader. The binder-free example applies the full
composed source law. The node and binder-free review reuses complete
proof probes and adds no new proof heads or Lean runs.

The adversarial evaluator searches are incomplete. The 64-case and reduced
12-case runs each hit a five-minute cap. Zero paired cases completed.
The failed indexing attempt printed two base evaluator facts. They are
not kernel proof heads. No counterexample or universal binder law follows.
Every attempt and cap readback remains preserved. The focused actual
older-writer changing-capture check is recorded as unexecuted next work.

The next main proof target is general source binder Fusion. Retain the
actual earlier selected writer, its body and chronology. The full semantic
simulation also needs reference, row and epsilon Local clauses, finite
observations and guard-depth agreement. Physical Empty alone is not
semantic language emptiness. Preserve initial query operand/source ancestry,
active-owner exclusion, fresh bounds, arbitrary open-Mu reader support,
recursive completion, repeated convergence, equality-operation resources,
host Int adequacy and full public Haskell correspondence.

All 32262 starting tracked files remain. All 3333 older non-Audit Lean
sources, 242 Haskell files and 206 active package files retain their bytes.
Two stashes and three other worktrees retain their metadata. Preservation
extends 169 frozen manifests with four new modules. Every prior proof,
counterexample, repair, draft, failed attempt and optimized core remains.

Selected Lean 4.34.1 runs have five-minute caps. Inner readback verifies
memory.max and memory.high 4294967296 and memory.swap.max 0. Complete
public and constructed probes use all eight required printer and linter
settings. Only propext, Classical.choice and Quot.sound are permitted.
No Haskell file changes. Haskell formatters and tests are not needed for
this batch. The full-library proof goal remains active.
'''
(ROOT/'lean/notes-current-general-filtered-fusion.md').write_text(note)
print('Updated restart authorities and current note at',proof[:8])
