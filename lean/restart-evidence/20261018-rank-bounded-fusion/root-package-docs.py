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
section=f'''## Current bounded source fusion and actual recursive marker tests

Updated: {stamp}. Proof checkpoint is `{proof[:8]}`.
Starting checkpoint is `9efb49c5`. Main source remains `c0cc8a05`.
Read `lean/notes-current-rank-bounded-fusion.md`.

Filtered Fusion now has a contract restricted by both original raw result
depths. Replacement values and reconstructed outputs remain unrestricted.
Node and union cases compose strict source child laws at that same bound.
Actual surviving node rows derive each child bound. Actual union calls
derive every original member bound, including normalized members. Source
syntax can contain arbitrary binders under the explicit child hypotheses.

An actual selected writer now applies source Fusion at a strictly smaller
original depth to its body and ordinary callbacks. Historical verification
and Keeps derive the full lexical reader Contexts and warm calls. A shared
replacement map permits arbitrary outer replacements, including Empty.
The uniform smaller-depth source induction hypothesis remains explicit.
The proof compares unlowered callback Empty tests. It does not complete
general source binder Fusion or remove the enclosing symbolic self.

A fresh available marker now gives an actual strict original-body call.
For an open stored Mu, its whole result is Empty exactly when that body
result is Empty or the bare marker reference. Initial data constructs the
body call and its Keeps. Marker freshness over finite resolved body leaves
remains explicit. Checked nested used-Mu and ordinary f[marker] cases
distinguish bare marker cleanup from a marker inside a node child.

The next main obligation is bare-marker reflection between the selected
writer body and ordinary probe, together with the Empty comparison. A
stronger recursive relation must retain that information through nested
source binders. Complete induction, changing-capture semantic observations
and the initial recursive guard-profile certificate remain open.

The strongest broad theorem remains conditional correctness of the
checked Lean constraint-reduction model. Successful bounded reduction adds
no finite tree and loses no input tree that satisfies inherited constraints.
With inherited payload some [], the input and output finite-tree languages
are equal. Initial semantic cache facts, recursive guard-profile agreement
and computed resource bounds remain explicit. General termination and
full public Haskell correspondence remain open.

Full Audit passes {audit['jobs']} jobs and {audit['dependency_checks']} dependency checks.
All 12 new public and 5 constructed heads pass complete statement, proof
and standard-axiom checks. Ten selected strict logs are empty. All five
canonical builds are warning-free. Audit retains only its existing
ClosedCompletion warning. Six manifests pin {entries} entries. Independent
writer review identified a redundant-instance linter warning. It was
removed and rechecked. No mathematical issue remains in that review.
Evidence is in `lean/restart-evidence/20261018-rank-bounded-fusion/`.

No Haskell patch or new executable defect is added. FINDINGS retains the
repair registry first. Field-pool repair b9219b9e remains fixed in c0cc8a05.
Publication awaits the existing direct approval. No push is retried.
The full-library goal remains active.

'''
for name in ['NEXT-PROMPT.md','HANDOFF.md','lean/README.md','lean/SYSTEM.md','lean/API-COVERAGE.md','lean/COVERAGE.md','lean/notes-proof-status-20261017.md']:
 p=ROOT/name;s=p.read_text();marker='## Current recursive writer histories and symbolic Empty plans\n'
 assert marker in s and section.splitlines()[0] not in s,name
 s=s.replace(marker,section+marker,1)
 if name=='lean/notes-proof-status-20261017.md':s=re.sub(r'Checked at proof checkpoint `[0-9a-f]+`\.',f'Checked at proof checkpoint `{proof[:8]}`.',s,count=1)
 p.write_text(s)
entry=f'''Current proof update: {stamp}. Proof checkpoint is `{proof[:8]}`.
Node and union fusion now compose strict child laws at the same original
raw depth bound. Actual writer callbacks apply a strictly smaller-depth
source law under arbitrary outer replacements, including Empty. That
uniform induction hypothesis remains unproved. An actual fresh-marker
body call characterizes whole open-Mu Empty as body Empty or bare marker.
Finite marker freshness remains explicit. General writer body/probe bare
marker reflection and source binder Fusion remain open. These are proof
results, not Haskell repair requests. Full Audit passes {audit['jobs']} jobs and
{audit['dependency_checks']} checks. No Haskell patch or new executable defect is added.
Field-pool repair `b9219b9e` remains fixed in `c0cc8a05`. Read
`lean/notes-current-rank-bounded-fusion.md`. Keep this registry first.
Record later repairs with failure, executable reproducer, paths, commit,
checks and upstream status. Preserve every earlier entry.

'''
p=ROOT/'FINDINGS.md';s=p.read_text();header='## Haskell fix handoff for external work\n\n';assert header in s;p.write_text(s.replace(header,header+entry,1))
note='# Bounded fusion and the remaining recursive observation\n\n'+section.split('\n\n',1)[1]
note=note.replace('Read `lean/notes-current-rank-bounded-fusion.md`.\n','')
note+='''## Exact bounded contracts

SourceCurrentBoundedFilteredFusion.Fusion is the earlier actual
reader-filtered contract with firstRaw.depth <= bound and secondRaw.depth
<= bound before the original premises. It retains historical Contexts,
actual raw source calls, common Ready reader, Grows, raw availability,
scope Aliases and self tests, resolved physical Empty slot agreement,
Replacements and literal warm root filters and stored calls. It places
no bound on replacement values, reconstructed values or source syntax.
of_fusion embeds unbounded Fusion. mono restricts a larger bound. Empty
and variable cases are checked. A variable integration has raw depth0
and reconstructs a used source-built Mu with positive depth.

SourceCurrentBoundedFilteredNodeFusion derives opposite row survival from
strict child Fusion at the same bound. The actual physical row on each
side is a surviving original source row at the same index. Coherent raw
parent availability derives every selected child's original depth bound.
Dead rows do not require child bounds. Both node and row endpoints retain
symbols, guards, ordered Empty tests and literal historical child calls.
The integration has a positive-depth nested used Mu and a dead row.

SourceCurrentBoundedFilteredUnionFusion derives each original member's
depth from actual source normalization. Deterministic buildMany calls
align that list with the two actual finite member preparations. The proof
retains exact bare-self selection and common final-reader warm schedules.
The integration includes duplicate and Empty members, a cold subgroup
filter, depth0 raw parents, and a positive-depth reconstructed bare member.

## Earlier writer application and its remaining hypothesis

SourceCurrentBoundedWriterFusion.publication takes an actual Publication,
Keeps from cut and afterBody to a common reader, and Fusion at
event.body.depth for event.expression. Actual callback verification derives
complete lexical reader Contexts, including unused captures. Determinism
aligns the original raw callbacks with their depth certificates. A shared
sparse map retains both original separate substitutions by cross-absence.
Outer maps can contain Empty. Only local replacement Empty parity is used.

The writer endpoint recovers the exact earlier event from strong Written.
Actual reservation, body path and issued suffix derive both Keeps. It
uses the uniform all-source hypothesis at event.body.depth, strictly below
the selected original Mu depth. That uniform hypothesis is not proved.
The endpoint retains the earlier writer's expression; it does not replace
that expression with a later requester's source syntax. Its conclusion is
the physical Empty agreement of actual unlowered callback reconstructions.

The constructed writer case has node[var0,var1], a nonempty selected Mu
local replacement, and an actual captured issued reference mapped to Empty.
A real source call prepares the dead edge. Both sparse stored calls then
return Empty at one warm reader. BinderFree derives this particular
bounded body law. This case does not instantiate the uniform writer IH.

## Actual symbolic-self removal

SourceCurrentStoredMuMarkerEmpty.marker_test compares a successful whole
open-Mu execution with an actual strict original-body execution. The body
map shadows the own name with an available marker reference. The marker
is absent from the finite resolved original leaf profiles. The whole
result is Empty iff the actual body result is Empty or the bare marker.
complete constructs that body call from initial Ready, Available and
Replacements, and derives its Keeps and output availability. No future
body completion or desired body/probe comparison is supplied.

The first checked source-built open used Mu has a nested raw body. Its
body reconstruction is the bare marker, so whole execution returns Empty.
The second has body root alternatives f[self] and an outer reference.
Replacing the outer reference with Empty leaves an ordinary node with the
marker as its child. Whole execution remains nonempty. The node is not
the bare marker. These cases check the precise root-only distinction.

## Next main proof work

Extend the recursive observation to retain bare-marker reflection as well
as physical Empty. The current slot relation permits arbitrary distinct
nonempty replacements, so it cannot imply bare-marker reflection by itself.
Use a stronger slot relation where the needed marker tests agree. Retain
the marker and local scopes through nested source binders. Derive the
node and union observation rules from actual literal root coverage. Use
the actual selected writer, smaller original callback bounds, shared maps
and marker_test to close the source binder case. Do not assume the desired
writer output comparison or count the explicit smaller-source IH as proved.

Then derive changing-capture Local reference, row and epsilon clauses,
finite observations and the initial recursive guard-profile certificate.
Initial query operands and public source ancestry, arbitrary open-Mu
reader support, active-owner exclusion, fresh call bounds, recursive
completion, repeated convergence, equality-operation resources, host Int
adequacy and full public Haskell correspondence remain separate obligations.

The broad theorem remains SourceCurrentOuterInitialActual.node_call at
line432 and NodeLaw in SourceCurrentAllocatedPartialMemoSound at line29.
It quantifies every ambient reference language and finite term. Result
membership implies input membership. An input term that satisfies the
inherited payload is retained. Payload some [] yields language equality.
Payload none is contradiction. Initial Context, Frame, Fits, Carrier,
EqReady, Available and computed Schedule Room remain explicit. This does
not prove all result terms satisfy the inherited payload, general
termination, or all public Haskell initial states satisfy these premises.

## Preservation and verification

All 32841 starting tracked files remain. All 3342 older non-Audit Lean
sources, 242 Haskell files and 206 active package files retain their bytes.
Two stashes and three other worktrees retain their metadata. Preservation
extends 170 earlier frozen manifests to 171 manifests and 1105 module
entries. All earlier proofs, counterexamples, repairs, drafts, attempts
and the optimized interned core remain. No Haskell bytes change.

Selected Lean4.34.1 checks use five-minute caps. Inner readback verifies
memory.max=memory.high=4294967296 and memory.swap.max=0. All selected full
probes retain all eight required options. Only propext, Classical.choice
and Quot.sound are permitted. Ten selected strict logs contain zero bytes.
All earlier failed and warning-bearing attempts remain unselected. The
writer review caught and corrected a redundant instance warning before
the final strict, canonical and public checks. No Haskell formatter or
test run was needed for this proof-only batch. The goal remains active.
'''
(ROOT/'lean/notes-current-rank-bounded-fusion.md').write_text(note)
print('Updated current authorities at',proof[:8])
