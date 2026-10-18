import json,re,subprocess
from pathlib import Path
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[2]
read=lambda n:json.loads((HERE/n).read_text())
stamp=subprocess.check_output(['date','+%Y-%m-%d %H:%M %Z'],text=True).strip()
proof=subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip()
(HERE/'proof-commit.txt').write_text(proof+'\n')
audit=read('selected-audit.json')
entries=sum(len(read(n).get('entries',read(n).get('files',[]))) for n in read('component-manifests.json'))
section=f'''## Current binder contract counterexample and derived marker premises

Updated: {stamp}. Proof checkpoint is `{proof[:8]}`.
Starting checkpoint is `c81461ba`. Main source remains `c0cc8a05`.
Read `lean/notes-current-tracked-binder-fusion.md`.

A checked counterexample refutes both unrestricted bounded and tracked
binder Fusion at original raw depth0. Its strict ordinary source body law
is proved. One artificial resident Mu has the actual probes node7[x,y]
but a stored body with rows node7[x] and node7[y]. All stated Context,
Ready, aliases, slot, availability, growth and warm-call premises hold.
Replacing x with Empty and y with bare30 retains one row on the artificial
side and returns Empty on the genuine side. The cache is admitted by the
summary invariants. No actual source-history or Haskell defect is proved.

The checked no_uniform consequence rules out the current uniform all-source
Fusion hypothesis at every positive bound. Thus the existing uniform writer
endpoint cannot be instantiated under that contract. Its particular-body
publication lemma remains useful. All earlier checked theorems remain.
A second obstruction concerns the induction measure: smart-unused finish
can return depth0 while the selected Mu has depth1 and its body has depth0.
Actual causal support alone does not give the missing strict raw-depth bound.

The next main step needs actual publication provenance and a different
induction route. Derive a body/probe substitution invariant through real
source construction, or use a chronological writer induction that covers
smart-unused hits. Preserve every source form and arbitrary nested Mu.
Do not silently add provenance to the refuted old definitions. Do not
assume the missing comparison as an initial fact without deriving it.

Three new modules derive finite fresh markers from actual resolved input
profiles, extend tracked paired lexical slots and fresh local bindings,
and transport actual strict-body comparisons through root marker erasure.
They add no future-result freshness premise. Actual fixtures retain visible
outer markers, opaque node bodies and literal local reference executions.
These valid input and erasure laws do not repair the refuted binder contract.

The strongest broad theorem remains conditional finite-tree preservation
for successful checked-model constraint reduction. It adds no input-external
tree and retains each input tree that satisfies inherited constraints.
Inherited payload some [] gives exact language equality. Initial semantic
cache facts, recursive guard-profile agreement and computed resource bounds
remain explicit. General termination and full Haskell correspondence stay open.

Full Audit passes {audit['jobs']} jobs and {audit['dependency_checks']} dependency checks.
Nine new public heads, three integration fixtures, the exact counterexample
and its uniform-bound consequence pass complete proof/standard-axiom checks.
Eight selected strict logs are empty. Three canonical builds are warning-free.
Audit retains only its existing ClosedCompletion warning. Seven manifests
pin {entries} entries. Independent slot and contract review finds no proof issue.
Evidence is in `lean/restart-evidence/20261018-tracked-binder-fusion/`.

No Haskell patch or executable defect is added. FINDINGS retains the repair
registry first. Field-pool repair b9219b9e remains fixed in c0cc8a05.
Publication still awaits the existing direct approval. No push is retried.
The full-library goal remains active.

'''
for n in ['NEXT-PROMPT.md','HANDOFF.md','lean/README.md','lean/SYSTEM.md','lean/API-COVERAGE.md','lean/COVERAGE.md','lean/notes-proof-status-20261017.md']:
 p=ROOT/n;s=p.read_text();marker='## Current finite tracked profiles and recursive marker removal\n'
 assert marker in s and section.splitlines()[0] not in s,n
 s=s.replace(marker,section+marker,1)
 if n=='lean/notes-proof-status-20261017.md':s=re.sub(r'Checked at proof checkpoint `[0-9a-f]+`\.',f'Checked at proof checkpoint `{proof[:8]}`.',s,count=1)
 p.write_text(s)
entry=f'''Current proof update: {stamp}. Proof checkpoint is `{proof[:8]}`.
A checked artificial cache refutes the current unrestricted bounded and
tracked binder Fusion contracts at raw depth0. All their stated premises
hold, including Ready and a proved strict source-body law. The stored body
combines different source callbacks under one probe key. This is a proof
contract counterexample. It establishes no actual source-history or Haskell
defect and requests no Haskell repair. The old uniform all-source writer
hypothesis is impossible at every positive bound. Actual publication
provenance and a new induction route are required. Particular-body writer,
fresh-marker and erasure laws remain checked. Full Audit passes
{audit['jobs']} jobs and {audit['dependency_checks']} checks. No Haskell bytes change.
Field-pool repair `b9219b9e` remains fixed in `c0cc8a05`. Read
`lean/notes-current-tracked-binder-fusion.md`. Keep this registry first.
Record later repairs with failure, executable reproducer, paths, commit,
checks and upstream status. Preserve every earlier entry.

'''
p=ROOT/'FINDINGS.md';s=p.read_text();header='## Haskell fix handoff for external work\n\n';assert header in s;p.write_text(s.replace(header,header+entry,1))
note='# Binder contract refutation and the next causal proof\n\n'+section.split('\n\n',1)[1]
note=note.replace('Read `lean/notes-current-tracked-binder-fusion.md`.\n','')
note+='''## Exact negative result

The frozen binder-contract-counterexample.lean proves an existential body
with TrackedFusion0, the vacuous all-source laws below0, and the negations
of both BoundedFusion0 and TrackedFusion0 for binder true body. Its body is
node [7(false)[var1,var2]]. The binder local is unused.

Actual ordinary source callbacks produce the one-row probes under external
references10 and11. A separate two-row ordinary callback supplies the stored
body under a fresh Mu reservation for those probes. The generic complete
operation installs it. That mixed-source installation is the artificial
step. It is not the actual one-expression binder publication schedule.

The proof derives every Ready field, including normalization, coherence,
complete child availability, decoded root/free/deep/depth summaries,
complete coverage and body/probe open-depth equality. A second genuine
binder key under references20 and21 coexists in the same cache. Both raw
smart results are ordinary nodes of depth0. Source-scoped alias equivalence
and both self-filter tests hold. The replacement maps pair10/20 with Empty
and11/21 with bare30. Literal stored executions produce a nonempty unary
row on the first side and Empty on the second. Actual Keeps gives a common
final Ready reader. Replay proves literal warm calls there. Raw growth,
raw availability, original Contexts, both root filters and every remaining
exact old-contract premise are derived. The old bounded conclusion would
assert false=true. to_empty refutes the tracked contract as well.

The separate no_uniform theorem proves that every positive bound includes
this false rank0 instance. Every selected candidate Mu has positive depth.
Therefore the old uniform smaller-depth writer premise is unattainable.
This does not invalidate a checked implication with that explicit premise.
It prevents using that implication to complete the intended full source
induction. The publication theorem under a particular body Fusion law
remains useful, for example with an actual binder-free body.

Existing empty, variable, node, union and BinderFree theorems remain intact.
The unrestricted full source law was a definition and an open target. This
batch proves its failure under the stated assumptions. No earlier positive
theorem or source file is removed or rewritten.

## Why causal support and a new induction route are needed

ConstrainedCapSourceHistory.Context contains the earlier semantic Context
and decoded DepthHeap. The earlier Context contains Normal, Values,
ProfileHeap and FreeHeap. Ready adds coverage and open-depth equality.
These are summaries. None supplies an actual common-expression publication
or the issued-reference path from that publication to the common reader.
ConstrainedCapSourceHistory.Heap is separate and retains only Origin.
Origin alone does not supply the later growth and issued suffix.

NativeMuIssuedWriters.writers retains an initial-presence alternative.
A path from empty eliminates that alternative and derives actual Written.
Thus an actual issued path from empty to the reader, or actual per-key
Written receipts to that reader, supports earlier-writer recovery. A new
causal contract must state its input explicitly and derive it for the real
initial state and every actual execution. The old definitions stay refuted.

Adding that causal input does not repair the old raw-depth induction.
Smart-unused finish can return an ordinary value of depth0. Its selected
candidate Mu has depth1 and its stored body has depth0. The earlier writer
body is not strictly below the returned raw bound0. The current strict
syntax-body IH cannot cover an arbitrary earlier writer's different syntax.
Use a chronological writer induction or prove a stronger substitution
invariant while each actual publication is installed. Such an invariant
must be established through source execution. It cannot be supplied as the
missing desired result law. Keep all raw/smart, used/unused, closed/open,
bare-self and nested binder cases in scope.

## Valid marker inputs and erasure transport

TrackedMarkerChoice.choose computes an ordinary marker using freeBound over
supplied tracked names and actual resolved root profiles. fresh proves
availability at any reader and exact absence from each finite profile.
bodies specializes it to both resolved body-leaf collections. No Ready,
Replacements or future output assumption is needed for this finite choice.
The actual nested-Mu fixture chooses206, reconstructs body profile[206,101]
and uses the existing complete endpoint to obtain whole bare101.

TrackedSlotExtension.related gives the exact tracking-extension iff from
absence in both resolved profiles. paired extends only reference slot
observations and retains fixed captures and free-map equality. bind_marker
uses explicit original local-name freshness to bind the same available
marker on both sides. Its actual used-Mu fixture checks the extended Paired
spine and two literal local execute calls. No future profile absence is
inferred. Failed computational fixture attempts remain as unselected logs.

TrackedProfileErasure.mask_erase proves exact mask/erase commutation. The
outer marker list may contain the local marker and duplicates. equivalent
transports extended masked equivalence through erasure. open_execute uses
two actual whole and strict-body calls, initial Ready/Available/Replacements
and finite leaf freshness. An explicit strict-body Related IH derives the
whole Related conclusion. The actual fixture includes visible outer101,
distinct untracked101/102 opacity, and an ordinary node containing local100.
These are input and cleanup laws, not full source binder closure.

## Preserved broad theorem and remaining scope

SourceCurrentOuterInitialActual.node_call at line432 and NodeLaw in
SourceCurrentAllocatedPartialMemoSound at line29 retain the broad conditional
claim. Every output finite tree belongs to the input language. Every input
finite tree that satisfies inherited constraints is retained. Payload
some [] gives exact equality; none is contradiction. Context semantic memo
facts, Frame recursive profile agreement, Fits, Carrier, EqReady, Available
and computed Schedule Room remain explicit. This theorem does not assert
that all output trees satisfy the inherited payload or that all runs finish.

Changing-capture Local reference/row/epsilon observations, finite
observations and the initial recursive guard-profile certificate remain
open. Initial query operands and public source ancestry, arbitrary open-Mu
reader support, active-owner exclusion, fresh call bounds, recursive
completion, repeated convergence, equality resources, host Int adequacy and
full Haskell correspondence remain separate full-goal obligations.

## Preservation and validation

All33432 starting tracked files remain. All3353 older non-Audit Lean sources,
242 Haskell files and206 active package files retain their bytes. Two stashes
and three other worktrees retain their metadata. The new frozen module
manifest extends172 prior manifests to173 and1114 module entries. Every
prior proof, counterexample, repair, draft, failed attempt and the optimized
interned core remains. No Haskell bytes change.

Selected Lean4.34.1 jobs run under4GiB and five-minute limits. Inner readback
checks memory.max=memory.high=4294967296 and memory.swap.max=0. All selected
full probes use all eight required options. Only propext, Classical.choice
and Quot.sound are permitted. Nine new production heads and five supporting
heads pass full checks: three actual integrations, the exact counterexample
and its direct uniform-bound consequence. Eight selected strict logs contain
zero bytes. Three canonical builds are warning-free. Audit retains only its
existing ClosedCompletion unused-input warning. Independent review reuses
three public and two constructed checks, with zero new pairs or Lean runs.
No Haskell formatter or test run is required for unchanged Haskell bytes.
The full-library goal stays active. Publication awaits the prior direct
approval; this batch performs no push, deployment or board post.
'''
(ROOT/'lean/notes-current-tracked-binder-fusion.md').write_text(note)
print('Updated authorities at',proof[:8])
