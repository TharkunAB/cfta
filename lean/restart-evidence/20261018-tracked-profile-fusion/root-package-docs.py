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
section=f'''## Current finite tracked profiles and recursive marker removal

Updated: {stamp}. Proof checkpoint is `{proof[:8]}`.
Starting checkpoint is `cf787b1b`. Main source remains `c0cc8a05`.
Read `lean/notes-current-tracked-profile-fusion.md`.

Filtered Fusion now compares finite tracked root profiles. A pure root
reference set is visible only when all its names are tracked. Every other
nonempty root is opaque. The relation preserves Empty and bare tracked
names for actual available normalized results. With no tracked names,
to_empty recovers the exact prior bounded Empty contract under its original
Paired Empty premise. No lexical availability assumption is added.

Node and union cases compose strict source child laws at the same original
raw depth bound. Union composition retains root opacity and the exact
tracked name set. Actual earlier writers compare tracked callback outputs
under arbitrary outer maps, including Empty. Their uniform smaller-depth
source induction hypothesis remains explicit and unproved.

The actual open-Mu bridge now gives the complete unmasked root profile:
the whole result equals the strict marker-body profile after removing the
fresh local marker, up to reference-set equivalence. complete constructs
that body call. A checked nested used-Mu body has both a local marker and
an outer marker at its root. Removing the local marker retains the outer
marker. An ordinary node containing the local marker remains opaque.
Finite freshness over actual resolved original leaves remains explicit.

The next main obligation is the complete source binder clause and its
uniform depth induction. Derive fresh-marker absence and extended Paired
slots from the actual inputs, apply the earlier-writer step at strict body
depth, and retain exact finish/lower behavior. The new profile rules do
not establish these remaining obligations. Changing-capture semantic
observations and the initial recursive guard-profile certificate stay open.

The strongest broad theorem remains conditional correctness of the
checked Lean constraint-reduction model. Successful bounded reduction adds
no finite tree and loses no input tree that satisfies inherited constraints.
With inherited payload some [], the input and output finite-tree languages
are equal. Initial semantic cache facts, recursive guard-profile agreement
and computed resource bounds remain explicit. General termination and
full public Haskell correspondence remain open.

Full Audit passes {audit['jobs']} jobs and {audit['dependency_checks']} dependency checks.
All 26 new public and 6 constructed heads pass complete statement, proof
and standard-axiom checks. Twelve selected strict logs are empty. All six
canonical builds are warning-free. Audit retains only its existing
ClosedCompletion warning. Seven manifests pin {entries} entries. Independent
root/base/writer review finds no material issue. It reuses existing checks
and adds no proof pairs. Earlier failed and warning-bearing attempts remain.
Evidence is in `lean/restart-evidence/20261018-tracked-profile-fusion/`.

No Haskell patch or new executable defect is added. FINDINGS retains the
repair registry first. Field-pool repair b9219b9e remains fixed in c0cc8a05.
Publication awaits the existing direct approval. No push is retried.
The full-library goal remains active.

'''
for name in ['NEXT-PROMPT.md','HANDOFF.md','lean/README.md','lean/SYSTEM.md','lean/API-COVERAGE.md','lean/COVERAGE.md','lean/notes-proof-status-20261017.md']:
 p=ROOT/name;s=p.read_text();marker='## Current bounded source fusion and actual recursive marker tests\n'
 assert marker in s and section.splitlines()[0] not in s,name
 s=s.replace(marker,section+marker,1)
 if name=='lean/notes-proof-status-20261017.md':s=re.sub(r'Checked at proof checkpoint `[0-9a-f]+`\.',f'Checked at proof checkpoint `{proof[:8]}`.',s,count=1)
 p.write_text(s)
entry=f'''Current proof update: {stamp}. Proof checkpoint is `{proof[:8]}`.
Finite tracked root profiles now preserve Empty and bare tracked names.
The exact prior bounded Empty contract follows under its original Paired
Empty premise. Actual node and union clauses compose strict child laws.
An actual earlier writer compares tracked callbacks under an explicit
uniform smaller-source induction hypothesis. The open-Mu bridge removes
only the fresh root marker. A mixed local/outer-marker case retains the
outer marker. General binder Fusion, its uniform induction and semantic
initialization remain open. These are proof results, not Haskell repair
requests. Full Audit passes {audit['jobs']} jobs and {audit['dependency_checks']} checks.
No Haskell patch or new executable defect is added. Field-pool repair
`b9219b9e` remains fixed in `c0cc8a05`. Read
`lean/notes-current-tracked-profile-fusion.md`. Keep this registry first.
Record later repairs with failure, executable reproducer, paths, commit,
checks and upstream status. Preserve every earlier entry.

'''
p=ROOT/'FINDINGS.md';s=p.read_text();header='## Haskell fix handoff for external work\n\n';assert header in s;p.write_text(s.replace(header,header+entry,1))
note='# Finite tracked profiles and the remaining source binder proof\n\n'+section.split('\n\n',1)[1]
note=note.replace('Read `lean/notes-current-tracked-profile-fusion.md`.\n','')
note+='''## Exact observation and original-contract recovery

SourceCurrentTrackedRootProfile.mask keeps Some names when every name is
in the finite marker list. Otherwise it returns None. None is the opaque
profile. Some [] is Empty. This operation does not project a mixed list
to its tracked subset. Related uses InternedProfileEquivalence.Equivalent,
so name order and duplicates do not affect it. The full unmasked profile
remains a separate observation.

Related.empty and Related.bare use Ready and actual output availability.
They do not reflect arbitrary raw malformed records. Related.bare also
requires that the tested name is tracked. mask_cons_fresh states exact
mask equality when the added marker is absent from the complete profile.
It does not prove absence for a later resolved or reconstructed result.

SourceCurrentTrackedFilteredFusion.Fusion retains both original raw depth
bounds and every premise of SourceCurrentBoundedFilteredFusion.Fusion.
The markers parameter precedes Atom and reader. It replaces only reference
slot and output relations with Related markers. Fixed captures retain
exact value equality and replacement-map agreement on free names. Original
historical Contexts, Aliases, self tests, literal source builds, Grows,
Ready, Replacements, raw availability, root filters and stored calls remain.
Neither replacements nor outputs receive a depth bound.

nil_equiv recovers exactly the Empty-only observation. to_empty converts
the original Paired Empty slots with Ready and Replacements. Unmapped
reference slots use their literal nonempty fallback. Actual filter and
stored-call verification derives output availability. Thus to_empty does
not narrow the previous contract by adding a lexical availability premise.
The source-built base fixture applies both reference and to_empty.

## Same-bound composition and actual earlier writers

SourceCurrentTrackedFilteredNodeFusion.row and node derive physical child
Empty agreement from Related and actual available child outputs. Original
surviving row depths give each child bound. Returned ordinary node roots
then have the same tracked observation. The fixture retains actual ordered
children [ref99,ref98] and [ref99,leaf], with only ref99 tracked.

SourceCurrentTrackedFilteredUnionFusion.union derives its observation
from actual root coverage and retained member calls. The profile is
nonopaque exactly when there is no literal ordinary row and every literal
root atom is a tracked reference. In that case its reference set equals
the literal root reference set. Actual finite preparation retains cold
subgroup calls and the bare-own exception. The checked depth0 raw parents
include duplicate and Empty members and an excluded used nested Mu.
Their retained reconstructed roots are the actual tracked marker90.

SourceCurrentTrackedWriterFusion.publication derives complete lexical
reader Contexts and literal warm callbacks from actual historical calls
and Keeps. Original callback depths instantiate the smaller body law.
A shared replacement map retains each original sparse call by cross-absence.
Outer maps may contain Empty. Local Related inputs derive Related outputs.
writer recovers the exact earlier issued Publication, syntax and captures.
It uses a uniform all-source hypothesis strictly below the selected original
Mu depth. That hypothesis is not proved. It does not identify an earlier
writer's syntax with a later requester's syntax.

The writer fixture uses node[var0,var1]. A captured issued reference maps
to Empty. The local replacement is the available nonempty selected Mu.
A real source call prepares the dead row. The tracked node and variable
lemmas derive this particular body law. The witness applies publication.
Its actual Written receipt does not instantiate the uniform writer IH.

## Full actual root-profile marker removal

SourceCurrentStoredMuTrackedProfile.erase filters one marker from a pure
root name list and preserves None. open_execute compares the actual whole
open-Mu result with an actual strict original-body marker execution.
Their full profiles are Equivalent after erase. Ready, Available,
Replacements and finite freshness over actual resolved original body
leaves remain explicit. complete constructs the strict body execution,
its Keeps suffix and its available output from the initial facts.

The mixed-marker fixture builds an open used nested Mu. The strict body
profile is exactly Some [local100,old101]. Whole execution returns the
bare old101 reference. Erasing local100 retains Some [old101]. A second
actual body is ordinary node7(false)[local100]. That body remains opaque
through whole execution. Root-only erasure does not remove a node child.
No desired body/probe relation or future body completion is assumed.

## Next main proof work and broad claim

Prove the general source binder clause and complete the uniform original
depth induction. Select a local marker fresh for both finite resolved leaf
supports. Derive every exact profile-absence and extended Paired premise
needed by mask_cons_fresh. Use the actual earlier writer and strict
original callback depth. Compare its callbacks with the current ordinary
calls under the extended tracked relation. Apply actual marker erasure
and preserve every smart/raw used/unused finish case. Do not assume the
missing output relation or count the explicit smaller-source IH as proved.

Then derive changing-capture Local reference, row and epsilon observations,
finite observations and the initial recursive guard-profile certificate.
Initial query operands and public source ancestry, arbitrary open-Mu reader
support, active-owner exclusion, fresh call bounds, recursive completion,
repeated convergence, equality-operation resources, host Int adequacy and
full public Haskell correspondence remain separate obligations.

The broad theorem is SourceCurrentOuterInitialActual.node_call at line432
and NodeLaw in SourceCurrentAllocatedPartialMemoSound at line29. For every
ambient reference language and finite term, output membership implies
input membership. Every input term that satisfies the inherited payload
is retained. Payload some [] gives exact language equality. Payload none
is contradiction. Context semantic memo facts, Frame recursive profile
agreement, Fits, Carrier, EqReady, Available and computed Schedule Room
remain explicit. It does not show that all output terms satisfy inherited
constraints, that every run terminates, or that every public Haskell
execution satisfies these premises.

## Preservation and validation

All 33105 starting tracked files remain. All 3347 older non-Audit Lean
sources, 242 Haskell files and 206 active package files retain their bytes.
Two stashes and three other worktrees retain their metadata. The new frozen
manifest extends 171 prior manifests to 172 manifests and 1111 module
entries. Earlier proofs, counterexamples, repairs, drafts, failed attempts
and the optimized interned core remain. No Haskell bytes change.

Selected Lean4.34.1 jobs use five-minute caps. Inner readback verifies
memory.max=memory.high=4294967296 and memory.swap.max=0. All selected full
probes retain all eight required printer and linter options. Only propext,
Classical.choice and Quot.sound are permitted. All twelve selected strict
logs have zero bytes. Six canonical builds are warning-free. The full
Audit retains only the existing ClosedCompletion unused-input warning.
Independent review has zero new Lean runs and reuses 20 public plus three
constructed pairs. Its counts are not added to the new proof totals.
No Haskell formatter or test run is needed for this proof-only batch.
The full-library goal remains active.
'''
(ROOT/'lean/notes-current-tracked-profile-fusion.md').write_text(note)
print('Updated current authorities at',proof[:8])
