from pathlib import Path
import hashlib,json,re,subprocess
root=Path('/home/tritlo/Code/mcfta');area=Path('/tmp/mcfta-recursive-driver-arity-20261027');prior=Path('/tmp/mcfta-recursive-worker-arity-20261027')
head=(area/'source-head.txt').read_text().strip();base=(area/'published-base.txt').read_text().strip();stats=json.loads((area/'source-statistics.json').read_text());public=json.loads((area/'public-validation.json').read_text());assert public['status']=='pass';assert json.loads((area/'source-validation.json').read_text())['status']=='pass';upstream=json.loads((area/'final-upstream-refresh.json').read_text());assert upstream['fetch_exit']==0 and upstream['main_is_ancestor'];main=upstream['main']
audit=(area/'audit-final-1/raw.log').read_text();jobs=int(re.search(r'Build completed successfully \((\d+) jobs\)',audit)[1]);deps=int(re.search(r'Checked axiom dependencies of (\d+) MicroCFTA',audit)[1])
prefix=f'''
## Derived arity histories and rendered original acceptance

Source checkpoint: {head}.
The finite recursive driver now derives every actual output's arity history
from a genuine initial arity heap. No supplied ResourceHistoryWithArity or
future heap is an input. The complete original resource admission and stable
outcome remain. The proof covers every finite recursive depth. It retains
the aggregate caller even when a callback returns no outputs, and retains
each emitted output's own caller and full resource packet.

With initial Canonical storage, each fully discharged output whose native
rendering succeeds and whose returned residuals check belongs to the original
stored native language. It satisfies every original suspended constraint at
the selected root. The proof constructs the assignment and retains original,
output and rendered-state satisfaction. Desired final Satisfies or original
acceptance is not an input. The original root lookup, own output, Discharged,
rendering and checked-residual observations remain explicit.

Actual native Posts retain earlier selected records in the SAME output heap.
That derived output heap supplies each earlier projected-arity annotation.
One common bound aligns the old history producer and the new arity producer
before any output is selected. All old producer fields and full memo states
remain. H6 keeps its exact finite-tree language-preservation contract.

The next gaps are enumeration coverage and the remaining connections from
public entry points to the proved contracts. Convergence, withoutRedundantEdges,
remaining API obligations and full physical Haskell correspondence retain
their earlier limits. The whole formalization goal stays ACTIVE.

Seventeen modules contain {stats['lines']} lines and {stats['new_public_theorems']} new public theorems. All pass
strict checks. Audit passes {jobs} jobs and checks {deps} theorem dependencies.
Public readback contains {public['theorem_signatures_and_axiom_checks']} full signatures and axiom sets without elision.
All {stats['prior_public_theorems']} prior blocks match byte exactly. Only the three standard Lean
axioms occur. No Haskell source changed. FINDINGS retains all repair handoffs.
Details: `lean/notes-current-recursive-driver-arity.md`.

'''
extra=f'''
### Derived histories and Haskell repair status

This checkpoint changes Lean proofs only. All previous Haskell fixes,
regressions and external repair instructions remain below without deletion.
The final successful refresh reads main at
{main}. It remains an ancestor.
The LPO fix and extraction documentation fixes stay integrated. The separate
KBO candidate d7b6a9dfff464eb32c17c314d4825d5b027f1b2d remains unintegrated,
unbuilt and unexecuted here. The positive-Int context-reversal finding stays
open. Run the recorded native regression after its repair reaches main.
Keep all earlier field-pool, constructor, equality and other repair evidence.

The new result closes the Lean arity-history observer gap under genuine
initial arity and the original producer contracts. It does not establish a
new Haskell defect, native regression success or full implementation
correspondence. No Haskell test or benchmark ran in this checkpoint.

'''
note=f'''# Derived arity histories and rendered original acceptance

Source checkpoint: {head}.
Published base: {base}.
Imported main: {main}.
The successful final fetch confirms that main is an ancestor.
The whole CFTA formalization goal stays ACTIVE. Preserve the optimized
interned core, older constructor and equality proofs, marked drafts,
counterexamples and repairs. Previous note:
`notes-current-recursive-worker-arity.md`.

## Target and strongest statements

The top level target remains correctness of the whole CFTA system. This
includes exact finite-tree transformation laws, enumeration soundness and
coverage under explicit contracts, API behavior and physical Haskell
correspondence. The complete target remains open.

The new theorem is
SourcePruningEnumerationRecursive.run_finite_complete_resources_render_sound_from_initial_arity.
The complete original finite-driver admission, genuine initial arity heap
and initial Canonical storage derive a stable actual outcome and all actual
resource histories. For each emitted output, successful native rendering,
own Discharged storage and checked returned residuals construct an assignment.
The rendered term belongs to the original stored native value. It satisfies
every original Suspended.Holds clause at that root. The assignment satisfies
the original input, that output and its rendered state. Original root storage
and native lookup remain explicit observations. No desired original acceptance,
final Satisfies, future heap or supplied arity-certified history is an input.

This proves soundness for those checked, fully discharged rendered outputs
of the modeled finite recursive driver. It does not state that every output
is discharged, every rendering succeeds or every residual check passes.
It does not prove enumeration coverage, convergence or all Haskell execution.
Initial Packet, numerical bounds, annotation carrier, selector membership
and length contracts, mass ceiling and finite reservation remain explicit.
The new initial Heap must come from genuine checked origins. Raw buildEdges,
closure and memo validity alone do not replace that premise.

H6, SourceCurrentColdFiniteWarmCalls.constructed_node_calls, remains the
strongest global exact finite-tree construction theorem. A covered closed
construction, original guard-allocation history and empty inherited payload
derive an actual finite call trace for any chosen finite number of rounds.
Sufficient mathematical width and fuel make every actual node call complete.
The final value accepts exactly the original finite trees at every ambient
environment. H6 does not assert convergence or include withoutRedundantEdges.
All earlier conditional semantic and native-query contracts remain unchanged.

## Finite recursive arity

FiniteArityEffects retains the exact reached caller and each output heap
when it composes an earlier Post or pads a numerical and guard forecast.
FiniteCallbackResourcesArity runs actual recording once. A true callback
returns [] at the current caller. A false callback uses the smaller-depth
contract at the actual framed cache, same caller and full Memos. A common
bound covers both operations. FiniteReceiptResourcesArity retains the full
original receipt packet and uses that actual callback.

FiniteHeadResourcesArity uses the immediate head arity result and the
original resource reservation. It passes the derived head heap to the
callback. FiniteSiblingResourcesArity passes the actual callback aggregate
caller and the full Memos from its retained Post to the next sibling. This
also covers callbacks with outputs=[]. The captured enumeration cache is
the same cache specified by the original algorithm. The proof does not
reconstruct full Memos from equality of query fields.

Stopped results retain their outputs and optional endpoint. A present
endpoint aligns the actual caller. An absent endpoint remains absent.
The strong resource certificate supplies its own retained Post witness on
that branch. The proof does not infer that witness from a missing endpoint.
Each emitted output retains arity at its own caller independently of the
aggregate caller. FiniteSiblingFinishResourcesArity retains every original
scan result and constructs resources for the exact finished outcome.

The ordinary entry and forecast wrappers retain every original field.
Actual entry preserves the enumeration values and mass bound. The original
row envelope bounds the scan and pads its exact reached resources. Parked
prefixes retain their literal native caller. Accepted and rejected narrowing
use the actual PrefixValid observation and proved prefix_heap. Fallback
keeps its exact reached caller and explicit stopped outcome. Initial stop,
done and stuck decisions use their original equations.

FiniteResourcesArity proves CompleteWithArity by Nat induction for every
finite recursive depth. The zero case uses the already proved literal zero
contract. Each successor uses the actual full expansion and smaller-depth
IH. No recursive completion or future arity premise remains in the public
run_finite_complete_resources_arity theorem. It retains the old stable run
and OutcomeResources, then the stronger same-outcome resource certificate.
There is no global CompleteWithArity-to-unconditional-Complete theorem.
The initial Heap remains an extra admission.

CompletedHeadReceipt.returned_heap separately aligns the original receipt
and the new immediate-head producer at one common bound. It derives arity
at the same reached caller from that receipt's own current input heap.
It does not require the earlier work fuel to exceed a new completion bound.
An earlier caller's Post alone does not supply a later caller's whole Heap.

## Derived histories at the same output

ResourceHistory.native_post composes every actual retained prefix, head
input, completed-head and tail Post. It returns a Post to the SAME output's
caller, with its full Memos and exact query field. It needs no arity premise.

ResourceHistory.with_arity_of_output_heap uses the actual output heap.
An ordinary receipt's head Post, completed-head Post and tail Post retain
every original scan edge record in that output heap. The Heap predicate
therefore transfers backward through actual growth.edgeRecords. The existing
with_arity_from_scan_heap theorem derives the exact recorded projected-arity
gate. The recursive tail uses the same output heap. Every original history
field remains. No intermediate or desired heap is assumed.

run_finite_complete_resources_with_history_arity calls the original history
producer once and the finite arity producer once. Their stable run families
identify the literal full outcome at the sum of their bounds. This bound is
fixed before all extra-fuel and output quantifiers. The theorem retains the
entire old stable run, OutcomeResources and original history family. It adds
the stronger actual outcome resources and all same-bound ResourceHistoryWithArity
certificates. Each output heap is derived from that actual stronger outcome.
The public producer does not take the output heap as a premise.

The final rendered-acceptance theorem uses those certificates internally.
It derives output Canonical from each original history and initial Canonical.
The old render_sound theorem then constructs the assignment and all original
and output satisfaction conclusions. The only extra input is initial Heap.
The supplied ResourceHistoryWithArity observer antecedent is removed. All
other original admission, rendering, residual, root and result clauses remain.
The retained work-bound observer index has an explicit Nat type and an unused
name because the observer no longer needs a supplied history argument.

## Validation and retained attempts

Seventeen modules contain {stats['lines']} lines and {stats['new_public_theorems']} public theorems. All seventeen
sources and standalone Audit pass -DwarningAsError=true -Dlinter.all=true.
Audit passes {jobs} jobs and checks {deps} theorem dependencies. Public output
has {public['theorem_signatures_and_axiom_checks']} complete signature and axiom blocks: {stats['new_public_theorems']} new and all {stats['prior_public_theorems']} prior.
All prior blocks match byte exactly. All {stats['unchanged_prior_sources']} pinned prior source modules
retain their published bytes. Only propext, Classical.choice and Quot.sound
occur. There is no new public predicate or structure. There is no sorry,
admit tactic, custom axiom, native_decide, heartbeat increase or linter
suppression. The existing unused-input dependency warning remains in build
logs. New strict source logs are empty.

All attempts remain in the evidence. The first TEMP overlay check failed
before elaboration because a partial namespace hid existing cached modules.
An external TEMP namespace union fixed lookup. Every new proof then passed
strict checking at its own exact snapshot. No overlay artifact changed a
repository source or an earlier cached module. Installed Lake builds and
public readback separately check the repository sources.

The first HistoryPost check found an unqualified Graph. Its final source
qualifies EnumerationState.Graph. The first final-render check could not
infer the now-independent observer index type after the old history premise
was removed. The next check required its unused name to have an underscore.
The final source changes only that type annotation and binder name. Both
failed checks remain. No logical gate or linter option was added.

The first public readback omitted prior modules outside the new dependency
closure. The successful readback explicitly imports all pinned prior sources.
This changes only the checking script. Its failed source and output remain.
The complete signature and axiom output is {public['bytes']} bytes, SHA256
{public['sha256']}.
Literal comparisons retain full old headers and the declared exact inverses.
The final consumer inverse restores only the old supplied history antecedent,
removes initial Heap and undoes the observer binder annotation and name.

No Haskell source, Cabal file, native test or benchmark changed. FINDINGS
retains all prior fixes and repair handoffs. The LPO and extraction-document
fixes remain integrated. KBO candidate d7b6a9dfff464eb32c17c314d4825d5b027f1b2d
remains unintegrated, unbuilt and unexecuted here. The positive-Int
context-reversal finding remains open. Run its recorded native regression
after the repair reaches main.

## Remaining work and restart

Connect every supported public enumeration entry to these proved input
contracts. Retain genuine initial arity, physical and full memo invariants,
canonical storage, resource reservations and selector contracts. Existing
checked-origin results cover their declared constructors. They do not
justify every arbitrary public input without a proof.

Prove whole enumeration coverage for the supported language. Extend the
remaining API obligations and physical Haskell correspondence. Keep the
separate convergence and withoutRedundantEdges boundaries. Preserve all
counterexamples and external Haskell repair instructions. The arity-history
gap in the previous current note is now closed under the new theorem's
explicit initial assumptions. Earlier sections remain historical checkpoints.
No defensible completion percentage or date is claimed.

Portable evidence: `restart-evidence/20261027-recursive-driver-arity/`.
The manifest records stored bytes. decoded-files.json records original bytes
for deterministic gzip payloads. The snapshot retains exact sources, drafts,
failed and successful checks, full public readback, contract comparisons,
source cuts, review seals and document preservation checks. Run its
verify-evidence.py with the snapshot path and --repository for this checkout.
After publication, --committed also compares every payload with Git.
The full formalization goal stays ACTIVE after this checkpoint.
'''
paths=json.loads((prior/'document-paths.json').read_text())[:-1];newnote='lean/notes-current-recursive-driver-arity.md';paths.append(newnote);records=[]
for name in paths[:-1]:
 p=root/name;old=p.read_bytes();assert old==subprocess.check_output(['git','show',base+':'+name],cwd=root);saved=area/'prior-documents'/name;saved.parent.mkdir(parents=True,exist_ok=True);saved.write_bytes(old);offset=old.index(b'\n')+1;addition=(prefix+(extra if name=='FINDINGS.md' else '')).encode();new=old[:offset]+addition+old[offset:];p.write_bytes(new);assert new[:offset]+new[offset+len(addition):]==old;records.append({'path':name,'bytes':len(new),'sha256':hashlib.sha256(new).hexdigest(),'offset':offset,'inserted_bytes':len(addition)})
p=root/newnote;assert not p.exists();p.write_text(note);data=p.read_bytes();records.append({'path':newnote,'bytes':len(data),'sha256':hashlib.sha256(data).hexdigest()});(area/'document-paths.json').write_text(json.dumps(paths,indent=2)+'\n');(area/'document-validation.json').write_text(json.dumps(records,indent=2)+'\n');print(json.dumps({'documents':len(paths),'note_bytes':len(data),'prior_documents_preserved':len(paths)-1}))
