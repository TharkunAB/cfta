from pathlib import Path
import hashlib
import json
import re
import subprocess
root=Path('/home/tritlo/Code/mcfta')
area=Path('/tmp/mcfta-recursive-receipts-20261027')
head=(area/'source-head.txt').read_text().strip()
base=(area/'published-base.txt').read_text().strip()
aggregate=(area/'build-aggregate-final/raw.log').read_text()
jobs=re.search(r'Build completed successfully \((\d+) jobs\)',aggregate).group(1)
dependencies=re.search(r'Checked axiom dependencies of (\d+) MicroCFTA theorems',aggregate).group(1)
public=json.loads((area/'public-validation.json').read_text()); assert public['status']=='pass'
modules=json.loads((area/'modules.json').read_text())
lines=sum(len((root/'lean/MicroCFTA'/f'{module}.lean').read_bytes().splitlines()) for module in modules)
prefix=f'''
## Finite sibling invocations now carry full native head receipts

Source checkpoint: {head}.
Original finite resources now derive one sufficient work bound for the whole
sibling result and every actual invoked hook. The result keeps the ENTIRE old
sibling contract. Each hook retains its actual head Caller, full Memos, input
Packet, reservation, completed Packet and stable completed head receipt.
An aggregate native Post connects the scan input to that actual head input.
Earlier hooks thread their actual native endpoints. Every sibling restores
the SAME captured enumeration input. The finite-depth corollary derives the
smaller recursive completion contract. No future success premise remains.

The resource-backed semantic consumer restores head and scan-input assignment
meaning from satisfaction at the actual completed head cache. Canonical,
nonterminal, fresh arity and child retention remain explicit semantic gates.
An isolated recursive boundary is disabled by the original native index.
Actual retained parked and narrowed prefixes preserve its isolation.
Whole recursive-history admission, cleared or opaque constraint recovery or
exclusion, whole output acceptance and enumeration coverage remain open.

Ten modules, {lines} lines and 21 public theorems pass strict checking.
Audit passes {jobs} jobs and {dependencies} theorem dependency checks.
H6 remains the strongest global exact finite-tree construction theorem.
Its signature and both earlier conditional captured renderers are unchanged.
No Haskell source changed. No new Haskell defect or repair is claimed.
All earlier Haskell fixes and external repair handoffs remain in FINDINGS.
Details: `lean/notes-current-recursive-receipts.md`. The full goal stays ACTIVE.

'''
documents=['NEXT-PROMPT.md','HANDOFF.md','FINDINGS.md','lean/API-COVERAGE.md','lean/COVERAGE.md','lean/README.md','lean/SYSTEM.md','lean/notes-current-system-claim.md','lean/notes-proof-status-20261017.md']
records=[]
for name in documents:
 path=root/name; old=path.read_bytes()
 assert old==subprocess.check_output(['git','show',base+':'+name],cwd=root)
 target=area/'prior-documents'/name; target.parent.mkdir(parents=True,exist_ok=True); target.write_bytes(old)
 first,rest=old.split(b'\n',1); data=first+b'\n'+prefix.encode()+rest
 path.write_bytes(data)
 records.append(dict(path=name,bytes=len(data),sha256=hashlib.sha256(data).hexdigest(),offset=len(first)+1,inserted_bytes=len(prefix.encode())))
note=f'''# Finite sibling receipts and actual prefix isolation

Source checkpoint: {head}.
Published base: {base}.
Imported main: 82258094c2c32bb93e517427bc649a5c7077adac.
The formalize pull and main fetch succeeded. Main did not change.
The preceding checkpoint abd06c770 is published. Its detailed note is
notes-current-recursive-composition.md. Preserve the optimized interned core,
older constructor and equality work, repairs, counterexamples and marked drafts.
The full goal remains ACTIVE.

## Target and strongest current claims

The target remains whole-system source-connected correctness. It includes
exact finite-tree language preservation, enumeration soundness and enumeration
coverage under explicit solver and pruning contracts. It is not complete.

SourceCurrentColdFiniteWarmCalls.constructed_node_calls remains the strongest
global exact finite-tree construction result. Covered closed construction and
the original valid guard-allocation history derive mathematical width and
fuels for each finite budget and round count. The actual formal calls complete.
The final node stays available and accepts exactly the original finite trees
in every ambient environment. Its inherited payload is empty.

The earlier actual flat captured renderer restores acceptance at its original
captured edge and parent from the original resource and semantic admission.
Original Stratified order, an actual completed captured receipt, Discharged,
actual rendering at that receipt's reached heap and checks of every returned
residual remain required. This is one captured step. It does not restore the
whole recursive input from a later emitted output.

The strongest new execution result concerns every actual hook invocation in
an admitted finite sibling scan. A bound is derived from the original input
before the extra fuel and actual invocation are quantified. At that bound and
all larger diagonal bounds, each actual invocation has its own complete head
receipt and aggregate native Post from the scan's original Caller. The entire
earlier sibling result remains present at that same common work bound.

The finite-depth corollary supplies Recursive.finite_complete itself. It has
no abstract smaller-depth Complete admission. It does not assert that a raw
low-fuel completion has a stable receipt, or that every recursive history tag
has such an admitted receipt. Those are different claims.

## Rich head input and completion data

HeadAdmission retains the original recursive Packet and full native Context
and Memos. It also retains Ready, IncomingAvoid, Fits, the guard annotation
heap, actual stored parent and selected edge, and its original cost reservation.
CompletedHeadReceipt retains that input admission, actual native Post and
query equality, the restored captured Packet, the own completed-cache Packet,
the padded resource carrier, arity and projection facts, and stable actual
head execution. Its fragment, reached Caller, Queries and cache are the actual
hook input endpoint. No desired assignment is a producer admission premise.

head_finite_complete_resources_with_receipt calls the original head producer
once and retains its entire literal contract before appending the receipt.
alternatives_finite_invocation_receipts performs the resource induction over
the selected edges. After a completed earlier hook, the suffix uses its actual
returned Caller, full Memos, Packet, resource seed and native Post. It restores
the SAME captured enumeration input. It does not use that earlier subtree's
final enumeration cache as the next sibling input. A stopped hook supplies
no suffix invocation. Earlier actual invocations remain covered.

alternatives_finite_complete_resources_with_invocations calls the old sibling
producer once and the rich helper once. It chooses their summed bound. Exact
arithmetic aligns the callback's own work fuel as well as the captured run.
It retains all processed receipts, outputs, Post, Packet, Fits, guard heap,
receipt and output certificates, and complete or stopped endpoint evidence.
alternatives_finite_complete_invocation_resources removes only the abstract
Complete argument. Its entire output is the same.

## Backward assignment meaning at the actual endpoints

stable_complete_of_diagonal_resources uses genuine original resource completion
to obtain independent sufficient bounds. It intersects that execution with
the actual stable diagonal at one common larger fuel. Determinism identifies
the same completed endpoint. It does not infer general multi-fuel stability
from an arbitrary diagonal observation alone.

CompletedHeadReceipt.sound_current consumes that actual rich receipt. Under
explicit Canonical, nonterminal, fresh arity and child-retention gates,
satisfaction of its actual completed cache implies satisfaction of its input
cache, selected-edge and parent acceptance, all original suspended constraints,
and the fragment fill equation. Original Fits, reservation and guard carrier
replace universal numeric Ranges. The structural semantic gates stay explicit.

captured_post_semantics retains the complete returned Packet and assignment
iff for the SAME captured cache under its actual native Post. The residual
meaning is arbitrary. PendingRealized and native Keeps supply the heap law.
CompletedHeadReceipt.sound_scan_input uses the original scan Packet and the
aggregate Post to restore original scan-input satisfaction from the actual
head result. The parent lookup remains at the actual local head input heap.
This does not construct a satisfying assignment or prove that all local gates
hold along the complete recursive output history.

## Isolated boundaries through the actual prefix

An IsolatedPending certificate retains a root with an empty native pending
bucket and no incoming references. At an actual decoded recursive boundary,
the original Packet supplies the exact false native candidate flag. Actual
pure selection and actual Restart.decision therefore select another variable.
The same Packet realizes its native handle as available and closed.

Actual getValue, clearing at another root, handle replacement with the same
bucket, both recursion-check branches, and actual nonempty prepared writes
preserve the certificate. The proof uses actual Success receipts. It does not
infer Safe from a generic frame or assume the desired after-certificate.

prefix_isolated uses the literal runPrefix equation to extract the actual
prepared action receipt. PrefixValid alone does not supply that execution.
packet_prefix_complete_isolated calls the original prefix producer once,
retains its full universal PrefixValid family and appends preservation at each
attached parked or narrowed cache. Its initial isolated boundary and decoding
are quantified after the original sufficient bound and old family. These are
not extra inputs to the original producer.

This result covers the selected prefix. It does not cover all ordinary entry,
captured traversal, callback, suffix and recursive output operations. It also
does not derive isolation for every cleared slot. Discharged excludes an
isolated empty pending slot; whole-history persistence or lost-constraint
recovery still needs proof.

## Validation and preserved evidence

All ten modules and Audit pass warning-as-error and all-linter checking with
Lean 4.34.1. The ten source checks produce empty logs. Audit builds {jobs} jobs
and checks axiom dependencies of {dependencies} theorems. Each heavy check
uses one 4 GiB cgroup, with memory.high = memory.max and swap disabled.
The earlier dependency linter warning is replayed by Lake; no source was
changed to suppress it. Public readback prints 21 new theorem signatures and
two data declarations. The three earlier strongest claim signatures and axiom
blocks are byte-identical. Only propext, Classical.choice and Quot.sound occur.
No sorry, admit, new axiom, native_decide or heartbeat setting is introduced.

The immutable evidence snapshot is restart-evidence/20261027-recursive-receipts.
It retains all failed strict attempts and their exact source snapshots,
corrected variants, actual raw logs, cap readback, public declarations, source
contracts, focused source cuts, review bundles, document baselines and helpers.
The manifest covers every stored payload. decoded-files.json retains decoded
hashes for deterministic gzip logs, patches and large payloads. The portable
verify-evidence.py checks payloads, whole sources, cuts, seals and document
preservation, then verifies the committed bytes. Do not edit sealed bundles.

No Haskell source changed. No Haskell test was required for these Lean-only
changes. No new Haskell defect or fix is claimed. Root FINDINGS retains all
previous repaired defects and external repair work, including the extraction
progress boundary. The prior LPO and extraction repairs remain integrated.
The opaque Mu/Union constraint behavior is a documented boundary. Its saved
native recipe remains UNEXECUTED. A storage or Canonical theorem does not
recover removed suspended constraints.

## Next proof work

1. Lift rich per-head receipts through actual ordinary entry, callbacks and
   depth induction into every relevant recursive OutputHistory tag. Keep the
   entire original producer result and quantifier order. Do not add future
   success, desired satisfaction or an after-state invariant to admission.
2. Derive current semantic gates at the actual captured inputs, or state and
   justify the narrow input class that supplies them. Keep Canonical separate
   from fresh arity, child retention and constraint validity.
3. Prove whole-history persistence or exclusion for isolated opaque and parked
   slots, and recover each cleared Holds that can reach a rendered output.
   The selected-prefix result is only the first part of this argument.
4. Compose backward assignment laws at the SAME actual output cache, Caller
   and full Memos. Sibling restoration must retain its captured input cache.
   Connect actual discharge and rendering only at that output endpoint.
5. Close whole recursive acceptance, then coverage and the remaining physical
   Haskell correspondence and contract boundaries. Do not infer these from
   executable simulation or from a count of checked declarations.

Push only non-force to the authorized formalize branch. Leave the whole goal
ACTIVE at this checkpoint. Keep all earlier notes as historical evidence.
'''
name='lean/notes-current-recursive-receipts.md'; data=note.encode(); (root/name).write_bytes(data)
documents.append(name); records.append(dict(path=name,bytes=len(data),sha256=hashlib.sha256(data).hexdigest()))
(area/'document-paths.json').write_text(json.dumps(documents,indent=2)+'\n')
(area/'document-validation.json').write_text(json.dumps(records,indent=2)+'\n')
print(json.dumps(dict(documents=len(documents),modules=len(modules),lines=lines,jobs=jobs,dependencies=dependencies)))
