from pathlib import Path
import hashlib,json,subprocess
root=Path('/home/tritlo/Code/mcfta');area=Path('/tmp/mcfta-enumeration-startup-20261027')
head=(area/'source-head.txt').read_text().strip();base=(area/'published-base.txt').read_text().strip()
assert json.loads((area/'public-validation.json').read_text())['status']=='pass'
assert json.loads((area/'source-validation.json').read_text())['status']=='pass'
prefix=f'''
## Checked rendering from the literal native startup

Source checkpoint: {head}.
The initial enumeration packet now follows from an available closed native
root, the original native Context and metadata with no pending templates.
The proof derives Canonical storage, both native indexes, the exact root
handle and lookup, and zero suspended mass. It uses the literal single-root
startup state. Empty is initially expandable. Mu and Union are initially
parked when their suspended bucket is empty. Every unallocated slot has a
false expandable flag.

run_initial_finite_render_sound connects that startup to the finite driver.
For each fully discharged output whose native rendering succeeds and whose
returned residuals check, the rendered term belongs to the original root's
native language. The proof constructs an assignment for the original,
output and rendered states. Stable execution, all original resource packets,
all resource histories and every output Canonical certificate remain.
No supplied startup Packet, Canonical, mass bound, root storage or root lookup
is an input. Genuine initial arity, native Context, numerical resources,
annotation carrier, selector and reservation contracts remain explicit.
The model handle encoding remains separate from physical Haskell NodeId
extraction. The proof retains the full caller and all memo families.

H6 retains exact accepted finite trees for its covered construction and any
fixed finite number of pruning rounds, with sufficient width and fuel.
Enumeration coverage, remaining public admissions and API obligations, and
physical Haskell correspondence remain open. A selector that returns []
satisfies the current subset and length contracts. Coverage needs a stronger
edge-retention contract. The full formalization goal stays ACTIVE.

Two modules contain 198 lines and two new theorems. Both pass strict checks.
Audit passes 4234 jobs and checks 80044 theorem dependencies. Public readback
contains 159 full signature and axiom blocks. All 157 prior blocks and all
80 pinned prior source modules remain byte exact. Only the three standard
Lean axioms occur. No Haskell source changed. FINDINGS retains every repair
handoff. Details: `lean/notes-current-enumeration-startup.md`.

'''
extra='''
### Startup proof and Haskell repair status

This checkpoint changes Lean proofs only. All previous Haskell fixes and
external repair instructions remain below without deletion. The latest
successful fetch reads main at 8766699b594eaad80381af2eee034c378ccf3192.
Main remains an ancestor. The LPO and extraction documentation fixes remain
integrated. KBO candidate d7b6a9dfff464eb32c17c314d4825d5b027f1b2d remains
unintegrated, unbuilt and unexecuted here. The positive-Int context-reversal
finding remains open. No native test or benchmark ran in this checkpoint.
The Empty, Mu and Union startup flags match the existing source predicate.
They do not establish a new Haskell defect or full native correspondence.

'''
paths=['NEXT-PROMPT.md','HANDOFF.md','FINDINGS.md','lean/API-COVERAGE.md','lean/COVERAGE.md','lean/README.md','lean/SYSTEM.md','lean/notes-current-system-claim.md','lean/notes-proof-status-20261017.md']
records=[]
for name in paths:
 p=root/name;original=p.read_bytes();saved=area/'prior-documents'/name;saved.parent.mkdir(parents=True,exist_ok=True);assert not saved.exists();saved.write_bytes(original)
 assert original==subprocess.check_output(['git','show',base+':'+name],cwd=root)
 offset=original.index(b'\n')+1;insert=(prefix+(extra if name=='FINDINGS.md' else '')).encode()
 updated=original[:offset]+insert+original[offset:];p.write_bytes(updated)
 assert updated[:offset]+updated[offset+len(insert):]==original
 records.append({'path':name,'bytes':len(updated),'sha256':hashlib.sha256(updated).hexdigest(),'offset':offset,'inserted_bytes':len(insert),'prior_bytes':len(original),'prior_sha256':hashlib.sha256(original).hexdigest()})
note=f'''# Native enumeration startup and checked rendered acceptance

Source checkpoint: {head}.
Published base: {base}.
Main: 8766699b594eaad80381af2eee034c378ccf3192. It remains an ancestor.
Previous note: `notes-current-recursive-driver-arity.md`.

## Target and strongest statements

The top level target remains correctness of the whole CFTA system. It
includes exact finite-tree transformations, enumeration soundness and
coverage under explicit contracts, API behavior and physical Haskell
correspondence. The complete target remains open. Preserve the optimized
interned core, older constructor and equality proofs, counterexamples,
repairs, marked drafts and all earlier evidence.

The new theorem is
SourcePruningEnumerationRecursive.run_initial_finite_render_sound.
Start from an actual available closed interned value, the original native
Context with its full memo state, and metadata.pending=[]. The proof
derives the literal initial enumeration state and a stable finite-driver
outcome. Every own output retains Canonical storage. For each fully
discharged output with successful native rendering and checked returned
residuals, the rendered term belongs to the ORIGINAL native root language.
An assignment satisfies the original startup, output and rendered states.
The rendered term is assignment 0. The rendering retains its Frame.
The original empty suspended bucket is the actual initial bucket.
The full old result, including all resource histories, remains.

No desired acceptance, final Satisfies, supplied future heap or arity
history is an input. Startup Packet, Canonical, suspended-mass bound and
stored-root/native-lookup observations are now derived. Genuine initial
arity, native Context, current Fits, annotation carrier, selector subset
and length, and finite reservation remain explicit. Arbitrary ceiling is
allowed because the initial suspended mass is zero.

H6, SourceCurrentColdFiniteWarmCalls.constructed_node_calls, remains the
strongest global exact finite-tree construction theorem. Its covered closed
construction, original guard-allocation history and empty inherited payload
supply an actual call trace for any fixed finite number of rounds.
Sufficient mathematical width and fuel make every actual node call complete.
The final value accepts exactly the original finite trees at every ambient
environment. Convergence and withoutRedundantEdges remain separate limits.

## Literal initialization

SourcePruningEnumerationRecursive.initial_packet uses the original native
Context, Available root, root.free=[] and metadata.pending=[]. Context
supplies native coherence. Actual available readback derives encodeNode and
lookupNode for the same root and heap. The startup has counter 1, UVar 0,
one pending root slot with an empty suspended bucket, no guard obligations,
empty ancestry and no waiting counts. The expandable flag at 0 is exactly
!recursiveBoundary root. Every other slot has flag false.

Empty remains expandable. Mu and Union remain parked with the empty
bucket. This follows the existing Haskell predicate. A parked initial
outcome need not be Discharged. The rendered theorem therefore keeps its
own Discharged, render-success and residual-check observations.
The model handle 0 and UVar 0 are distinct concepts. The proof follows the
existing encodeNode convention. It does not prove physical NodeId extraction
or the complete Haskell representation of maps and union-find storage.
Missing union-find entries retain the existing implicit-root convention.
Identity Roots outside the allocated domain does not allocate more variables.

The packet proof derives Safe, PendingReferences, CacheValid, finite
Stratified order and bounded pending templates. Existing initial lemmas
derive storage, live roots, pending references, canonical tries and waiting
counts. Native flags use the actual decoded root, including missing slots.
The native caller and full Memos remain unchanged. Empty metadata.pending
makes its reference bound vacuous; arbitrary pending metadata needs a
separate proof. Other metadata fields retain their original types and values.
The independent graph, policy edgesOf and constrained-recursion flag remain
at their existing boundaries. This theorem proves the modeled startup
fields and contracts, not full public Haskell initialization correspondence.

The direct consumer invokes initial_packet once and the existing finite
render producer once. It fixes uv=0, bucket=[] and the same derived handle
and original value. It derives mass=0<=ceiling. It discharges only the
original stored-root and native-lookup observer antecedents. Exact literal
comparison retains the entire old result after these specializations.

## Validation and retained attempts

Two modules contain 198 lines, 12669 source bytes and two public theorems.
Both first strict checks pass with empty logs. The installed packet build
passes 1663 jobs. Audit passes 4234 jobs and checks 80044 theorem dependencies.
Standalone strict Audit passes. Standalone strict checks use
-DwarningAsError=true and -Dlinter.all=true. All recorded checks use a
measured 4 GiB cap and zero swap.

Public readback has 159 complete signature and axiom blocks. Both new
blocks are printed in full. All 157 previous blocks match byte exactly.
All 80 pinned prior source modules retain their published bytes. Only
propext, Classical.choice and Quot.sound occur. No new public definition,
predicate or structure is added. There is no sorry, admit tactic, custom
axiom, native_decide, heartbeat increase or linter suppression.
The existing unused-input dependency warning remains in installed build
logs. New strict source logs are empty.

The public output is 539153 bytes, SHA256
a2bd227d4d5d8e123572c1b0efd409f46b27530c41752295b59bd9524ada1a84.
The first Audit integration put imports after its existing commands.
Lean rejected that import placement. The corrected insertion adds only
two imports to the existing import block. Its exact inverse recovers all
previous Audit bytes. The failed source, log, report and repair remain.
Neither proof source changed. No Haskell source, Cabal file, native test or
benchmark changed. FINDINGS keeps every earlier Haskell repair handoff.
The LPO and extraction documentation fixes remain integrated. KBO candidate
d7b6a9dfff464eb32c17c314d4825d5b027f1b2d remains unintegrated, unbuilt and
unexecuted. The positive-Int context-reversal finding remains open.

## Remaining work and restart

Prove genuine enumeration coverage for supported policies. The current
selector subset and length contracts allow edgesOf to return []. They cannot
imply completeness for a nonempty language. The old graph enumeration has
its own coverage result under CompleteGraph and IntersectionCorrect.
It does not supply native recursive pruning coverage or arbitrary callback
completeness. Coverage needs semantic edge retention and policy contracts.

A bounded next coverage step is IncomingNode.run_complete_accepting.
IncomingNodeResources.initial_ranges derives current WordRanges from
Fits and Room. IncomingBranchesLanguage.run_complete_branches has an actual
branch-existence equivalence. An original satisfying assignment that accepts
the incoming value and inherited constraints can use that equivalence to
exclude an empty result and derive the actual stable singleton branch.
Retain the complete Post and full Memos. Keep the read core and written core
distinct. Do not assume future success or universal traversal/fold ranges.
This is a proposed next theorem. It is not proved by this checkpoint.

Continue public admission from actual checked construction into native
Context, initial arity, physical/full memo invariants and resource bounds.
Canonical enumeration storage alone does not supply those native invariants.
Complete remaining API obligations and physical Haskell correspondence.
Keep convergence, withoutRedundantEdges and every prior contract boundary.
No defensible completion percentage or date is claimed. The full goal stays
ACTIVE after publication.

Portable evidence: `restart-evidence/20261027-enumeration-startup/`.
The manifest records stored bytes. decoded-files.json records original
bytes for deterministic gzip payloads. Preserve all exact sources, drafts,
checks, public output, contract comparisons, source cuts, reviews and
original document bytes. Run verify-evidence.py with the snapshot path.
Use --committed after publication to compare all payload bytes with Git.
Publication receipts stay outside the frozen TEMP stage and archive.
'''
name='lean/notes-current-enumeration-startup.md';p=root/name;assert not p.exists();p.write_text(note)
records.append({'path':name,'bytes':len(p.read_bytes()),'sha256':hashlib.sha256(p.read_bytes()).hexdigest()});paths.append(name)
(area/'document-paths.json').write_text(json.dumps(paths,indent=2)+'\n');(area/'document-validation.json').write_text(json.dumps(records,indent=2)+'\n')
print(json.dumps({'documents':len(paths),'preserved_prior_documents':9,'note_bytes':len(p.read_bytes()),'source_head':head}))
