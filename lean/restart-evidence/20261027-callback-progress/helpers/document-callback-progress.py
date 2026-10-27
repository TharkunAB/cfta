from pathlib import Path
import hashlib,json
root=Path('/home/tritlo/Code/mcfta')
area=Path('/tmp/mcfta-callback-progress-20261027')
head=(area/'source-head.txt').read_text().strip()
base=(area/'published-base.txt').read_text().strip()
public=json.loads((area/'public-validation.json').read_text())
assert public['status']=='pass'
modules=json.loads((area/'modules.json').read_text())
source_bytes=sum((root/'lean/MicroCFTA'/(m+'.lean')).stat().st_size for m in modules)
source_lines=sum(len((root/'lean/MicroCFTA'/(m+'.lean')).read_bytes().splitlines()) for m in modules)
common=f'''
## Native scheduler progress after the actual callback

Source checkpoint: {head}.
The actual native scheduler cannot return stuck from a safe indexed state
that has ProperState and a satisfying finite assignment. ProperState requires
strict nonempty pending paths. Canonical waiting counts identify a blocking
reference. Its source is an actual native candidate, including Mu and Union
when its pending bucket is nonempty. A cycle would require an infinite
strict descent in finite terms. The theorem uses the actual native heap.

The callback producer retains its ENTIRE original admission and result.
Its uniform fuel and actual result precede the new semantic observer.
For any original ProperState and satisfying assignment, the SAME returned
metadata and framed cache have a restart decision different from stuck.
The frame preserves ProperState and the same assignment. The proof uses the
actual returned Packet. No future successful execution is supplied.

This excludes one empty-result route. It does not prove that recording
returns false, a hook emits output, or recursion finishes. Packet alone does
not imply ProperState. Its origin and preservation through native child
preparation remain open. Templates are forbidden patterns, so native term
acceptance alone does not exclude legitimate template pruning. Pending-group
meaning and the early template transformation need separate semantic laws.
The witness designs in the review are source assessments, not executed
countermodels or new physical Haskell defects.

Two modules contain {source_lines} lines and two public theorems. Strict checks
and full Audit pass. Audit passes 4254 jobs and checks 80108 theorem
dependencies. Public readback has 182 complete blocks; all 180 older blocks
form the exact 783343-byte prefix. Only the three standard Lean axioms occur.
All 4251 older non-Audit Lean sources, 100 pinned modules, 447 enumeration
sources and 203 Haskell sources retain their bytes. Only two imports change
Audit. H6, checked finite rendering soundness and finite invocation-or-stop
coverage retain their earlier scopes. End-to-end recursive coverage, frontier
policy, rendering coverage, API admission and Haskell correspondence remain
open. The whole goal stays ACTIVE. Details:
`lean/notes-current-callback-progress.md`.

'''
haskell='''
### Callback progress and external Haskell repair status

No Haskell source, Cabal file, native test or benchmark changed or ran.
All earlier repair handoffs remain below. Main stays
8766699b594eaad80381af2eee034c378ccf3192 and contains the LPO and extraction
documentation fixes. The current pull and fetch pass; main is an ancestor.
KBO candidate d7b6a9dfff464eb32c17c314d4825d5b027f1b2d remains unintegrated,
unbuilt and unexecuted. The positive-Int context-reversal finding remains open.

The new callback result is a Lean scheduler theorem. It establishes no new
physical Haskell defect. External proof work must keep template rejection
separate from automaton acceptance. Packet.bounded permits an empty pending
group. Such a group causes rejection in the modeled oracle. Also, the early
structural template conversion can erase an allowed arrow marker to a hole.
Avoidance of original full templates alone therefore does not justify the
early rejection step without syntax provenance or a law for transformed
templates. These are source-level semantic gaps. The review retains three
unexecuted witness designs; it supplies no compiled full Packet countermodel.

'''
note=f'''# Native scheduler progress after the actual fragment callback

Source checkpoint: {head}.
Published base: {base}.
Main: 8766699b594eaad80381af2eee034c378ccf3192. Pull and fetch pass; ancestry holds.
Previous note: `notes-current-continuation-coverage.md`.

## Full target and strongest current claims

The target remains correctness of the whole CFTA system. It includes exact
finite-tree transformations, enumeration soundness and coverage, ranking and
sampling, public API behavior and physical Haskell correspondence. Preserve
the optimized interned core, older constructor and equality proofs, every
counterexample, repair, marked draft and restart record. The full target is
open. No completion percentage or date is established.

H6, SourceCurrentColdFiniteWarmCalls.constructed_node_calls, proves exact
original finite-tree language preservation for its covered closed construction,
original guard allocation history and empty inherited payload. Every fixed
finite number of pruning rounds has an actual complete modeled call trace
with sufficient mathematical width and fuel. Convergence and
withoutRedundantEdges remain outside that theorem.

Recursive.run_initial_finite_render_sound starts at the literal native
initial cache under its original Context, arity, resource and policy gates.
Each returned output must still be Discharged, render successfully and pass
all returned residual checks. Its rendered term then belongs to the original
root language. Whole enumeration coverage and physical correspondence do not
follow from this conditional soundness result.

The previous finite sibling result retains its whole original resource
packet. Uniform work bounds precede the chosen selected index and original
semantic model. It derives an actual chosen hook invocation or a precise
strictly earlier stopped hook, including the actual prefix, index, caller,
full Memos and local resource witnesses. At the chosen occurrence it
constructs a satisfying filling that fixes all original variables. It does
not promise that an invoked hook returns output.

This checkpoint adds a conditional native scheduler progress result and
attaches it to the actual callback. It excludes a stuck restart at that
callback's exact returned metadata and framed cache.

## Native progress theorem

SourcePruningEnumerationRestart.not_stuck_of_proper takes the actual caller
and cached enumeration state. It requires the existing native CacheValid,
Safe, ProperState, and Satisfies at the caller's actual native heap. Its
residualMeaning, ambient interpretation, stop policy and order policy are
arbitrary. It concludes Restart.decision is different from some stuck.
It does not introduce a new operational definition or restriction to
ordinary nodes. Mu and Union remain in scope.

ProperState is the existing structural condition in EnumerationProgress.
A pending slot without a node has an empty suspended bucket. Every suspended
trie of a slot with a node is valid, nonempty and nonterminal. Every blocking
reference therefore has a strict nonempty path. This condition is stronger
than Canonical and is not a field of the recursive Packet.

The proof follows the actual pure selection definition. A stuck decision
would give a nonempty native candidate list with no unblocked candidate.
CacheValid gives canonical waiting support and native flags. Each blocked
candidate has a suspended reference in a stored source slot. ProperState
excludes the no-node case and supplies a strict path. The nonempty bucket
makes that actual native source a candidate, even at a recursive boundary.
Safe supplies its allocated range. Satisfies and actual forest paths identify
the target's assigned term with that strict subterm of the source assignment.
The existing finite-height argument rules out such a dependency for every
member of a finite nonempty candidate list. No Graph/native correspondence
or desired future scheduler result is assumed.

## Full callback packet and quantifier order

Recursive.callback_complete_progress calls callback_complete_semantics once.
It keeps that theorem's ENTIRE original declaration after a theorem rename,
outer grouping and the appended observer. The retained declaration has 2032
bytes, SHA256 874e0ac089c46007fe07d66015b4f968b6166841e69876422626ba8ba2da8159.
The namespace, variables, instance and local notation context remain.
The original admission is Packet plus FragmentBound. ProperState and a
semantic model are observer antecedents after the operational witnesses.

The result fixes one fuel, result and after state. It retains the returned
Packet, RenderStable, Frame, exact updated types, unchanged open holes and
typing, stable Success for every extra fuel, exact successful singleton,
and the actual continueWith equation for every supplied continuation and
stop/order policy. It also retains the generic assignment equivalence at
the unchanged native heap. Full Memos and the query projection keep their
original roles; no full Memos equality follows from query equality.

After that whole packet, the observer takes arbitrary stop/order, original
ProperState, ambient, residualMeaning, assignment and original Satisfies.
Frame.values preserves ProperState at the SAME framed cache. The existing
assignment equivalence transports the SAME assignment. The returned Packet
supplies the actual native CacheValid and Safe. The new native theorem then
excludes stuck at result.2 and that actual framed cache. All semantic inputs
follow the already fixed work bound and result. No successful future callback,
false recording flag, nonempty output or final assignment is an input.

The theorem also describes a hypothetical restart when recording returns
true. The actual continueWith still prunes in that branch. In the false branch
its retained execution equation identifies this same nonstuck decision as
the recursive restart. The observer does not assert that a true-branch
restart executes.

## Remaining semantic coverage work

Derive and preserve ProperState through actual native preparation, pending
bucket writes, assimilation, child preparation and recursive history. The
initial graph proof and the native Packet do not discharge this obligation.
The new callback frame preservation is proved; the native origin is not.

Do not use native acceptance alone to rule out recording=true. Templates
are forbidden patterns. A wildcard template can intentionally reject an
accepted program. Packet.bounded bounds raw pending IDs but permits an empty
pending group. finishChecks rejects such a group. Early structural template
conversion can erase an allowed arrow marker to a wildcard. Absence of the
original full pattern alone does not imply absence of that transformed
pattern. These are source-level contract observations. The retained review
has three UNEXECUTED witness designs, not compiled full Packet countermodels
or established physical Haskell defects.

The next template proof needs independent original semantic data. Relate
raw holes to the original assignment in partial terms. Prove one-way
matchPartial soundness under completion of those holes. Relate the actual
partial renderer to the filled callback fragment without excluding truncated
markers. Prove that new and resumed pending groups retain a semantic
refutation, and that indexed templates come from the catalog. Derive false
recording from original pending refutation and avoidance of the original and
transformed early patterns, or derive the latter from genuine source syntax
provenance. The callback fragment must fill to assignment uv; actual captured
Admitted receipts can supply that connection. Do not supply a desired future
false result or a final satisfying state as an original premise.

Existing original resource producers exclude local malformed callback and
selected-prefix faults at their chosen bounds. They still permit explicit
recursive depth exhaustion, exact unsupported ordinary fallback, unsupported
projection and stopped recursive hooks. ResourceHistory describes emitted
outputs and gives no history for a stopped zero-output branch. A global stop
classification needs a stronger actual recursive induction, with each exact
endpoint and full Memos. The current native progress theorem excludes only
some stuck, not these other stops.

Continue through depth and user-stop policy, recursive Mu/Union frontiers,
Discharged outputs and concrete rendering coverage. Fresh recursive
boundaries can remain parked with empty buckets. Selector permutation and
projection support still have explicit gates. Public source sorting,
canonical map construction, API admission and physical Haskell correspondence
remain separate bridges. The whole goal stays ACTIVE.

## Checks, attempts and preservation

The two modules have {source_lines} lines and {source_bytes} bytes. They add two
public theorems and no definition, structure or predicate. Both installed
sources and standalone Audit pass -DwarningAsError=true and -Dlinter.all=true.
Successful source logs are empty. Audit has its expected 56-byte dependency
count. The native dependency build passes 1360 jobs. Full Audit passes 4254
jobs and checks 80108 theorem dependencies. Lake replays the unchanged
unused-input warning from InternedFreshOrdinaryClosedCompletion. No warning
is suppressed. Every compiler/build/public command runs serially under
measured 4 GiB memory.max/high and zero swap.

Seven actual compiler/build/public commands are retained. One fails:
native-progress-strict-1. Native v1 is UNTESTED. V2 generalizes only the
residual interpretation and fails strict1 in the local noOffered proof:
constructor contradictions need explicit elimination, its nil case is already
rewritten, and a local candidates definition needs an explicit change.
Root v3 repairs those proof steps and passes strict2. Its public statement
is byte identical to v2. Callback root v1 is an explicitly INCOMPLETE,
UNTESTED draft. V2 imports the actual semantic producer, uses the finalized
native lemma interface and updates its module description. It passes its
first strict check. All drafts and the entire 8499-byte failed log remain.

Public readback has 182 full signature/axiom blocks, {public['bytes']} bytes,
SHA256 {public['sha256']}.
All 180 prior blocks form the exact 783343-byte prefix. The two new blocks
have 9091 bytes and 119 lines. Only propext, Classical.choice and Quot.sound
occur. No sorry, admit tactic, custom axiom, native_decide, heartbeat increase
or linter suppression is used. The public-validation helper first fails
because its literal name boundary misses the existing universe suffix on
complete_prefix_invocation. The corrected helper accepts that suffix and
verifies both complete outputs. No compiler rerun was needed for this repair.

All 100 prior strong modules, 447 prior enumeration sources, 4251 old
non-Audit Lean sources and 203 Haskell sources retain their bytes. Removing
only the two new imports recovers the entire old Audit source. Removing each
new document insertion recovers all nine entire previous restart documents.
All previous frozen evidence remains unchanged.

## Haskell handoff and portable evidence

No Haskell source or Cabal file changed. No native test or benchmark ran.
Main contains the LPO and extraction documentation fixes. Candidate
KBO d7b6a9dfff464eb32c17c314d4825d5b027f1b2d remains unintegrated, unbuilt and
unexecuted. Its positive-Int context-reversal finding remains open. FINDINGS
retains all earlier external repair instructions and records the current
source-level template/pending semantics gaps without claiming a new runtime
repair or physical defect.

Portable evidence: restart-evidence/20261027-callback-progress/.
The manifest records stored bytes. decoded-files.json records original bytes
for deterministic gzip payloads. Run verify-evidence.py on the snapshot.
Use --committed after the evidence commit to compare every payload with Git.
Preserve all drafts, failures, public output, exact old-contract comparison,
source copies/cuts, final reviews and all nine entire old document bodies.
Keep publication receipts outside frozen TEMP and archive.
'''
paths=['NEXT-PROMPT.md','HANDOFF.md','FINDINGS.md','lean/API-COVERAGE.md','lean/COVERAGE.md','lean/README.md','lean/SYSTEM.md','lean/notes-current-system-claim.md','lean/notes-proof-status-20261017.md']
records=[]
for name in paths:
    target=root/name;old=(area/'prior-documents'/name).read_bytes();assert target.read_bytes()==old,name
    offset=old.index(b'\n')+1;extra=(common+(haskell if name=='FINDINGS.md' else '')).encode()
    data=old[:offset]+extra+old[offset:];assert data[:offset]+data[offset+len(extra):]==old
    target.write_bytes(data)
    records.append(dict(path=name,bytes=len(data),sha256=hashlib.sha256(data).hexdigest(),offset=offset,inserted_bytes=len(extra),old_bytes=len(old),old_sha256=hashlib.sha256(old).hexdigest(),whole_old_body_preserved=True))
name='lean/notes-current-callback-progress.md';target=root/name;assert not target.exists();target.write_text(note)
records.append(dict(path=name,bytes=target.stat().st_size,sha256=hashlib.sha256(target.read_bytes()).hexdigest()))
paths.append(name)
(area/'document-paths.json').write_text(json.dumps(paths,indent=2)+'\n')
(area/'document-validation.json').write_text(json.dumps(records,indent=2)+'\n')
print(json.dumps(dict(documents=len(paths),old_bodies_retained=9,source_lines=source_lines,source_bytes=source_bytes,new_note_bytes=target.stat().st_size)))
