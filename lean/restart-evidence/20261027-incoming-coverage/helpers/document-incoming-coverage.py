from pathlib import Path
import hashlib,json,re,subprocess
root=Path('/home/tritlo/Code/mcfta');area=Path('/tmp/mcfta-incoming-coverage-20261027')
head=(area/'source-head.txt').read_text().strip();base=(area/'published-base.txt').read_text().strip();stats=json.loads((area/'statistics.json').read_text());public=json.loads((area/'public-validation.json').read_text());upstream=json.loads((area/'final-upstream-refresh.json').read_text());assert public['status']=='pass' and upstream['fetch_exit']==0 and upstream['main_is_ancestor'];assert json.loads((area/'source-validation.json').read_text())['status']=='pass'
audit=(area/'audit-coverage-1/raw.log').read_text();jobs=int(re.search(r'Build completed successfully \((\d+) jobs\)',audit)[1]);deps=int(re.search(r'Checked axiom dependencies of (\d+) MicroCFTA',audit)[1])
prefix=f'''
## Constructive coverage of native child preparation

Source checkpoint: {head}.
The original resource contract now constructs an actual child singleton for
every supplied term accepted by the incoming native value and every original
suspended constraint, under an original satisfying assignment. The proof
constructs an extended assignment that agrees at every old allocated variable.
It satisfies the original and returned states. The actual returned fragment
fills to the supplied term. All old resources, histories, full memo states
and returned cache fields remain. No desired future row, assignment or final
Satisfies is an input.

Terminal children use the original assignment. The proof excludes both
fold rejection and incoming Empty rejection at the same actual endpoint.
Other children use a fresh assignment value at the old counter. Storage and
bounded references retain every old state constraint. Current resource
admission derives all required ranges. Earlier clauses cover generic
incoming updates and the full terminal child packet.

This is symbolic child-preparation coverage. It does not prove that the whole
enumerator selects a parent edge, expands every hole or renders the term.
Fresh Mu and Union slots still use the existing empty stored bucket. A valid
chosen filling does not prove retention for every future filling. Preserve
all earlier retention counterexamples and Haskell repair instructions.

The initial native-to-render soundness theorem and H6 exact finite-tree
preservation keep their full earlier scopes. Next prove constructive coverage
through ordered child traversal, then accepting-edge selection and equality
witness allocation. Whole recursive coverage, semantic selector and pruning
policy contracts, remaining API admissions and physical Haskell correspondence
remain open. The full formalization goal stays ACTIVE.

Three modules contain {stats['lines']} lines and three new public theorems.
All three sources and standalone Audit pass strict checks. Audit passes
{jobs} jobs and checks {deps} theorem dependencies. Public readback has
162 full signature and axiom blocks. All 159 prior blocks and all 82 pinned
prior source modules remain byte exact. Only the three standard Lean axioms
occur. No Haskell source changed. FINDINGS retains every repair handoff.
Details: `lean/notes-current-incoming-coverage.md`.

'''
extra='''
### Child coverage and Haskell repair status

This checkpoint changes Lean proofs only. All earlier Haskell fixes,
regressions and external repair instructions remain below without deletion.
Main remains 8766699b594eaad80381af2eee034c378ccf3192 and is an ancestor.
The LPO and extraction documentation fixes remain integrated. KBO candidate
d7b6a9dfff464eb32c17c314d4825d5b027f1b2d remains unintegrated, unbuilt and
unexecuted. The positive-Int context-reversal finding remains open.
No Haskell source, Cabal file, native test or benchmark changed or ran here.
The new coverage result does not repair the existing opaque-bucket retention
boundary or establish full physical Haskell correspondence.

'''
paths=['NEXT-PROMPT.md','HANDOFF.md','FINDINGS.md','lean/API-COVERAGE.md','lean/COVERAGE.md','lean/README.md','lean/SYSTEM.md','lean/notes-current-system-claim.md','lean/notes-proof-status-20261017.md'];records=[]
for name in paths:
 p=root/name;old=p.read_bytes();saved=area/'prior-documents'/name;saved.parent.mkdir(parents=True,exist_ok=True);assert not saved.exists();saved.write_bytes(old);assert old==subprocess.check_output(['git','show',base+':'+name],cwd=root)
 offset=old.index(b'\n')+1;insert=(prefix+(extra if name=='FINDINGS.md' else '')).encode();new=old[:offset]+insert+old[offset:];p.write_bytes(new);assert new[:offset]+new[offset+len(insert):]==old
 records.append({'path':name,'bytes':len(new),'sha256':hashlib.sha256(new).hexdigest(),'offset':offset,'inserted_bytes':len(insert),'prior_bytes':len(old),'prior_sha256':hashlib.sha256(old).hexdigest()})
note=f'''# Constructive native incoming and child coverage

Source checkpoint: {head}.
Published base: {base}.
Main: {upstream['main']}. The final successful fetch confirms ancestry.
Previous note: `notes-current-enumeration-startup.md`.

## Target and current statements

The top level target remains correctness of the whole CFTA system. It
includes exact finite-tree transformations, enumeration soundness and
coverage, API behavior and physical Haskell correspondence. The complete
target remains open. Preserve the optimized interned core, older constructor
and equality proofs, counterexamples, repairs, marked drafts and evidence.

The new general theorem is
SourcePruningEnumerationChildCompletion.complete_with_fragments_resources_accepting.
It retains the entire original current-resource admission and result packet.
For every original satisfying assignment and concrete term accepted by the
incoming native value and ALL original suspended constraints, it derives a
literal successful singleton at the SAME actual returned cache and caller.
It constructs an assignment that agrees below the original counter and
satisfies both original and returned states. The actual fragment fills to
the supplied term. All work bounds precede these semantic observers.
No future row, desired extended assignment or final satisfaction is supplied.

This proves coverage of symbolic native CHILD PREPARATION. It does not prove
coverage of parent-edge selection, a whole traversal, recursive enumeration,
full hole expansion or concrete rendering. Acceptance uses the existing
native language and guard interpretation at the declared ambient environment.
The proof retains Context, Safe, actual Roots, both native indexes, realized
slots, bounded pending references, Available/closed incoming value, Fits,
finite reservation and the guard annotation carrier. It assumes no desired
future state. It adds no new producer admission to the original child theorem.

The prior run_initial_finite_render_sound theorem keeps its full scope.
Given its genuine native inputs and resources, the literal startup derives
Packet, Canonical, root lookup and mass bound. Own discharged outputs with
successful rendering and checked residuals belong to the original native
root language. Finite arity histories are derived. Remaining native Context,
initial arity, resources and policy contracts stay explicit.

H6 keeps exact finite-tree preservation for its covered closed construction,
original guard-allocation history and empty inherited payload. Any fixed
finite number of rounds has an actual complete call trace with sufficient
mathematical width and fuel. It does not prove convergence or include
withoutRedundantEdges. These global statements are unchanged here.

## Three constructive steps

IncomingNode.run_complete_accepting first derives current WordRanges from
Fits and Room. It invokes the original branch producer once. Original
Satisfies, incoming native acceptance at assignment uv and every incoming
suspended Hold yield an actual row through the branch equivalence. That row
excludes Empty replacement and identifies the same written after state.
The stable runtime family therefore returns its nonempty singleton.
The entire old receipt and all semantic equivalences remain. The outer
returned core is the READ endpoint. It is not the written branch state.

ChildCompletion.complete_with_fragments_resources_terminal_accepting invokes
the original resource producer once. Its semantic observer handles buckets
with a terminal entry. It derives all terminal ranges from the SAME original
reservation. It compares the actual child run and the canonical terminal
run at common representative, native and index fuel, with adequate P/H.
Tuple equality identifies the same raw rows, caller, query, outer state,
waiting map and cache. The original full Memos and Post stay retained.
Equality of query fields never substitutes for equality of full Memos.

Actual recorded-root membership, original forest satisfaction and terminal
Holds prove that the winner denotes the supplied term. The terminal-bucket
equivalence uses EVERY original bucket entry, including duplicates.
The actual raw semantic equivalence supplies a successful member. It excludes
BOTH foldRows=[] and replacement=Empty. Thus the actual raw list is exactly
one hole at the winner, in the same returned cache. That hole fills to the
supplied term and its state satisfies the original assignment.

ChildCompletion.complete_with_fragments_resources_accepting invokes that
terminal-enriched producer once and preserves its complete packet. A
terminal bucket uses the original assignment unchanged. Otherwise it sets
extended := install assignment oldCounter [term]. install_before preserves
every old variable. StorageValid and state_assignment_congr retain the
entire original forest, value slots and residual fragments. Bounded sc.var
and holds_extension transfer every original suspended obligation.

The existing cached preparation semantics supplies an actual singleton.
A common adequate index evaluation identifies the SAME raw rows, caller
and returned cache. The new hole denotes extended oldCounter = term.
The written state satisfies extended. All final numeric Fits and annotation
Heap fields remain those of the original resource packet. No arbitrary
low-fuel uniqueness or supplied future completion is used.

Fresh ordinary nodes retain their bucket. Fresh Mu and Union slots still
store an empty bucket, as in the source. The proof supplies ONE valid filling
for the input model and term. It does not assert that the runtime retains
those dropped constraints or that every future filling satisfies them.
Keep the earlier opaque-retention findings and repairs. The Empty case has
no accepted term and therefore cannot satisfy the observer antecedent.

## Verification and attempts

Three modules contain {stats['lines']} lines and {stats['bytes']} source bytes.
They declare three public theorems and no new public definition, predicate
or structure. All three exact installed sources pass standalone strict
Lean checks. Standalone strict Audit also passes. These strict commands use
-DwarningAsError=true and -Dlinter.all=true. All recorded compiler commands
run serially at a measured 4 GiB cap with zero swap.

The incoming installed build passes 1595 jobs. The terminal installed build
passes 1874 jobs. The complete Audit build passes {jobs} jobs and checks
{deps} theorem dependencies. Its output includes the built general child
module. The existing unused-input dependency warning remains in build logs.
The new successful strict source logs are empty.

Public output has 162 complete signature and axiom blocks with no elision.
All 159 previous blocks match byte exactly. All 82 pinned prior source
modules retain their published bytes. Only propext, Classical.choice and
Quot.sound occur. Audit adds only three imports, with an exact inverse that
recovers its entire previous file. There is no sorry, admit tactic, custom
axiom, native_decide, heartbeat increase or linter suppression.
Public output is {public['bytes']} bytes, SHA256
{public['sha256']}.

Both initial failed attempts remain. Terminal v1 needed an explicit
Fragments.fill reduction for its final hole equality. Its v2 changes only
that proof step. General child v1 needed constructor reduction to identify
two effective-bucket membership types. Its v2 adds only cases incoming at
that proof argument. Neither repair changes admission or conclusion.
Full original contracts recover byte exactly after the declared result
appendix, grouping and theorem-name transformations. Earlier terminal and
fresh-child plans remain as historical proposal evidence. Their local steps
are now proved by these modules. No new native test or benchmark ran.

No Haskell source or Cabal file changed. FINDINGS preserves all earlier
Haskell repair instructions. Main remains integrated with LPO and extraction
documentation fixes. KBO candidate d7b6a9dfff464eb32c17c314d4825d5b027f1b2d
remains unintegrated, unbuilt and unexecuted. The positive-Int context-reversal
finding remains open. Do not report its native regression as passed.

## Remaining work and restart

Next derive constructive coverage through the actual ordered child traversal.
Use agreement on all old variables to retain earlier fragment fillings when
a later child allocates fresh variables. Keep each reached caller, cache,
full memo state, resource forecast and original guard carrier. A per-row
semantic implication is insufficient when raw=[]. Derive real membership.

Then derive selected-edge execution from an accepted parent term. Select an
accepting resident edge, derive actual guard projection and own/inherited
arity, allocate equality witnesses, and prepare the ordered child terms.
Keep actual native semantics throughout. No unrelated graph replaces it.

Whole recursive coverage needs these constructive steps and policy contracts.
Current selector subset and length conditions admit edgesOf := fun _ => [].
They cannot prove coverage of a nonempty language. Supported selectors and
pruning callbacks must retain an accepting edge or an equivalent language.
Stop/depth policies can still park or exhaust. Do not infer discharge,
renderability or unbounded convergence from this child theorem.

Continue deriving public native Context, initial arity, physical/full memo
invariants and resource bounds from actual checked construction. Complete
remaining API obligations and physical Haskell correspondence. Preserve
withoutRedundantEdges and every other earlier scope boundary. No defensible
completion percentage or date is claimed. The full goal stays ACTIVE.

Portable evidence: `restart-evidence/20261027-incoming-coverage/`.
The manifest records stored bytes. decoded-files.json records original
bytes for deterministic gzip payloads. Preserve exact drafts, failed and
successful checks, full public output, contract comparisons, source cuts,
reviews and original document bodies. Run verify-evidence.py with the
snapshot path. Use --committed to compare every payload with Git after the
evidence commit. Keep publication receipts outside the frozen TEMP stage
and archive. Earlier frozen evidence remains unchanged.
'''
name='lean/notes-current-incoming-coverage.md';p=root/name;assert not p.exists();p.write_text(note);paths.append(name);records.append({'path':name,'bytes':len(p.read_bytes()),'sha256':hashlib.sha256(p.read_bytes()).hexdigest()})
(area/'document-paths.json').write_text(json.dumps(paths,indent=2)+'\n');(area/'document-validation.json').write_text(json.dumps(records,indent=2)+'\n');print(json.dumps({'documents':len(paths),'preserved_prior_documents':9,'note_bytes':len(p.read_bytes()),'source_head':head}))
