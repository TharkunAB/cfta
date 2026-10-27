from pathlib import Path
import hashlib
import json

root = Path('/home/tritlo/Code/mcfta')
area = Path('/tmp/mcfta-continuation-coverage-20261027')
head = (area / 'source-head.txt').read_text().strip()
base = (area / 'published-base.txt').read_text().strip()
modules = json.loads((area / 'modules.json').read_text())
source_bytes = sum((root / 'lean/MicroCFTA' / (module + '.lean')).stat().st_size for module in modules)
source_lines = sum(len((root / 'lean/MicroCFTA' / (module + '.lean')).read_bytes().splitlines()) for module in modules)
public = json.loads((area / 'public-validation.json').read_text())
assert public['status'] == 'pass'
common = f'''\n## Actual finite recursive invocation or an exact earlier hook stop

Source checkpoint: {head}.
The modeled finite recursive sibling scan now reaches a chosen accepted
edge's actual hook invocation or identifies a strictly earlier stopped hook.
The result derives the actual completed prefix and its exact list index.
Duplicate edge occurrences remain distinct. The event keeps its actual input
caller, full input Memos, Packet, resource forecast and reservation. Its
completed head keeps its own caller, full Memos, cache and local Post.

At the chosen index, the fragment has a satisfying filling that fixes all
original variables. At an earlier index, the result keeps the exact hook
outputs, reason, optional endpoint and aggregate stopped result. The stopping
receipt is outside the processed prefix. A stop in the chosen hook itself
still counts as a reached chosen invocation. No callback success is assumed.

One work bound is uniform before every extra, index and semantic model.
Event witnesses can depend on those later inputs. The parent wrapper derives
an accepting selected edge and index from the original stored model and a
selector permutation. It derives finite Complete from the existing theorem.
It requires explicit support for the FULL selected list. The primary observer
only needs support for the chosen prefix. The whole primary packet and its
uniform observer remain. Context alone does not derive projection support.

This closes invocation-or-precise-stop coverage through actual finite hooks.
It does not exclude earlier hook stops or callbacks that return no output.
Next prove semantic callback progress and justify the depth, stop and frontier
policies from original inputs. Discharged rendering coverage, public API
admission and physical Haskell correspondence remain open. H6 and conditional
finite rendered soundness keep their earlier scopes. The full goal is ACTIVE.

Four modules contain {source_lines} lines and four public theorems. All installed
sources and standalone Audit pass strict checks. Audit passes 4252 jobs and
checks 80105 theorem dependencies. Public readback has 180 complete blocks;
all 176 prior blocks remain an exact prefix. All 4247 older non-Audit Lean
sources, 96 pinned prior modules and 203 Haskell sources retain their bytes.
Only the three standard Lean axioms occur. Details:
`lean/notes-current-continuation-coverage.md`.

'''
haskell = '''\n### Finite recursive coverage and Haskell repair status

This checkpoint changes Lean proofs only. Every earlier Haskell repair,
regression and external repair instruction remains below without deletion.
Main remains 8766699b594eaad80381af2eee034c378ccf3192, including the LPO and
extraction documentation fixes. The current pull and fetch pass; main is
an ancestor. KBO candidate d7b6a9dfff464eb32c17c314d4825d5b027f1b2d remains
unintegrated, unbuilt and unexecuted. The positive-Int context-reversal
finding remains open. All 203 pinned Haskell sources retain their bytes.
No Haskell source, Cabal file, native test or benchmark changed or ran.

The identified hook stop is a formal operational outcome. This theorem does
not establish a new physical Haskell defect or runtime repair. Projection
support and selector policies remain explicit. Physical canonical map
construction, source sorting and handle extraction remain separate bridges.

'''
note = f'''# Actual finite recursive invocation coverage with precise earlier stops

Source checkpoint: {head}.
Published base: {base}.
Main: 8766699b594eaad80381af2eee034c378ccf3192. Pull and fetch pass; ancestry holds.
Previous note: `notes-current-native-scan-coverage.md`.

## Full target and current statement

The full target remains correctness of the whole CFTA system. It includes
exact finite-tree transformations, enumeration soundness and coverage, API
behavior and physical Haskell correspondence. Keep the optimized interned
core, older constructor and equality targets, every counterexample, repair,
marked draft and restart record. The full target remains open.

NativeFiniteSiblingResources.alternatives_finite_complete_resources_accepting
extends the original direct finite sibling resource induction. It retains
its complete original admission and result. One bound fixes the actual
aggregate result before every extra, chosen index and semantic model.
The observer takes the original selected index, original satisfying assignment,
acceptance by that edge and projection support for the earlier selected
prefix. It constructs an event index at or before the chosen index.

At that event, the actual run on selectedEdges.take eventIndex completes.
Its processed length equals eventIndex. It reaches the actual head caller
and full input Memos, with an aggregate original-to-input Post, Packet,
Fits, annotation carrier and HeadReserved at that exact original stage.
The captured call uses the same work bound and captured cache. It completes
at the event's own branch caller, queries, full Memos and cache, with a local
Post and ReceiptAt certificate. A literal whole-list Invocation is derived.
The branch endpoint need not equal the aggregate final scan endpoint.

The event has exactly the following alternatives:

- At the chosen index, the event edge is the chosen edge. A constructed
  assignment fixes every original variable. It satisfies the original state
  at its original heap and the returned branch cache at its own native heap.
  Filling the actual fragment gives the captured variable's original value.
- At a strictly earlier index, the actual hook returns stopped. Its precise
  outputs, reason and optional reached endpoint remain. The aggregate result
  is that same continuation stop, with the actual completed prefix receipts
  and prefix outputs followed by the stopped hook outputs. Its stopped
  OutcomeResources remain at eventIndex + 1. The stopped current receipt is
  outside the processed prefix.

A stopped chosen hook still counts as a reached chosen invocation. The theorem
does not supply callback success or exclude legitimate callback pruning.
The bound is uniform. Event witnesses may depend on extra, index and model.
It does not assert one fixed existential event for every extra.

## Original policies and resource scope

The primary keeps the original Packet, ready captured variable, exact stored
ordinary parent, actual lookup, selector membership and IncomingAvoid.
It keeps original Fits, annotation Heap, selector membership and length
policies, captured suspended mass, inherited length and ScanReserved.
The smaller-depth Complete contract is the same original input.
No future heap, desired invocation, desired assignment or callback success
replaces these original conditions.

Prefix support means: each earlier selected edge whose arity is allowed has
a successful current projection result. It is a statement about the immutable
original edge and captured inherited bucket. Context alone does not derive it.
It does not impose projection support on later alternatives.

NativeFiniteSiblingResources.parent_finite_complete_resources takes the
original stored satisfying parent model and an actual selected-list Perm.
It derives parent meaning, an accepted selected edge and that edge's actual
index. It requires support for the FULL selected list, which supplies the
chosen-prefix support. It derives Complete with Recursive.finite_complete
and calls the stronger sibling producer once. It retains the ENTIRE primary
existential packet and observer under explicit grouping. The parent model
precedes its outer bound; chosen index and edge precede every extra. The
retained primary observer remains uniform after the bound. Event witnesses
can still depend on extra. Neither whole scan completion nor chosen-hook
completion follows from the all-selected projection support.

## Proof construction

SourcePruningEnumerationFiniteHeadCoverage retains the entire original head
proposition. It calls the accepted native head producer once. The literal
head run at zero extras derives HeadCacheBounds through the existing observed
bounds theorem. Original edge padding, cache mass ceiling and finite callback
resources remain unchanged. The appended semantic observer follows all
operational witnesses and the exact unsupported-or-outcome result. It
constructs accepted captured completion while preserving the actual callback
outcome, full Memos and captured cache restore.

SourcePruningEnumerationContinuationInvocation proves
NativeContinuations.complete_prefix_invocation. A completed actual prefix
and the literal next completed captured call derive the existing whole-list
Invocation relation. The proof follows actual complete hooks and advanceable
other receipts. It eliminates impossible stopped-prefix equations by
constructor disjointness. It does not require success or output from the
chosen hook. No new operational definition or policy predicate is introduced.

SourcePruningEnumerationFiniteSiblingCoverage calls the strengthened head
once at each inductive step. An unsupported head contradicts chosen acceptance
at index zero or the explicit support for an earlier prefix occurrence.
A completed hook supplies the actual next caller and full Memos. Its Post,
rather than the earlier head Post alone, transports the original native model
to the suffix and retains the original parent lookup. The captured cache and
metadata remain fixed. The induction shifts the original resource stage,
composes the actual Post and constructs the actual completed take prefix.
The generic prefix lemma then derives the exact whole-list Invocation.
A stopped hook constructs the chosen event if its index is zero, or the
strictly earlier exact stop otherwise. No desired future execution is given.

SourcePruningEnumerationFiniteParentCoverage derives the chosen edge from
independent parent meaning and the modeled selector permutation. Its single
primary call supplies the original resource packet and the event observer.
It specializes that observer without discarding its universal version.

## Verification and retained attempts

The four modules contain {source_lines} lines and {source_bytes} bytes. They declare four
public theorems and no definition, predicate or structure. All installed
sources and standalone Audit pass -DwarningAsError=true and -Dlinter.all=true.
Commands run serially under measured 4 GiB memory.max/high and zero swap.
All successful source strict logs are empty. Standalone Audit records its
expected 56-byte theorem dependency count.

The supporting head and invocation build passes 1987 jobs. The sibling build
passes 1990 jobs. Full Audit includes the parent wrapper and passes 4252 jobs,
checking 80105 theorem dependencies. The unchanged unused-input dependency
warning remains in the Lake logs. No new warning is suppressed.

Public readback contains 180 complete signature and axiom blocks, {public['bytes']}
bytes, SHA256 {public['sha256']}.
The 176 old blocks form the exact 710226-byte prefix. The four new blocks
occupy 73117 bytes and 892 lines. All 96 pinned prior modules, 443 older
Enumeration sources, all 4247 old non-Audit Lean sources and 203 Haskell sources
retain their bytes. Removing only four inserted imports recovers the entire
old Audit file. Only propext, Classical.choice and Quot.sound occur. No sorry,
admit tactic, custom axiom, native_decide, heartbeat increase or linter
suppression is used.

Fourteen actual compiler/build/public commands are retained. Five fail:
head strict1, invocation strict1 and strict2, sibling strict1 and strict2.
Head v1 fails because Satisfies lacks its existing namespace open. Root v2
adds only EnumerationCorrectness to that open and passes strict2. Invocation
v1 fails because prefix is a reserved identifier. V2 renames that bound list
to earlierEdges. It then fails in seven impossible stopped=complete arms.
V3 adds only explicit cases elimination after their existing simplifications
and passes strict3. Its v2 public statement is unchanged.

Sibling v1 is an untested draft. V2 repairs a local query composition before
the first strict check. Strict1 fails because observer lets must be reduced
before semantic introductions, and because a notation was used as a simp
name. Root v3 repairs those proof steps. Strict2 then fails to infer the width
of a local hook. Root v4 gives that hook its existing full type and passes
strict3. Every sibling public statement from v2 through v4 is byte identical.
Parent v1 remains untested. V2 dedents only its copied specialized event block
before the first check. It passes strict1. Every exact failed source, raw
log, repair and successful check remains. Untested drafts are not compiler
results.

Literal comparisons recover the entire old head declaration, 4589 bytes,
SHA256 caff96663d7effd955218ba8dc81ba4df533e227d61df0e77966276cfc465990,
and the entire old sibling declaration, 4149 bytes,
SHA256 85cab7c443446f4150a095651cabf7cad9ea9177700122e686078fac5cdd699d.
Only the appended observers and new theorem names are removed. The parent
retains the entire 7129-byte primary existential result and observer, SHA256
f46474658ecba97da238f5f9030c2cf9ceb02087d9e480a432e3d1e68361582f,
with only outer grouping. Smaller comparison records have explicit scopes:
the sibling's 4102-byte input/result cut excludes its 47-byte theorem header;
the primary's 6857-byte conjunction excludes its 272-byte existential prefix.

## Next semantic coverage and global limits

Next classify the actual stopped-hook reasons under the original callback
admission. Prove which stops are excluded by an accepted model and sufficient
recursive depth. Preserve genuine user stop and depth policies explicitly.
A completed hook can return no output after recordTypes or a stuck restart.
The current invocation theorem does not prove that those empty outcomes are
incompatible with a desired accepted tree. Connect the actual callback and
smaller-depth ResourceHistory to a satisfying descendant or a precise
remaining frontier condition. Do not assume that every invoked callback
completes, produces output or already satisfies the desired final model.

Continue through the actual recursive driver and justify its frontier policy.
Fresh Mu and Union still use empty stored buckets and can remain parked.
A satisfying symbolic fragment does not prove hole unfolding, Discharged
outputs or concrete rendering. Derive the remaining projection-support
origins and public selector correspondence. Physical canonical map
construction and source sorting remain separate implementation bridges.

H6 retains exact finite-tree language preservation for its covered closed
construction, original guard allocation history and empty inherited payload.
Any fixed finite number of pruning rounds has an actual complete call trace
with sufficient mathematical width and fuel. Convergence and
withoutRedundantEdges remain outside that theorem.

run_initial_finite_render_sound retains soundness from literal native startup
under its original Context, arity, resource and policy conditions. Each output
must still be Discharged, render successfully and pass returned residual
checks. Its rendered term then belongs to the original root language. Whole
enumeration coverage, remaining API admission and physical Haskell
correspondence remain open. The whole goal stays ACTIVE. No completion
percentage or date is claimed.

## Haskell handoffs and restart evidence

No Haskell source or Cabal file changed. No native test or benchmark ran.
Main includes the LPO and extraction documentation fixes. KBO candidate
d7b6a9dfff464eb32c17c314d4825d5b027f1b2d remains unintegrated, unbuilt and
unexecuted. The positive-Int context-reversal finding remains open. FINDINGS
retains all prior Haskell repair handoffs. The precise modeled hook stop
is not a new physical Haskell defect or runtime repair.

Portable evidence: restart-evidence/20261027-continuation-coverage/.
The manifest records stored bytes. decoded-files.json records original bytes
for deterministic gzip payloads. Run verify-evidence.py with the snapshot path.
Use --committed after the evidence commit to compare every payload with Git.
Preserve all drafts, failures, complete public output, exact contract
comparisons, inspected source copies/cuts, final reviews and all nine complete
old document bodies. Keep publication receipts outside frozen TEMP and archive.
All earlier frozen evidence remains unchanged.
'''
paths = ['NEXT-PROMPT.md','HANDOFF.md','FINDINGS.md','lean/API-COVERAGE.md',
    'lean/COVERAGE.md','lean/README.md','lean/SYSTEM.md','lean/notes-current-system-claim.md',
    'lean/notes-proof-status-20261017.md']
records=[]
for name in paths:
    target = root/name
    old = (area/'prior-documents'/name).read_bytes()
    assert target.read_bytes()==old,name
    offset=old.index(b'\n')+1
    extra=(common+(haskell if name=='FINDINGS.md' else '')).encode()
    data=old[:offset]+extra+old[offset:]
    assert data[:offset]+data[offset+len(extra):]==old
    target.write_bytes(data)
    records.append({'path':name,'bytes':len(data),'sha256':hashlib.sha256(data).hexdigest(),
        'offset':offset,'inserted_bytes':len(extra),'old_bytes':len(old),'old_sha256':hashlib.sha256(old).hexdigest(),
        'whole_old_body_preserved':True})
name='lean/notes-current-continuation-coverage.md'
target=root/name
assert not target.exists()
target.write_text(note)
records.append({'path':name,'bytes':target.stat().st_size,'sha256':hashlib.sha256(target.read_bytes()).hexdigest()})
paths.append(name)
(area/'document-paths.json').write_text(json.dumps(paths,indent=2)+'\n')
(area/'document-validation.json').write_text(json.dumps(records,indent=2)+'\n')
print(json.dumps({'documents':len(paths),'old_bodies_retained':9,'common_insert_bytes':len(common.encode()),'new_note_bytes':target.stat().st_size,'source_lines':source_lines,'source_bytes':source_bytes}))
