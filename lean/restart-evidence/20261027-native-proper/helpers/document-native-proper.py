from pathlib import Path
import hashlib
import json

root = Path('/home/tritlo/Code/mcfta')
area = Path('/tmp/mcfta-native-proper-20261027')
head = (area / 'source-head.txt').read_text().strip()
base = (area / 'published-base.txt').read_text().strip()
public = json.loads((area / 'public-validation.json').read_text())
assert public['status'] == 'pass'
common = f'''
## Proper native paths from startup through completed captured edges

Source checkpoint: {head}.
Native startup now derives ProperState with the entire original Packet.
Actual preparation, incoming writes, assimilation, folds, terminal merging,
child dispatch and completed ordered child traces preserve proper paths.
The cache observers also cover rejected branches that retain a cache.
Actual child descent supplies the nonempty trie inputs. Current heap
annotations supply projected trie validity. Mu and Union remain in scope.

The captured resource producer retains its ENTIRE original declaration.
Its work bounds, actual result and full resource packet precede the new
observer. Given the original ProperState and an accepted original model,
the same constructed assignment satisfies the actual completed cache.
That cache is proper and its native restart decision cannot be stuck.
No future proper state, callback success or final model is supplied.

This closes local native invariant preservation through completed captured
execution. Full recursive origin through partial narrowing, selected prefixes
and stopped histories remains open. ProperState alone does not imply Safe
or Packet. Template pruning, depth and stop policy, recursive frontiers,
discharge and rendering coverage, API admission and physical Haskell
correspondence remain open. H6 exact finite pruning language preservation,
conditional rendered soundness and finite invocation-or-stop coverage retain
their previous scopes. The whole goal remains ACTIVE.

Fourteen modules add 1772 lines, 102547 bytes and 30 public theorems.
All strict checks pass. Full Audit passes 4268 jobs and checks 80193 theorem
dependencies. Public readback has 212 complete blocks. The 182 old blocks
form the exact 792434-byte prefix. Only the three standard Lean axioms occur.
All 4253 prior non-Audit Lean sources, 102 pinned modules, 449 enumeration
sources and 203 Haskell sources retain their bytes. Audit adds only imports.
Details: `lean/notes-current-native-proper.md`.

'''
haskell = '''
### External Haskell repair status at the native proper checkpoint

No Haskell source or Cabal file changed. No native test or benchmark ran.
The LPO and extraction documentation fixes are integrated from main
8766699b594eaad80381af2eee034c378ccf3192. Pull and fetch passed. Main is an
ancestor. KBO candidate d7b6a9dfff464eb32c17c314d4825d5b027f1b2d remains
unintegrated, unbuilt and unexecuted. The positive-Int context-reversal
finding remains open. All earlier repair instructions remain below.

The new work proves a structural invariant of the Lean native execution.
It establishes no new physical Haskell defect or repair. External work must
retain the distinction between forbidden-template pruning and automaton
acceptance. Pending-group refutation and early transformed-template meaning
still need semantic laws. The previous witness designs remain unexecuted.

'''
note = f'''# Proper native paths and accepted captured endpoint progress

Source checkpoint: {head}.
Published base: {base}.
Main: 8766699b594eaad80381af2eee034c378ccf3192. Pull and fetch passed.
Previous note: `notes-current-callback-progress.md`.

## Target and strongest current statements

The target remains correctness of the whole CFTA system. It includes the
optimized interned core, exact finite-tree transformations, enumeration
soundness and coverage, ranking, sampling, public APIs and physical Haskell
correspondence. Preserve all older constructor and equality proofs, repairs,
counterexamples, marked drafts and restart evidence. The goal remains ACTIVE.

H6, SourceCurrentColdFiniteWarmCalls.constructed_node_calls, proves exact
original finite-tree language preservation for its covered closed construction,
original guard allocation history and empty inherited payload. For every fixed
finite number of pruning rounds, sufficient mathematical width and fuel give
an actual complete modeled call trace. This does not prove convergence or
withoutRedundantEdges.

Recursive.run_initial_finite_render_sound starts at the literal native cache
under its original Context, arity, resource and policy gates. Each returned
output must still be Discharged, render successfully and pass all returned
residual checks. Its rendered term then belongs to the original root language.
This is conditional output soundness. Whole enumeration coverage and physical
Haskell correspondence do not follow.

Finite sibling coverage retains its original resource packet and uniform
bounds before the selected index and semantic model. It reaches the actual
chosen hook invocation or identifies a precise strictly earlier stopped hook.
At the chosen occurrence it constructs a satisfying filling that fixes all
original variables. An invoked hook can itself stop or return no output.

The previous native scheduler theorem excludes some stuck for a Safe, indexed,
proper state with a satisfying assignment at the actual native heap. The
callback theorem preserves its full original packet and attaches that guarantee
to the exact returned metadata and framed cache. This checkpoint derives
ProperState at startup and preserves it through actual native child operations.
It also attaches proper storage and nonstuck selection to the actual accepted
captured endpoint, while retaining the complete original resource producer.

## Structural invariant and actual input origin

ProperState is the existing predicate in EnumerationProgress. A pending slot
without a node must have an empty suspended bucket. Each suspended trie stored
with a node must be valid, nonempty and nonterminal. The strict path prevents
a model of all blocked native candidates from forming a finite dependency cycle.
Canonical or Packet alone does not establish this structural condition.

ProperInputs applies before the terminal partition. It requires valid nonempty
tries and permits terminal tries. Actual child descent filters empty tries.
After terminal partition, the descendant bucket contains only nonterminal
tries. These operations derive the stronger ProperTrie inputs for stored paths.
Do not replace ProperInputs with ValidSuspended alone at the child API.

The selected-edge theorem derives projected trie validity from the original
current annotation heap and selected available edge. Its generic inherited
bucket still has the original independent validity premise. The captured-edge
theorem derives that premise from the actual stored pending value and original
ProperState. Neither theorem supplies a desired future invariant as an input.

## Actual native operations covered

CachedPrepare preserves proper storage for every actual returned row and every
actual observed cache. Ordinary preparation uses the real nonterminal test.
Mu and Union allocate empty buckets. Empty rejection retains the original
proper cache. Own suspension allocates empty stored buckets. Its core invariant
does not by itself justify validity of the separate returned suspended list.

IncomingNode preserves the actual outer core and actual successful singleton.
Its adapter also covers the synthetic cache written for raw empty results.
The proof derives old bucket paths from the actual read pending value. It does
not require Safe on a rejected synthetic cache.

Dispatch follows the actual optional and queried branches. A missing merged
handle requires both original handles to be missing. Original ProperState
then forces both old buckets to be empty. A generic assimilation shape with
an arbitrary missing merged handle would lose this origin fact. The proof
therefore uses the actual dispatcher. Queried branches retain their literal
some handle. The cached adapter derives singleton row validity from that
dispatcher. Its empty-result cache restores the original state, unlike the
incoming adapter's synthetic empty-result write.

Fold preserves every actual outer endpoint, including errors and rejection.
Its cached observer covers every attached candidate, including a rejected
prefix. Terminal merging threads the actual terminal prefix, fold and incoming
write. The proof identifies the actual folded core with the exact fold result.
It does not equate an arbitrary recovered cache with that core. The candidate
observer covers both nil fold caches and synthetic nil incoming caches.

Child dispatch uses the literal terminal partition. Its observer preserves
all actual attached caches. The successful result is a projection of that
stronger observer. Ordered traversal follows each actual successful child
cache and caller. The completed selected edge starts from the actual own
allocation, derives the real child inputs and retains proper storage through
residual finish. Captured completion adds the same indexed finalizer write.

## Complete original producer contracts

Recursive.initial_packet_proper calls initial_packet once. Removing only the
new theorem name, outer grouping and added ProperState recovers the ENTIRE
1350-byte old declaration, SHA256
e9af585b8dc064e8364774b1f20ac07db9b926fe203f7a12d1ba88a70c7f8b2a.
All old admission, handle readback, Packet, Canonical, stored root, zero mass,
waiting counts and flags remain. ProperState follows from the literal initial
core. No new producer admission is added.

CapturedEdge.complete_with_history_resources_progress calls the original
complete_with_history_resources_accepting once. The ENTIRE 5913-byte old
declaration remains after only theorem rename, outer grouping and an appended
observer. Its SHA256 is
7af30586c81976537d2e8a8d68c581d9fe2b21d859f66f93cc6c1f5a41ffe050.
The namespace, local notations, variables and instance context remain.

The original witnesses fix r, n, p, h, k, actual caller, actual cache, saved
queries, full final Memos, inventory, roots and result. They retain stability
for every extra resource amount, Post, query projection, counter growth,
storage, realized pending nodes, counts, flags, fragment origin, pending and
protected references, history, complete-or-stopped shape, Fits, Heap and the
original universal accepting observer. Full Memos is not reconstructed from
the query projection.

The appended observer takes original ProperState, then arbitrary ambient,
original assignment, original Satisfies and accepted edge meaning. All these
inputs follow the fixed operational witnesses and their whole packet. The
old accepting observer constructs the SAME extended assignment and fragment.
It fixes every original variable, satisfies the original core, fills the
fragment to the original captured value and satisfies the actual final core.
The actual complete run supplies final ProperState through the new preservation
theorem. The retained shape supplies Safe. Original returned roots, storage,
realization, counts and flags supply native CacheValid. The previous progress
theorem excludes stuck for arbitrary typing, stop policy, order and metadata
at this exact endpoint. This describes a restart decision; it does not assert
that an arbitrary future restart executes or emits output.

## Remaining obligations and next work

The main gap is end-to-end recursive coverage from original public inputs.
Derive ProperState through actual partial narrowing, native parent selection,
the processed selected prefix and every recursive history, including stopped
zero-output paths. The new local preservation theorems and startup origin do
not yet form that whole recursive induction. Keep exact callers, caches, full
Memos, resources and actual branch outcomes in that induction.

Prove semantic pending-group refutation and partial-match soundness under
completion. Relate actual partial rendering to the filled callback fragment.
Relate early transformed templates to source syntax or original forbidden
patterns. Automaton acceptance alone cannot exclude legitimate forbidden
template pruning. Packet.bounded permits empty groups. The earlier witness
designs are source assessments and remain unexecuted.

Then justify explicit recursive depth and user-stop policy, ordinary fallback,
projection support and Mu/Union frontiers. Fresh recursive boundaries with
empty buckets can remain parked. Finish discharge and rendering coverage,
public selector/map/API admission, ranking and sampling composition, and
physical Haskell correspondence. No reliable completion percentage or date
is established.

## Checks, attempts and preservation

Fourteen new modules contain 1772 lines and 102547 bytes. They add 30 public
theorems and no definition or data structure. All installed modules and
standalone Audit pass -DwarningAsError=true and -Dlinter.all=true. Each successful
new-source log is empty. Audit returns its 56-byte dependency count. Full Audit
passes 4268 jobs and checks 80193 theorem dependencies. The builds replay an
unchanged unused-input warning from InternedFreshOrdinaryClosedCompletion.
No warning or linter is suppressed.

There are 27 actual compiler, build and public commands. Two fail. Terminal
strict1 has a 9823-byte log. Root v3 explicitly reduces the actual nested cache
matches. Child strict1 has a 677-byte log. Root v2 explicitly splits the actual
optional preparation rows. Both repairs leave their whole public declarations
byte identical and then pass. Other versioned drafts remain explicitly
untested where no compiler ran. Captured progress v1 was corrected by source
review to group the appended implication in v2, before its first strict pass.
All failed sources and complete logs remain. The source validator was first
invoked before the live Audit report existed. Waiting for that same check
allowed validation to pass without a source change or compiler rerun.

Every actual compiler/build/public command ran serially with measured 4 GiB
memory.max and memory.high and zero swap. Public readback has 212 complete
signature and axiom blocks, {public['bytes']} bytes, SHA256 {public['sha256']}.
All 182 old blocks form the exact 792434-byte prefix. The new 30 blocks have
64854 bytes and 939 lines. Only propext, Classical.choice and Quot.sound occur.
No placeholder, custom axiom, native_decide or heartbeat increase is used.

All 4253 old non-Audit Lean sources, 102 pinned modules, 449 enumeration sources
and 203 Haskell sources retain their bytes. Removing only the new imports
recovers the whole old Audit. Removing each document insertion recovers all
nine entire old restart documents. All earlier frozen evidence remains intact.

## Haskell handoff and portable evidence

No Haskell source or Cabal file changed. No native test or benchmark ran.
Main contains the LPO and extraction documentation fixes. KBO candidate
d7b6a9dfff464eb32c17c314d4825d5b027f1b2d remains unintegrated, unbuilt and
unexecuted. The positive-Int context-reversal finding remains open. FINDINGS
retains every earlier external repair instruction and records this status.
The new structural proofs establish no new physical Haskell defect or repair.

Portable evidence: restart-evidence/20261027-native-proper/.
The manifest records stored bytes. decoded-files.json records original bytes
for deterministic gzip payloads. Run verify-evidence.py on the snapshot.
Use --committed after the evidence commit. Preserve all drafts, failures,
public output, exact whole old-contract comparisons, copied source cuts,
final sealed reviews and all nine old document bodies. Publication receipts
stay outside frozen TEMP and archive.
'''
paths = ['NEXT-PROMPT.md', 'HANDOFF.md', 'FINDINGS.md', 'lean/API-COVERAGE.md',
    'lean/COVERAGE.md', 'lean/README.md', 'lean/SYSTEM.md',
    'lean/notes-current-system-claim.md', 'lean/notes-proof-status-20261017.md']
records = []
for name in paths:
    target = root / name
    old = (area / 'prior-documents' / name).read_bytes()
    assert target.read_bytes() == old, name
    offset = old.index(b'\n') + 1
    extra = (common + (haskell if name == 'FINDINGS.md' else '')).encode()
    data = old[:offset] + extra + old[offset:]
    assert data[:offset] + data[offset + len(extra):] == old
    target.write_bytes(data)
    records.append(dict(path=name, bytes=len(data), sha256=hashlib.sha256(data).hexdigest(),
        offset=offset, inserted_bytes=len(extra), old_bytes=len(old),
        old_sha256=hashlib.sha256(old).hexdigest(), whole_old_body_preserved=True))
name = 'lean/notes-current-native-proper.md'
target = root / name
assert not target.exists()
target.write_text(note)
records.append(dict(path=name, bytes=target.stat().st_size,
    sha256=hashlib.sha256(target.read_bytes()).hexdigest()))
paths.append(name)
(area / 'document-paths.json').write_text(json.dumps(paths, indent=2) + '\n')
(area / 'document-validation.json').write_text(json.dumps(records, indent=2) + '\n')
print(json.dumps(dict(documents=len(paths), old_bodies_retained=9,
    new_note_bytes=target.stat().st_size)))
