import datetime,json
from pathlib import Path
from zoneinfo import ZoneInfo
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[2]
proof=(HERE/'proof-commit.txt').read_text().strip()
stats=json.loads((HERE/'attempt-accounting.json').read_text())
stamp=datetime.datetime.now(ZoneInfo('Europe/Stockholm')).strftime('%Y-%m-%d %H:%M %Z')
block=f'''## Current actual native capture to original node rows

Updated: {stamp}. Proof checkpoint: `{proof[:9]}`.
Verified start: `499357bf4`. Imported main remains `794903b3f`.
Read `lean/notes-current-native-original-captured-node-rows.md`.

An actual checked native prefix now connects an initial captured Mu to
the original node calls for its stored rows and successful unfold rows.
The exact initial full cell selects one indexed publication in one
original build path. That path and publication stay fixed before all
stored rows and all actual successful unfolds. The result retains the
full payload, original Reached, missing cell, prefix and three callback
paths, physical and issued suffixes, and all generic stored-row origins.
Current semantic support and causal publication history follow from
the actual source build, checked Trace and exact leaves occurrence.

Each literal row of an actual successful unfold keeps its stored-row
anchor, symbol, constraint and arity. It keeps row identity or actual
ordered Calls from stored children to returned children. The same path
supplies an ultimate original node SourceRow/build/RowCall for that
stored anchor. Its producer index is at most the selected outer index.
The result retains producer-relative SyntaxBound/UnionDescent, original
Context/Reached, buildEdges/makeNode and the complete stored RowCall.
Changed returned children need not equal the original stored children.
The later-generated capture arm retains its complete existing receipt.

The existing shared-inner source family runs an actual native prefix
to an outer optional site. Leaf occurrence one selects the initial Mu.
Its actual unfold returns a rec/Top/arity1 row with a full Mu child.
The stored row has a reference child. Their inequality forces actual
child Calls. The same stored anchor keeps its original node RowCall.
All generic clauses remain. No independent source family is added.

One public and one constructed full readback pass with standard axioms.
Root strict logs are empty. Canonical and default Audit pass: 3540 jobs
and 74337 theorem dependency checks. Only the older ClosedCompletion
warning remains. All {stats['capped_commands']} actual capped Lean/Lake commands and
{stats['failed_commands']} failed attempt remain. Counts do not measure completion.
Every earlier proof, draft, repair and counterexample remains.

Original ancestry for later-generated nonempty captures and complete
residual Mu observations remain open. These are inputs to the remaining
global renewal and active-owner exclusion, final retention, general
outer completion and convergence proofs. Production Haskell refinement
also remains open. All 268 Haskell and 207 active package files keep
their bytes. FINDINGS retains the external repair registry first.
No new Haskell fix or runtime result is claimed. The full goal stays
active. Pushes to formalize remain authorized.

'''
paths=['NEXT-PROMPT.md','HANDOFF.md','lean/README.md','lean/SYSTEM.md','lean/API-COVERAGE.md','lean/COVERAGE.md','lean/notes-proof-status-20261017.md','lean/notes-current-system-claim.md']
for name in paths:
    path=ROOT/name
    text=path.read_text()
    if name=='NEXT-PROMPT.md':
        prefix='Continue the cfta formalization in /home/tritlo/Code/mcfta.\n\n'
        assert text.startswith(prefix)
        text=prefix+block+text[len(prefix):]
    else:
        first,rest=text.split('\n',1)
        text=first+'\n\n'+block+rest.lstrip('\n')
    path.write_text(text)
finding=f'''Current proof update: {stamp}. Proof checkpoint: `{proof[:9]}`.
Actual native initial captures now retain original node production for
stored rows and actual successful unfold anchors. One lower capture
call preserves its generated arm. The initial full cell selects one
indexed publication in one original build path before all row consumers.
Current semantic support, Mu availability and causal publication history
follow from the actual source build, checked Trace and leaves lookup.
An actual unfold keeps its effects and stored-row anchor with the same
symbol, constraint and arity, plus identity or actual ordered child Calls.
The same path supplies the stored anchor's ultimate original node call.
It keeps producer-relative bounds, Context/Reached, actual node build,
buildEdges/makeNode and full RowCall output equal to the stored anchor.
The existing native shared-inner example has different output and stored
children. It forces actual Calls and keeps that same original node call.
One public and one constructed full readback pass. Root strict logs are
empty. Default Audit passes: 3540 jobs and 74337 dependency checks.
All {stats['capped_commands']} actual Lean/Lake jobs and {stats['failed_commands']} failed attempt remain.
No new Haskell fix or runtime result is claimed. The imported PR #97
repair and all earlier external fixes remain above or below this update.
Prior formatter results remain valid for unchanged source files.
All 268 Haskell and 207 active package files keep their bytes.
Generated nonempty-capture ancestry, complete residual Mu observations,
global renewal, active-owner exclusion, final retention, outer completion,
convergence and production Haskell refinement remain open. Read
`lean/notes-current-native-original-captured-node-rows.md`.
Preserve every external repair, reproducer and validation result below.

'''
(HERE/'findings-update.md').write_text(finding)
path=ROOT/'FINDINGS.md'
text=path.read_text();position=text.index('Current proof update:')
path.write_text(text[:position]+finding+text[position:])
note='# Original node calls for actual initial captured Mu rows\n\n'+block+'''## Whole-library target

For each public operation, supported valid initial inputs must imply
that execution terminates and satisfies the intended specification.
Support must follow from initial data and resources. It must not assume
a future successful return. The target includes construction, transforms,
reduction, size classes, counts, ranks, enumeration, generation,
probability, external interfaces and the optimized interned core.
The older constructor and equality proofs remain in scope.

## Strongest statement for this step

Suppose an actual original build from empty supplies the exact native
entry heap. Suppose a valid checked native request reaches an optional
site and its available body contains a particular full Mu leaf. If the
Mu was in the entry heap, every stored row has an actual original node
producer. Each literal row from an actual successful unfold has such a
stored-row anchor. The output keeps its symbol, constraint and arity.
The proof retains the actual child substitutions when children change.
The generated-Mu alternative retains its existing causal receipt.

This is a Lean model theorem for actual prefixes and successful unfolds.
It does not assert termination of arbitrary native requests. The existing
conditional language and exact Sized results retain their premises.
Whole-library production Haskell correspondence remains unproved.

## Exact public contract

SourceCurrentNativeOriginalCapturedNodeRows adds one public theorem,
capture_node_rows. Its inputs are the actual original[]/empty build,
initial Good and native memo History, an actual checked request Trace
to an optional site, available site body and exact full-Mu leaf lookup.
The source build returns exactly before.native.machine.heap. A leaf
occurrence is not assumed equal to an encode slot.

The proof derives entry SemanticHeap and causal MuPublication.History
from the source build. It calls CapturedMuUnfoldRows.capture once.
The generated branch has the lower branch's exact type and tuple.
It retains the actual earlier prefix, strict native fuel bound, maybeMu,
generated Context/build/rooted Written/Origin/Stored/Observed, and both
physical and issued effects. It supplies no original-program ancestry
for an encode root with nonempty captured inputs.

The initial branch calls build_node_row_origins once. Its final-cell
selector chooses one outer index and publication in that same path.
Full Mu injectivity supplies entry, body, depth and ordinary alignment.
The sites and full-cell selector remain. No independent Observed writer
is selected or assigned this event's identity.

The private actual-unfold proof derives current SemanticHeap and causal
publication History through source_trace for the same checked Trace.
leaves_available supplies the selected full Mu's current availability.
No current or future causal history is a public premise. Native memo
History and causal publication History remain different predicates.

For every successful actual unfold at that same current heap, the proof
retains SemanticHeap, physical growth, issued extension, returned value
availability and extended causal History. For every literal returned Row,
it keeps an original RowAt storedRow, exact symbol and constraint, equal
arity, and identity or actual ordered child Calls. The same selected
path and outer publication supply the storedRow's ultimate node proof.
The node RowCall output equals storedRow. It need not equal the changed
output row. The node-return suffix ends at the selected outer.afterBody.

The node receipt keeps producer index k <= j and same-path lookup,
producer-relative SyntaxBound and UnionDescent, rich Context and original
Reached, actual SourceRow/node build/buildEdges/makeNode, separate source
and output indices, canonical row lookup and complete RowCall output.
No positive arity or selected-child premise is added.

## Concrete native example

The example reuses the existing two distinct used outer binders with
one shared used inner Mu. The source, data, initial validity, resource
admission and actual unfold helpers retain their bytes. It adds no source
family. It invokes capture_node_rows once and keeps all generic clauses.

The actual finite execute prefix reaches the outer optional site.
The admission proof supplies its checked Trace and available body.
Leaf occurrence one selects a full Mu that was in the exact entry heap.
The generated arm's actual prefix growth contradicts its missing-cell
receipt for that initial cell. No event identity is supplied manually.

The actual unfold's rec/Top/arity1 output row has the full captured Mu
as its only child. Its unique stored rec row has an interned reference
child. Computed inequality removes the identity arm and retains actual
ordered Calls. The same stored anchor retains its indexed original node
SourceRow/build/RowCall and both suffixes. The current optional operation
has only been reached; its own execution is not assumed.

## Evidence and next work

The sealed evidence folder is
lean/restart-evidence/20261020-native-original-captured-node-rows/.
It retains all source attempts, selected strict checks, complete public
and concrete printers, source snapshots, caps, usage and memory peaks.
Receipt copies add no Lean commands. The root personally observed strict,
canonical, default Audit and concrete strict checks at terminal exit zero.
Independent source and fixture reviews retain their exact inputs.

The final preservation check retains every older non-Audit Lean source,
frozen source registry, Haskell file, active package file, stash and other
worktree. Current handoff files add this dated block. Older dated claims
remain historical. The final publication checks verify filesystem,
index and committed blobs and modes, every evidence checksum, the selected
proofs, clean state and exact remote formalize. Publication receipts stay
outside the sealed folder to avoid a self-referential commit.

Next derive original input ancestry through the later-generated capture
branch. Its generated build has nonempty leaves inputs and an encode
root. The closed original build theorem cannot be applied by pretending
those inputs are empty. Preserve the actual earlier native prefix and
captured input identities. The exact next obligation must state how
generated row production returns to the original input row families.

Literal Row excludes rows hidden inside a residual Mu. Complete actual
reader continuations remain necessary there. Source publication order
is not a global native renewal rank. Active-owner exclusion and final
retention still require progress across generated rows and native calls.
General outer completion, convergence and Haskell refinement remain open.
The complete goal stays active. No reduction of scope is authorized.
'''
note += "\n## Exact next contract\n\nRead next-generated-capture/plan.md in this evidence folder. The design\nis unproved. It proposes one generated-row consumer that fixes Observed\nbefore all rows. It derives the same raw row's node, binder or capture\nterminal. An actual row-bearing full-Mu capture keeps its original input\nslot and calls capture_node_rows at the actual earlier native prefix.\nThe same stored row can then retain an original node call or a strictly\nearlier generated receipt. The active source Path differs from the\nissued publication Path. Non-Mu captures, warm prior cells, self\nreplacement and residual observations remain explicit open cases.\nThis design adds no checked theorem, example or Lean command.\n"
(ROOT/'lean/notes-current-native-original-captured-node-rows.md').write_text(note)
print(json.dumps({'status':'PASS','updated_existing_documents':9,'new_note':1,'stamp':stamp}))
