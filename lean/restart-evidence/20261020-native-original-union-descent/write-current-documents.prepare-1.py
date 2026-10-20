from pathlib import Path
import datetime
import json
from zoneinfo import ZoneInfo

ROOT = Path('/home/tritlo/Code/mcfta')
HERE = ROOT / 'lean/restart-evidence/20261020-native-original-union-descent'
proof = (HERE / 'proof-commit.txt').read_text().strip()
stats = json.loads((HERE / 'attempt-accounting.json').read_text())
stamp = datetime.datetime.now(ZoneInfo('Europe/Stockholm')).strftime('%Y-%m-%d %H:%M %Z')
block = f'''## Current correlated source-union descent

Updated: {stamp}. Proof checkpoint: `{proof[:9]}`.
Verified start: `533db5d24`. Main remains `9769fe3e9`.
Read `lean/notes-current-native-original-union-descent.md`.

One original observed writer now retains union-only syntax descent to
the same actual terminal call. A joint SourceRow induction constructs
the descent and all five terminal witnesses together. It uses the same
original union indices and actual prefix, member and suffix effects.
One base Observed supplies a fixed publication and raw callback before
all stored rows and all successful unfold calls. The actual node RowCall
or selected binder payload resumption remains under that same tuple.
Unfolds use their same original stored anchor, including changed children.

The same warm source family now forces the returned nested binder arm.
Finite original Reached paths classify every possible enclosing writer.
Its same raw SourceRow and actual filter exclude the wrong node callback.
Its returned union descent and kind then force that same terminal to the
nested binder. The proof excludes only its node alternative and keeps
its full binder receipt. It assumes no writer identity or desired origin.
This source-only example executes no unfold or native prefix.

Two public and one constructed full readbacks pass. Root module and
independent fixture strict logs are empty. Canonical and default Audit
pass: 3536 jobs and 74283 theorem dependency checks. The sole warning is
the older ClosedCompletion input. All {stats['capped_commands']} actual capped Lean/Lake commands
remain, including {stats['failed_commands']} failed elaboration attempts. Counts do not measure
completion. Every earlier proof, repair, counterexample and draft remains.

Global renewal and active-owner exclusion, final retention, general outer
completion, convergence, generated-capture original ancestry, residual
observations and Haskell refinement remain open. Source descent is not a
runtime rank across historical winners. The proposed next plan inspects
causal publication order and states its missing links explicitly.
FINDINGS records external documentation repair 7469183 first. Its branch
is not imported here; the local runtime reproduction stays unvalidated.
All 268 Haskell and 207 active package files retain their bytes. The full
goal stays active. Pushes to formalize remain authorized.

'''
paths = ['NEXT-PROMPT.md', 'HANDOFF.md', 'lean/README.md', 'lean/SYSTEM.md',
         'lean/API-COVERAGE.md', 'lean/COVERAGE.md', 'lean/notes-proof-status-20261017.md',
         'lean/notes-current-system-claim.md']
for name in paths:
    path = ROOT / name
    text = path.read_text()
    if name == 'NEXT-PROMPT.md':
        prefix = 'Continue the cfta formalization in /home/tritlo/Code/mcfta.\n\n'
        assert text.startswith(prefix)
        text = prefix + block + text[len(prefix):]
    else:
        first, rest = text.split('\n', 1)
        text = first + '\n\n' + block + rest.lstrip('\n')
    path.write_text(text)
findings = f'''Current proof update: {stamp}. Proof checkpoint: `{proof[:9]}`.
The original observed-row producer now derives union-only descent and
the same terminal witnesses together from actual SourceRow induction.
The enclosing publication and raw callback stay fixed before all stored
rows and all actual unfold anchors. Actual node calls or selected full
binder payloads remain under that same tuple. The warm source now forces
its returned nested binder arm by finite Reached classification, the
same raw SourceRow/filter contradiction and its own returned descent.
No writer-identity or independent terminal-origin premise is added.
Two public and one constructed full readbacks pass. Root module and
fixture strict logs are empty. Default Audit: 3536 jobs and 74283 theorem
dependency checks. All {stats['capped_commands']} actual capped commands remain, including
{stats['failed_commands']} elaboration failures. This is the same source family as before.
Global renewal, active-owner exclusion, final retention, outer completion,
convergence, general generated ancestry, residual observations and Haskell
refinement remain open. The external Typing.hs documentation repair is
recorded above. It is not imported. No new local Haskell repair or runtime
validation is claimed. All 268 Haskell and 207 active package files retain
their bytes. Read `lean/notes-current-native-original-union-descent.md`.
Preserve every external repair, reproducer and validation result below.

'''
external = (HERE / 'findings-external-update.md').read_text()
path = ROOT / 'FINDINGS.md'
text = path.read_text()
assert text.count(external) == 1
path.write_text(text.replace(external, external + findings, 1))
(HERE / 'findings-update.md').write_text(external + findings)
note = f'''# Correlated source-union descent and forced binder resumption

{block}## Whole-library target and current claim

For each public operation, valid supported initial inputs must imply that
Haskell execution terminates and satisfies the intended specification.
Support must follow from initial data and resources. It must not assume a
future successful return. The target includes construction, transformations,
reduction, size classes, counts, ranks, enumeration, generation,
probability and external interfaces. The optimized interned core and the
older constructor and equality work remain in scope.

The model has conditional root-language and exact Sized results under
their stated premises. The native proof now connects actual stored rows
and successful unfold anchors to source terminals with a correlated
union route and actual node or binder receipts. This does not establish
general native termination or Haskell refinement. The main mathematical
gap remains a valid progress measure across selected native edits and
warm historical winners. Ordinary-height descent already has a checked
counterexample. There is no reliable completion percentage from totals.

## Exact new producer

SourceCurrentNativeOriginalUnionDescent adds UnionDescent and of_observed.
The generic relation has reflexivity and an exact indexed original union
member step. It does not traverse node children, capture values, stored
Mu bodies or binder callbacks. It does not identify unique occurrences
or intermediate executions by itself.

The private generic producer derives terminal and descent jointly by
induction on the actual SourceRow. Capture, node and binder stop at their
same receipt. Union uses that same constructor's original index and
lookup. Its actual earlier buildMany derives member Reached. The same
nested SourceRow supplies its terminal once. The actual member return
Context, suffix buildMany and final makeUnion work derive both physical
and issued intervals. The generic syntax bound uses the existing size
function. The same empty-original Reached and selected row exclude a
capture terminal. No selected child premise is needed.

The public inputs remain the actual closed original build to the exact
sourceHeap and base Observed with that same writer reader. A later reader
cannot replace this exact heap by reverse growth. The proof unpacks base
Observed once. One enclosing event and raw callback stay outside all
stored-row and successful-unfold clauses. Each same terminal retains
SourceRow, completed build, node-or-binder kind, nonunion, Context, Reached,
SyntaxBound, UnionDescent and both suffixes.

The node arm keeps actual buildEdges/makeNode, canonical output lookup,
distinct original source/output indices and the full RowCall output.
The binder arm calls resume on that same SourceRow and suffix. It keeps
actual probes/request, the same full selected cell at terminalAfter and
sourceHeap, smart finish, stored-body RowAt, both intervals and derived
original-root Written and Stored. Their hidden events remain independent
in the public conjunction. Stored internally fixes its own callback.
The resumed writer need not equal the enclosing or requesting writer.

Actual unfold rows keep their same original stored anchor, exact fields,
arity and equality-or-ordered-Calls receipt. Descent and resumption apply
to that stored anchor. Output children can differ. The conditional clause
does not establish that an unfold or an enclosing execution completes.

## Nonvacuous forced binder example

The source remains box[nested,outer]. Nested is a raw false binder with a
nullary tag17 node body. Outer is a raw false binder over union[var0,nested].
The original build, first nested publication, warm nested request, actual
outer callback and indexed member-one source call remain computed.
Semantic validity, full availability and causal history derive from
actual construction. The final outer full cell derives Written, Stored
and Observed. One new consumer supplies its fixed event/raw and complete
stored-row and conditional successful-unfold obligations.

For the concrete tag row, the proof classifies every recovered original
Reached binder expression. The source has only nestedBody and outerBody.
If it were nestedBody, its same actual SourceRow.node canonical lookup
would force raw to be a node. The actual root filter preserves that node.
This contradicts the selected outer stored body, a full inner Mu. Thus
the recovered expression is outerBody. No unique event is required.

The same returned UnionDescent from union[var0,nested] can stop only at
var0 or nested, because the terminal is nonunion. Its retained kind
excludes var0. The already-returned terminal is therefore nested. This
same terminal's node alternative is impossible. The proof retains its
entire existing binder resumption instead of selecting another terminal.
The public complete type equals the checked witness type.

Generic clauses still cover both terminal kinds. Only the concrete row's
branch is forced. This is a stronger proof version of the same source
family, not another independent example. It runs no unfold and has no
native execution prefix. It proves no unique publication, strict
requester-to-winner syntax decrease or global runtime rank.

## Validation, preservation and external Haskell repair

Proof authority: {proof}.
Evidence: lean/restart-evidence/20261020-native-original-union-descent/.
Two public FULL declarations and one constructed FULL declaration retain
complete proofs and axiom reports with all eight printer settings. Only
standard axioms occur. Root strict module and independent fixture logs
are empty. Canonical and default Audit pass: 3536 jobs and 74283 theorem
dependency checks. Only the older ClosedCompletion warning remains.

All {stats['capped_commands']} actual capped Lean/Lake commands remain, with
{stats['failed_commands']} failed elaboration attempts. Sources, logs, usage and effective limits
remain for every attempt. Copies add no commands. Heavy checks use
4 GiB memory max/high, zero swap, five minutes and fresh usage receipts.
Independent reviews and the proposed next-plan verifier add no Lean jobs.

Preservation retains 45043 starting files, 3532 older non-Audit proofs,
220 frozen manifests with 1291 entries, 268 Haskell files, 207 active
package files, two stashes and three other worktrees. Audit adds only the
new declared import. Every earlier proof, repair, draft and counterexample
retains its bytes. Publication and post-push closure receipts remain
outside sealed evidence. Closure checks all tracked blobs and modes,
checksums, clean status and exact remote formalize and unchanged main.

Refresh found external docs/binders-size-order commit7469183231da3a9c7aefc115c9cc818f4867bd9d.
Its Typing.hs, README and CHANGELOG patch qualifies Binders size ordering
by a subterm rule and advises upToSize for the finite acyclic case. The
exact patch and source-inspection status are retained. FINDINGS records
this available external repair first. It is not imported into formalize
or main. Its commit message reports the counterexample. No fresh local
matching-toolchain runtime validation is claimed. The earlier local
reproduction stays unvalidated. End False was already fixed upstream.

## Next proof and remaining obligations

Read next-publication-plan/plan.md in this evidence directory. It is a
source-pinned proposal, not a checked theorem. First move the same
selected full cell forward from terminalAfter through rawAfter only to
outer.afterBody. Its missing outer key proves the selected key differs.
Assemble one issued path from empty to that same outer.afterBody using
its retained prefix, probes, reservation and body path. The public
IssuedWriters.from_empty can then derive a same-payload writer with both
intervals to outer.afterBody. No reverse growth or event uniqueness is
needed. This feasible local producer is still unproved.

A well-founded original-source ordinal needs more: one completed-build
rooted trace that contains the chosen enclosing event and its earlier
selected-payload writer. The existing independent Written proposition
does not retain that common membership. Do not infer that earlier suffix
from its later sourceHeap reader. A common trace and strict event index
must be derived before they can support well-founded resumption.
This order still does not prove native owner renewal or termination.

General original ancestry through generated nonempty captures, preceding
Head/native entry histories, residual Mu observation chains and ordinary
continuations remain open. Global renewal and active-owner exclusion,
final owner retention, general outer termination/completion, repeated-pass
convergence and production Haskell refinement remain open. The full
original goal stays active.
'''
(ROOT / 'lean/notes-current-native-original-union-descent.md').write_text(note)
print(json.dumps({'status': 'PASS', 'updated_existing_documents': 9, 'new_note': 1, 'proof': proof}))
