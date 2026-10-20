from pathlib import Path
import datetime
import json
from zoneinfo import ZoneInfo

ROOT = Path('/home/tritlo/Code/mcfta')
HERE = ROOT / 'lean/restart-evidence/20261020-native-original-observed-resume'
proof = (HERE / 'proof-commit.txt').read_text().strip()
stats = json.loads((HERE / 'attempt-accounting.json').read_text())
stamp = datetime.datetime.now(ZoneInfo('Europe/Stockholm')).strftime('%Y-%m-%d %H:%M %Z')
block = f'''## Current observed source node and binder returns

Updated: {stamp}. Proof checkpoint: `{proof[:9]}`.
Verified start: `296d6f99c`. Main remains `9769fe3e9`.
Read `lean/notes-current-native-original-observed-resume.md`.

One observed original writer now retains an actual indexed node call or
an exact selected binder payload for each stored row and actual unfold
anchor. Its publication and raw callback stay fixed before all rows and
all successful unfold calls. Each same terminal keeps its source build,
Context, original-root Reached, generic syntax bound and both suffixes.
The node arm retains source and canonical output indices and RowCall.
The binder arm derives original-root Written and Stored for the same full
selected Mu. Its resumed writer can differ from the enclosing writer.
Separate Written and Stored Props do not equate their hidden events.

The same actual warm source family now derives the outer full record,
Written, Stored and Observed from its completed original build. The
consumer retains every stored-row and conditional unfold clause, plus a
concrete nullary tag row at that same callback. It keeps the node-or-binder
disjunction. It does not identify an opaque terminal with the manually
selected union member. No unfold or native execution prefix is run here.

Two public and one constructed full readbacks pass. The root module and
independent fixture strict logs are empty. Canonical build and default
audit pass: 3535 jobs and 74276 theorem dependency checks. Only the older
ClosedCompletion warning remains. All {stats['capped_commands']} actual capped Lean/Lake
commands remain, including {stats['failed_commands']} failed elaboration attempts.

The next local step must retain union-only syntax descent inside the same
terminal existential. Global Reached and a size bound do not expose that
route. The proposed plan is unproved. Global renewal and active-owner
exclusion, final retention, outer completion, convergence, general
generated-capture ancestry, residual observations and Haskell refinement
remain open. The largest gap is still general outer completion. Counts
do not measure completion. All 268 Haskell and 207 active package files
keep their bytes. FINDINGS keeps external repairs first. The full goal
stays active. Pushes to formalize remain authorized.

'''
paths = ['NEXT-PROMPT.md', 'HANDOFF.md', 'lean/README.md', 'lean/SYSTEM.md',
         'lean/API-COVERAGE.md', 'lean/COVERAGE.md', 'lean/notes-proof-status-20261017.md',
         'lean/notes-current-system-claim.md']
for name in paths:
    path = ROOT / name
    text = path.read_text()
    if name == 'NEXT-PROMPT.md':
        first = 'Continue the cfta formalization in /home/tritlo/Code/mcfta.\n\n'
        assert text.startswith(first)
        text = first + block + text[len(first):]
    else:
        first, rest = text.split('\n', 1)
        text = first + '\n\n' + block + rest.lstrip('\n')
    path.write_text(text)
findings = f'''Current proof update: {stamp}. Proof checkpoint: `{proof[:9]}`.
The original Observed producer now retains the same actual terminal tuple
and adds an indexed node RowCall or selected binder payload resumption.
The enclosing event and raw callback stay fixed across all stored rows
and actual unfold anchors. Binder resumption retains its same full record
at the exact original source heap and derives rooted Written and Stored.
The concrete warm-source consumer derives its outer record, semantics,
availability and causal history from actual construction. It retains one
fixed callback and a concrete nullary tag row with the full disjunction.
The public result does not force its binder alternative or identify its
terminal with the manually selected union member. Union-only terminal
descent remains an explicit next obligation. Two public and one
constructed full readbacks pass. Root module and fixture strict logs are
empty. Default audit: 3535 jobs and 74276 dependency checks. All
{stats['capped_commands']} capped commands remain, including {stats['failed_commands']} elaboration failures.
Global renewal, active-owner exclusion, final retention, outer completion,
convergence, general generated ancestry, residual observations and Haskell
refinement remain open. No new Haskell fix or runtime validation is
claimed. All 268 Haskell and 207 active package files retain their bytes.
The Typing.hs wording candidate remains unvalidated. Read
`lean/notes-current-native-original-observed-resume.md`.
Preserve every external repair, reproducer and validation result below.

'''
(HERE / 'findings-update.md').write_text(findings)
path = ROOT / 'FINDINGS.md'
text = path.read_text()
anchor = 'Current proof update: 2026-10-20 22:09 CEST.'
assert text.count(anchor) == 1
path.write_text(text.replace(anchor, findings + anchor, 1))
note = f'''# Observed original source node and binder returns

{block}## Whole-library statement and current status

The target remains the same for every public operation: valid supported
initial inputs imply that Haskell execution terminates and satisfies its
specification. Support must follow from initial data. It cannot assume a
future successful return. This includes construction, transformations,
reduction, size classes, counts, ranks, enumeration, generation,
probability and external interfaces.

The checked model has conditional root-language and Sized laws. Exact
size results retain their stated construction and annotation premises.
The native proof now connects more actual row observations to their
source calls and selected historical payloads. These local contracts do
not prove general native completion or production Haskell refinement.
The progress is concrete. The remaining global proof needs a valid
recursive measure across native edits and warm historical winners. A
simple ordinary-height measure already has a checked counterexample.
There is no reliable completion percentage from declaration counts.

## New exact contract

SourceCurrentNativeOriginalObservedResume adds two public declarations.
SyntaxBound is generic in Symbol and Guard. It is declared before the
concrete native aliases. It carries the existing generic syntax size
bound without selecting a different concrete SizeOf instance.

of_observed takes the actual build original [] empty = done root sourceHeap.
Its Observed writer reader must be exactly that sourceHeap. The current
observation heap can differ. Growth to an arbitrary later writer reader
cannot be reversed to recover this premise.

The producer calls OriginalObservedTerminals.of_observed once. It fixes
one enclosing publication and one raw reserved callback before both the
stored-row and successful-unfold quantifiers. Each old Terminal is
unpacked once. The same five witnesses retain SourceRow, actual completed
build, node-or-binder kind, nonunion property, Context, original-root
Reached, generic SyntaxBound and physical and issued suffixes.

For a node, the same SourceRow supplies actual buildEdges and makeNode,
the canonical output lookup and the indexed RowCall. Source and output
indices remain distinct. The call's complete output equals the same row.
No selected child is required. Nullary rows remain covered.

For a binder, one resume application uses that same terminal SourceRow
and the same containing callback and suffixes. It retains actual Depth
and ordinary callbacks, request, full selected record at terminalAfter
and sourceHeap, smart finish and RowAt of that selected stored body. It
derives original-root Written and Stored from the actual original build.
The selected historical writer can differ from the enclosing publication.
Written and Stored remain separate existential Props. Their public
conjunction does not equate hidden event witnesses. Stored internally
fixes its own publication and raw callback before all its body rows.

For a successful unfold, the returned row retains its original stored
anchor, symbol, constraint, arity and equality-or-ordered-Calls receipt.
The same original stored anchor supplies the terminal and resumption.
Rebuilt output children are not substituted for those stored children.
No future unfold completion is assumed or derived by this universal
conditional clause.

## Concrete consumer and its limits

The source family remains box[nested,outer]. The raw nested binder has
one nullary tag17 row. The raw outer body is union[var0,nested]. The first
box child publishes the nested full Mu. The later outer callback requests
the same nested syntax and retains its warm key and full selected record.
The unchanged source helpers retain the actual union member-one call,
rich callback Context, Reached, filter and both forward suffixes.

The new fixture derives the completed original build, final outer full
record, original-root Written, Stored and Observed. It derives semantic
heap validity, full outer-Mu availability and causal publication history.
One new of_observed application fixes its selected event/raw before all
stored rows and all conditional successful unfold rows. The same rows
clause also supplies the concrete tag17 terminal with its full disjunction.
The public complete type equals the complete checked witness type.

The selected event is not equated with the manually constructed outer
event. The returned terminal is not equated with the manually selected
member-one binder. Its public fields allow an earlier globally Reached
node callback with the same row and a forward suffix. This is an exposed
interface limit. The implementation still preserves one same terminal.
The fixture therefore retains the node-or-binder alternative honestly.
It runs no unfold and has no native execution prefix. The preceding
checkpoint separately checks the actual chosen member-one binder resume.
Both versions use the same constructed source family. They do not add an
independent example or prove all branches, writer uniqueness or a rank.

## Checks and preservation

Proof authority: {proof}.
Evidence: lean/restart-evidence/20261020-native-original-observed-resume/.
Two public FULL declaration, proof and axiom readbacks pass with all eight
printer settings. SyntaxBound is axiom-free. The theorem uses only the
standard axioms. One constructed FULL readback passes. Root strict module
and independent selected fixture logs are empty. Canonical module and
default Audit pass. Audit has 3535 jobs and 74276 theorem dependency checks.
Its sole warning is the older ClosedCompletion unused input.

All {stats['capped_commands']} actual capped Lean/Lake commands remain. The {stats['failed_commands']} failed
elaboration attempts retain exact sources and logs. Copies add no commands.
All heavy jobs use 4 GiB memory max/high, zero swap, a five-minute cap and
fresh usage receipts. Independent source and fixture reviews and the
unproved next-plan verifier add no Lean commands.

Preservation retains 44867 starting files, 3531 older non-Audit proofs,
219 frozen manifests with 1290 entries, 268 Haskell files, 207 active
package files, two stashes and three other worktrees. Audit adds only the
one declared import. Older proofs, repairs, counterexamples and marked
drafts retain their bytes. FINDINGS keeps the external Haskell registry
first. No new Haskell fix or runtime validation is claimed. End False is
already fixed upstream. The Typing.hs wording candidate stays unvalidated.

Publication and closure receipts stay outside sealed evidence to avoid
self-reference. Closure checks every tracked blob and mode against the
filesystem and index, evidence checksums, clean status, exact remote
formalize and unchanged main. The full goal remains active.

## Next local proof and remaining global work

Read next-union-descent-plan/plan.md in this evidence directory. The plan
is proposed and unproved. Add a small generic UnionDescent relation with
reflexivity and selection of an original union member. Derive it together
with the same terminal witnesses during SourceRow induction. Keep it in
that same existential. Existing SourceRow and actual call receipts remain.
Do not select an old opaque Terminal and separately select another route.

Compose from the base Observed once. Fix the enclosing event/raw before
all stored rows and actual unfold calls. For the warm source, first
classify every possible recovered enclosing writer expression. Do not
assume its event equals the manually constructed event. Then union-only
descent can exclude the bare var terminal using the retained kind and
leave the nested binder. These fixture steps are unproved. Pure syntax
descent alone gives no unique
intermediate call or occurrence. It gives no strict cross-writer decrease.

General original ancestry through generated nonempty captures, preceding
Head/native entry histories, residual Mu observation chains and ordinary
continuations remain open. Global renewal and active-owner exclusion,
final owner retention, general outer termination/completion, repeated-pass
convergence and Haskell refinement remain open. A historical producer
receipt and a local source bound are not a future runtime rank.
'''
(ROOT / 'lean/notes-current-native-original-observed-resume.md').write_text(note)
print(json.dumps({'status': 'PASS', 'updated_existing_documents': 9, 'new_note': 1, 'proof': proof}))
