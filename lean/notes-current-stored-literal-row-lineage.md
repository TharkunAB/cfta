# Original transitions of literal stored-substitution result rows

Proof checkpoint: `83199114`. Generic proof: `f226dc0a`.
Starting checkpoint: `9e1e57f3`. Main source: `c0cc8a05`.
Evidence: `restart-evidence/20261018-stored-literal-row-lineage/`.

The generic stored-substitution row theorem now derives an original source
trace from the actual execution. It covers arbitrary nested Mu values.
Literal ordinary rows can occur below root unions. A retained Mu stays
opaque. No BinderFree or finite ordinary Cap condition is added.

`SourceCurrentStoredLiteralCalls.execute` derives the actual output semantic
heap, record growth, issued-name extension, output availability and retained
replacement availability. Its indexed theorem follows the actual ordered
prefix and suffix. It derives the source member's semantic call entry and
its exact execution interval. Its union_row theorem uses literal union
normalization, not supplied epsilon origins, to select an indexed member
that returned the same complete row.

`SourceCurrentStoredMuLiteralRows.mu` generalizes physical selected-row
readback to a literal row below root unions. Such a row excludes retained
Mu and Empty cleanup branches. Correct comes from the exact selected
constructor winner. Forward record growth puts that winner in the later
reader's publication history. That history relates the winner to the
current ordinary callback. Root filtering preserves exact literal rows.
The proof yields repaired execution of the strict original body under
sparse local shadowing, at its actual post-depth entry. It derives the
semantic heap, body availability, replacement availability and both forms
of heap growth required for another source step.

`SourceCurrentStoredLiteralRowLineage.RowAt` records original node row
indexes, original union member indexes and original stored Mu body steps.
`ReferenceAt` records external source reference occurrences. A Mu step
excludes its own bound name from an external reference occurrence.

Origin retains separate closed identity, ordinary reconstruction, union,
Mu and external replacement cases. An ordinary case keeps its original row
index, exact symbol and full guard, and actual ordered child Calls. A Mu
case retains the lexical shadow choice at that source step. Origin does
not itself retain a full chronological parent callback schedule.

The anchor theorem eliminates the trace. A row either has an original
transition anchor with the same symbol, guard and arity, or occurs in a
mapped external replacement value. The source-anchor branch retains exact
row identity or actual ordered child calls under the lexical environment
at that occurrence. It does not relabel those calls as calls under an
unchanged root environment.

The replacement case is necessary for arbitrary composite replacements.
A local Mu override always supplies a bare ordinary reference, which has
no literal row. A remaining replacement witness therefore lifts to the
exact original external map. Aliases and absent mappings retain their
actual behavior. The source_row theorem excludes the replacement case
when the supplied mappings cannot contain the selected literal row.
This includes reference-only and Empty mappings.

`execute_row` constructs Origin from actual completed execution. Its
induction measure is the size of the original stored Value. Union steps
recurse on the selected original member. Mu steps recurse on the original
stored body. The proof never recurses on a generated raw result. Each
smaller call receives its derived semantic entry, available source and
replacement map. Its completed endpoint grows forward to the same final
reader history. No earlier global publication history is inferred backwards.

The ordinary case first proves that the actual makeNode return is Empty
or an ordinary node. It then converts the literal row into an immediate
nodeEdges index and applies the existing exact NodeRows producer. It does
not assume that an arbitrary literal row is an immediate physical row.
Closed execution is the exact identity shortcut. No child calls occurred
in that shortcut, so its provenance retains identity instead of fabricated
child executions.

`RowAt.child_smaller` proves that each anchored original transition child
is structurally smaller than the original input value. This bound concerns
original source children. Reconstructed output children can be larger.
It is not a bound on runtime recursive calls and does not exclude every
active memo-key collision.

The complete theorem constructs successful stored substitution from initial
SemanticHeap, Covered, Available, Replacements and global publication
History. It retains final semantic facts, coverage, output availability,
local and global histories, and Origin for every literal output row.
A successful future return or desired row origin is not a caller premise.
This is completion of stored substitution. General recursive outer
normalization is a different operation and remains open.

`SourceCurrentNativeConstructSourceRows.construct` consumes the generic
source trace at an actual native smart constructor. The previous readback
supplies current raw stored execution, filtering and the exact selected
winner. The proof derives the exact post-depth Context and SemanticHeap
from the actual depth callback. Actual growth and issued extension transport
body availability. The native replacement map supplies only a bare reference,
so its replacement-row origin is impossible. The selected physical row
therefore has an indexed original transition in this constructor's input
body, with full fields and identity or actual lexical child Calls.

That construct input body can itself be a generated native child result.
The theorem does not identify an original query operand or initial public
source transition. Those anchors must compose through actual native
writers, class folds, Parent and walk dispatch. Retained used-Mu epsilon
exposure remains separate. All-owner node-key exclusion, a bound on fresh
calls or another well-founded measure, recursive outer completion and
repeated convergence remain open. Equality-operation resource bounds, host
Int adequacy and public Haskell correspondence remain separate obligations.

The first integration builds open outer and nested Mu values. Replacing
one external name by Empty removes a recursive alternative. An unmapped
external reference keeps the final result as a mixed union. Its immediate
nodeEdges list is empty, but it contains the expected literal ordinary
row. The example derives every initial semantic fact from its own source,
applies the new Mu producer and generic execute_row, and excludes the
replacement branch to obtain an original indexed transition anchor.

The second integration uses an actual source body with a free pair and
an ordinary leaf. Native construction returns the leaf. A later edge
allocation changes the reader. Actual global history grows to that reader.
The new native source theorem derives its original transition anchor there.
A warm construct returns the same value and reader state. Both integration
theorems have no caller premises.

Four production strict logs and two integration strict logs are empty.
All thirteen production public pairs and both constructed pairs pass full
statement, proof and axiom printing in six groups with all eight settings.
Only propext, Classical.choice and Quot.sound occur. Full Audit passes
3279 jobs and 71402 dependency checks. All jobs record 4 GiB maximum/high
and zero swap. Earlier proof-development attempts remain unselected.
Independent generic and native reviews find no material issue.

No Haskell file changes in this checkpoint. No new executable defect is
claimed. FINDINGS keeps all earlier Haskell repair entries first. Field-pool
repair b9219b9e remains fixed in c0cc8a05. Every previous proof, repair,
counterexample and marked draft remains unchanged. Publication awaits the
existing direct approval. The full-library goal stays active.
