# One source universe in the same constructor execution

Status: source review and proposed private header only. No new theorem was
compiled or established. Root owns proof implementation and compilation.

The current algorithms support one shared native universe within one completed
repaired source build when that build actually reaches the universe. They do
not support a claim that every input has a resident universe. No algorithmic
counterexample to reuse was found in the inspected constructor schedule.

CurrentContext.context binds one allTypes expression with the current escaped
catalog. Components and argument-only schemes receive that expression.
Application puts it in its first Type child. Rigid query types do not use it.
GeneralizeSyntax.replace inserts the same expression at schematic leaves;
finish leaves its binder unchanged. TypeSyntax.allTypes has one smart binder,
and allTypesBody has no nested binder.

The finite source row algorithms add only node and union prefixes around those
Type expressions. They do not add another binder. Therefore every actual
allTypes occurrence in this source prefix executes with the same empty lexical
environment. The callback of allTypes itself reads its own var 0 and contains
no nested universe build. Arbitrary lexical-environment independence is not
needed for this bounded source domain.

The existing OverUniverse theorem proves this structure for the historical
constructor. UniverseConstruction.firstOrderRaw_constructor_complete is also
historical. CurrentConstruction uses CurrentContext and its current goal
encoding. Its source induction must be proved with that current context.
The old theorem cannot be applied unchanged by replacing the catalog name.

Exact reuse follows from an existing theorem once the first actual occurrence
has completed. FreshOrdinaryReplay.build_replay returns the exact same value
and the later input heap after Grows. This includes the complete binder record.
The repaired ordinary name comes from the replayed Depth value. Both probe
programs replay, the Mu request has the same key, and request_replays reuses its
stored complete body. It does not allocate a different owner for each occurrence.

The proof still must extract that first occurrence from the SAME actual root
build and derive its prefix validity and growth. A standalone allTypes build
from empty does not provide its owner. Earlier rigid nodes and probe records
can change cache allocation identities. The String-only cold universe heap
also cannot identify the current labeled-symbol heap.

header.txt proposes the next private source-derived law. Its only operational
premise is the accepted current root and its one mapped build from empty.
Its conclusion has an explicit absence branch. Otherwise it derives one
resident closed Mu, identifies every Mu record in that source-built heap with
it, and derives exact replay of the computed current ctx.types expression in
that same heap and later grown heaps. It assumes no second universe run,
resident U, ownership predicate, productivity law or completion provider.

The same-heap replay receipt is useful for finite witnesses. It connects the
actual resident U to the computed allTypes syntax, so its existing finite
var1 source witness can be transported through closed-language correctness
on this heap. A count of source binders alone would not provide that link.
The proposed header does not yet state or prove that language transport.

The implementation steps are:

1. Derive current OverUniverse structure from CurrentContext and the existing
   termsRows/relevantRows algorithms. Retain the current accepted root.
2. Follow the actual build through node/union children. If no atom is reached,
   show that no Mu record is installed. Otherwise retain its actual incoming
   state, completed result and prefix growth.
3. Derive the first atom's Mu tag and closedness from its real callbacks and
   canonical request. Body.callback_node supplies the actual callback shape
   for String symbols. Its corresponding labeled-symbol argument still needs
   a direct port or a proved mapping transport; do not equate the two heaps.
4. Apply existing exact replay to later occurrences. The complete source
   schedule preserves the first owner and its stored body. Derive final
   residency and the replay conclusion through that actual cache chain.

Absence is a real case. With an empty library, no query arguments and size 0,
CurrentConstruction uses no application or component annotation. The root is
ofType of an empty candidate union and a rigid encoded query type. Its build
uses ordinary constructors only. Context.types still exists as syntax, but
no universe request executes. Rigid size-1 component annotations can also
avoid it. These examples do not provide a resident U for later proofs.

Empty final values do not imply absence. At size 2 the application algorithm
includes ctx.types even when function and argument candidates are empty.
buildMany executes children in order before makeNode can collapse the result.
The application can therefore install U and still return Empty. Presence must
follow actual executed syntax, not the final result tag or rigid input alone.

The unique-record claim in the proposed header concerns the original source
heap. Later Grows heaps may contain other Mu records; only replay of this U
is claimed there. Native intersection can create a new intersection-pair Mu,
and preprocessing can rebuild recursive records. Their structural closure
remains open. Source ownership does not prove the no-pair-reference lemma,
finite joint assignment, occurs rejection, recursive eager completion or
full default Haskell correspondence.

source-pins.json freezes the inspected source fingerprints. excerpts.txt
preserves the exact small source passages used for these conclusions.
No compiler, live source, Haskell, Git or board action occurred here.
