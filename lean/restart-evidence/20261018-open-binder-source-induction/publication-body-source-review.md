# Actual publication body source cases

Date: 2026-10-18 13:04 CEST.

## Source

The final source is `lean/MicroCFTA/SourceCurrentPublicationBodySourceCases.lean`.
Its SHA-256 is `1826c36b030d16359f84d188149a0b37fa02f332b94273eeff9ed1851b15e3e9`.
Its two public declarations are `node` and `union`.
It imports the corrected publication adapter with SHA-256
`bf4e1251f28e250904fe8959363dcc20db14485c13008321be1fc10c0af1f59b`.
Both clauses produce that adapter's `BodyIH`. Neither assumes a parent
`RootMatch` or a parent reconstructed-output relation.

## Node clause

The event expression must be the literal source node in the statement.
Each hypothesis is indexed by an actual source row and ordered child.
It includes the strict child size bound. It quantifies execution heaps
that retain the initial common heap and keeps the observation view fixed.
The child relation uses depth plus one because `BodyIH` uses full-depth
`Executions (depth+1)` for its value relation. The later publication root
consumer lowers the relation for row children. This clause does not use
an all-smaller-grammar induction hypothesis.

The proof derives both local references and all captures at the actual
publication body's return heap. It obtains these facts from the real
reserved callback and its verification. Initial `Keeps` and each later
`Keeps` transport them into the execution heap. Replacement availability
and outer replacement availability derive the shared sparse map's
replacement invariant. The shared map pairs the two local lexical lists.
No freshness condition is imposed on unused captures.

The actual source calls and raw-return growth come from the corrected
`BodyIH` arguments. The proof applies `FiniteRootSourceNode.node` at those
exact raw entry and return heaps. The result retains full row symbols,
full guards, ordered child execution relations, and normalized survivor
matching.

## Union clause

The induction hypotheses cover only indexed immediate members of the
literal union source. Each includes a strict member size bound, the
member's derived lexical alias certificate, actual entry contexts, both
actual source calls, and both raw-return growth facts into the execution
heap. The member conclusion is a raw root match with the same finite
execution relation. It is not assumed for the parent union.

The proof inverts both actual union builds. It recovers the ordered
`buildMany` calls, their intermediate contexts, available results, and
actual `makeUnion` pairs. The private sequence induction recovers each
actual member call and derives its return growth through the actual
remaining suffix. The constructor growth and the parent growth complete
the chain into the execution heap. Source support derives each member's
alias certificate from the parent's certificate.

Actual ordered union normalization then produces the parent raw root
match. The existing publication consumer applies the actual root filter
and bare-self parity. The new clause does not replace literal root matches
with observational `AlignedAt`, and it supplies no desired filter law.

## Exact boundary

These are general conditional source constructor clauses. Arbitrary used
Mu syntax can occur in the strict source children or members. Their proper
induction cases remain hypotheses. The active nested-binder atom case is
not proved here. No BinderFree, closed-capture, finite Cap, or all-capture
freshness restriction is added.

The observation view remains explicit and fixed. The clauses do not prove
that every source expression satisfies the hypotheses at arbitrary views.
In particular, the ongoing arbitrary-view binder investigation is separate
from these valid conditional constructor implications. No reader transport,
general retained-Mu congruence, or outer completion is claimed.

## Checks

Selected strict check: `publication-body-source-direct-5`, exit zero and
an actual zero-byte log. Selected canonical build:
`publication-body-source-canonical-1`, all 642 jobs complete without warnings.
Selected imported full probe: `publication-body-source-public-1`, two public
pairs with all eight required options and `#check @`, full `#print`, and
`#print axioms`. No omission, printer error, warning, error, or `sorryAx`
occurs. Axioms are limited to `propext`, `Classical.choice`, and `Quot.sound`.

All selected checks use pinned Lean 4.34.1, a five-minute cap, and inner
readback of `memory.max=4294967296`, `memory.high=4294967296`, and
`memory.swap.max=0`. The highest selected peak is 191 MiB.

All numbered attempts remain present. Attempt 1 had a missing callback
namespace import. Attempt 2 checks the node clause. Attempt 3 had local
binder-name and type-inference errors in the new union clause. Attempt 4
checks both clauses. Attempt 5 removes an unused import and records the
reader-scope boundary. No frozen older source or evidence was changed.
The component adds two public pairs and zero constructed pairs. Its target
is the general source constructor implication, not a restricted fixture.
The manifest uses only owned evidence and explicit immutable source pins.
