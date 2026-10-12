# Generator support graph constructors

`SupportGraph.lean` models `singletonNode`, `familyNodeWith`, and
`restrictToKeyWith` with ordinary constrained edges. `SupportJoin.lean`
models `joinNodeWith`. The operands use `BinderLanguage.meaning`. They can
contain recursive binders and free references. The theorems hold for every
fixed interpretation of those references.

`singleton_exact` proves that the copied finite graph accepts exactly its
input term. `family_exact` proves that each keyed body contributes exactly
its terms under the family wrapper. `restrict_exact` checks the actual paths
`[0]` and `[1,0]`. Both paths must exist. `restrict_family_exact` derives exact
selection of the bodies stored under the requested key. Duplicate input keys
retain the union of all bodies at that key.

`join_exact` proves full agreement between the n-way graph constructor and
its term callback. The centre stores the operation first. Each argument
stores its key first. `join_equalities` proves every emitted equality between
`[0,i+1]` and `[i+1,0]`. `arguments_exact` proves ordered operand coverage.
The full graph theorem derives both directions. It assumes no graph/callback
agreement for the join itself. Empty argument lists are included.

These proofs use the standard private `Label` constructors. The source
`inject` parameter must preserve their identity for keyed family selection.
Inspection labels must use the same representation at both occurrences of
each argument key. The pure shape model omits edge interning order because
these theorems describe term membership, not member rank order.

Remaining support obligations include graph relabelling, all graph-closing
cases of `labelSupportWith`, recursive unfolding in that function, and the
heterogeneous generator records that select these constructors. `SupportTerms`
already proves the corresponding term-closing and surface-projection laws.
The graph-closing proof must retain source guards when it changes a root label.

Validation: `lake -d lean build MicroCFTA.SupportJoin` and the aggregate axiom
audit. There are no proof placeholders or new axioms.

## Closing finite layers

`SupportSpine.flatten_exact` proves that graph-side application flattening
and term-side flattening have the same ordered forest language. Arbitrary
recursive operand supports remain intact. Base labels exclude private Pure
and Apply because those labels select other source cases.

`SupportRoot.closeJoin_exact` proves graph/callback agreement when a user
label closes an n-way join. The source retains the original constraints.
Every join equality reads nonempty paths, so changing the root label preserves
its truth. A general root-replacement theorem makes this requirement explicit.

`SupportClosing.close_exact` composes pure, application, joined, ordinary, and
nested choice layers. Choice indices use their actual input positions. Closing
concatenates every alternative's labelled roots. Both directions of the
language theorem are proved by induction. Empty choices denote the empty
language even when source smart constructors use a different empty shape.

This closes finite outer-layer graph/callback agreement for those constructor
forms. The `Valid` conditions check private-label classification and spine
shape. Public heterogeneous records must establish that their stored support
has the represented form. Outer recursive binders, arbitrary mixed private
edge lists, explicit epsilon unions, and the source interning representation
still require their adapters. Recursive operands inside the proved finite
layers are already interpreted by the full least-language semantics.
