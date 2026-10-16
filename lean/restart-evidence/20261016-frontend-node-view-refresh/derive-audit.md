# Derive field atoms and node views: source audit

Reviewed on 2026-10-16 at 13:08 CEST. Source main is `999c04a5`.
The relevant implementation commits are `d0966953` (field atoms) and
`9968bd8e` (node-view extraction for typing). The saved
`derive-upstream.patch` compares `b931bcc6..HEAD` for the two Derive modules
and DeriveSpec. This review did not run a build, test, or Lean process.
No implementation, test, or frozen Lean source was changed.

## Exact API and behavior changes

- `Derive.hs:170–173,337–342` exports `nodeFields` and `checkNodeShape`.
  Generic extraction returns the zero-based declaration position and one
  `Maybe e` per field. Scalars are `Just`; measure records are `Nothing`
  (`365–427`). Sum positions add the size of the left sum. `AnyNode`
  returns `(0,[])`. Custom `NodeView` instances now need this method or
  its Generic default.
- `Derive.hs:560–620` separates full invariant field-kind validation from
  shape-only validation. Both check constructor count, then all ordered
  constructor arities, then name prefixes. Full validation also checks
  each field kind immediately after that constructor's arity. Thus a
  later arity/kind error still precedes an earlier name error. `Nothing`
  bypasses validation. Prefixes remain case-sensitive and have no delimiter
  or injective-association guarantee.
- `Derive.hs:632–653` and `Internal.hs:309–310,368–374` replace annotation
  keys `(String,Annotation)` with `(Constructor,Annotation)`. Lookup and
  unknown-key checks use the whole Constructor (`Internal.hs:425–432,
  468–469`). Constructor equality includes its fully applied type and fields
  (`cfta/src/Data/CFTA/Generic.hs:92–98`). Distinct datatypes with the same
  constructor name no longer share annotations. Error rendering still uses
  the unqualified constructor name.
- `Derive.hs:658–695` adds `FieldPool`, `drawnFrom`, and `fieldAtoms`.
  Pools retain the encoded field expression, generator type, and generator.
  The callback runs on each constructor's symbolic view. Structural equality
  against its ordered argument terms selects the position. A composite
  expression is not a field. Repeated entries within one callback use the
  last Map entry. `Atoms` now has separate type and field maps plus delayed
  errors (`Internal.hs:156–162`). Both maps combine with rightmost precedence;
  delayed errors concatenate (`170–176`). Field lookup precedes type lookup.
- `Internal.hs:423–465` first discovers descriptions. It then reports the
  first delayed field error, unknown Constructor keys, field type/position
  mismatch, missing atomic coverage, and annotation/measure errors. Every
  uncovered primitive field still needs its type atom. A field atom covers
  only its exact constructor and position (`472–474,503–510`).
- `Internal.hs:339–345` selects a field pool before the type generator and
  treats that selected field as atomic for condition placement.
  `Derive.hs:757–763` uses the same precedence when evaluating values.
- `deriveLTAOnWith` deliberately does not restrict automaton fields to their
  field-pool generators (`Internal.hs:361–366`). It uses a type atom, or any
  field atom of that type, to read each fixed term's integer (`191–200,
  394–410`). The automaton supplies the actual terms. This difference from
  `deriveLTAWith` is documented behavior, not a pool-filtering defect.

## Concrete domain gap to verify

There is no self-type exclusion for field atoms. `drawnFrom` requires only
`HasFTA` and `Literal`. Neither shape validation nor `derivation` rejects a
pool on a recursive field whose type is the root datatype.

The runnable draft `derive-self-field-draft.hs` uses:

```
data Chain = End Bool | Next Chain
rules = Contracted (EndNode flag -> flag == literal True; NextNode _ -> true)
field pool: Next's child is drawn from [End False]
```

Chain has an injective nonnegative integer encoding: `End False=0`,
`End True=1`, and `Next rest=2+encode rest`. This meets the documented
Literal round-trip domain. Its independent invariant checks every Chain
node. `Next (End False)` violates that invariant.

By direct source reduction, `holds selected rules (Next (End False))` is
True. The selected pool takes the first branch at `Derive.hs:758–760`, which
returns `below=True` instead of calling `go` on the recursive child. The
root Next contract is True. The derivation also draws the supplied child
without recursively applying the invariant (`Internal.hs:343–345`). The
predicted depth-zero member list contains `Next (End False)`.

This requires a policy decision. The comments promise a contract at each
node whose type is the datatype (`Derive.hs:699–701`) and an invariant on
each imported term (`518–522`). If that contract includes recursive fields
with a field pool, this is a counterexample. If a field pool intentionally
cuts that contract, the advertised semantic domain needs that restriction.
No source repair is made or recommended as settled in this review.

The old type-wide `atom @Chain` also makes `holds` skip recursive children.
That replacement behavior is documented (`Internal.hs:178–182`). However,
`deriveLTAFrom @Chain` with that atom rejects its root annotations as unknown:
the type-wide atom removes Chain from `derived`, while `invariantAnnotations`
still supplies its constructors. The new field-local pool keeps Chain
in `derived`, so it can introduce this high-level case without replacing
the root generator. This distinction must remain in the finding.

The draft has not been compiled or run. Suggested command inside the
project's existing Nix/Cabal environment, after the active suite finishes:

```
cabal exec -- runghc -package=cfta -package=cfta-generator lean/restart-evidence/20261016-frontend-node-view-refresh/derive-self-field-draft.hs
```

It prints both `holds` policies, the independent predicate, high-level
construction statuses, and generated members with their independent validity.

## Tests and proof boundaries

`DeriveSpec.hs:657–665` tests separate kept-height and key Int pools. It
compares with an independent height predicate and with a larger shared pool.
`714–725` tests wrong field type, a nonfield expression, wrong view arity,
and an uncovered Int field. These tests do not cover self-type pools,
duplicate pool precedence, or annotation keys from two same-named types.
`TypedLanguageSpec.hs:91–96` tests imported measured and named-measure
languages with type-wide Int atoms; it does not test field-only atoms.

`SourceDeriveNodeViewNames` remains accurate for the positional prefix phase
and its earlier-shape-error precedence. It explicitly leaves metadata and
node-view semantics outside its result. `Generic` models finite datatype
row discovery; it does not implement this field-pool map or Derive's
annotation validation. `SourceTypingRules` starts from resolved constructor
labels and Child fields. Its language proofs do not derive the new
`nodeFields` extraction or validate custom NodeView instances. `IntegerLiteral`
proves backend integer singleton behavior, not a user Literal codec law.
There is no existing `deriveLTAWith` or `fieldAtoms` semantic adapter in the
Lean sources searched in this review.

A current frontend bridge therefore needs Generic metadata coherence,
valid constructor positions, scalar/record extraction laws, exact
Constructor-key lookup, pool membership and Literal readback laws, condition
placement semantics, and the recursive-field atom policy. Arbitrary custom
NodeView methods are not validated by shape checks alone. For example,
`Typing.hs:292–301` trusts their returned position; Haskell `drop` treats a
negative position as zero. Generic nodeFields never returns that position.
This is a custom-instance coherence boundary, not an established Generic
implementation defect.
