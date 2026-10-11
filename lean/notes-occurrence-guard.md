# Recursive occurrence guards

`OccurrenceGuard.lean` follows the three token sets in
`Ranked.Internal.Size`: unguarded, termless, and used occurrences. It models
source size lists, occurrence minimum assumptions, map, pay, constructors,
choices, and products. Each token identifies one recursion independently.

The model also enumerates recursive contexts independently of the metadata.
A context records its hole token, the size outside that hole, and the number
of engine term nodes added on its path. Products choose sibling sizes.
`minimum_zero` proves that a product's sibling minimum test is exactly its
size-zero membership test. `unguarded_exact` identifies the unguarded token
set with contexts of extra size zero. `termless_exact` identifies the
termless token set with contexts that add no engine term node.

`guarded_context_growth` derives strict size growth and strict engine-term
growth for every context of an accepted occurrence. The proof does not
assume a shrink/decrease postcondition. `zero_sibling_rejected` proves that a
size-zero sibling cannot guard recursion. `pay_only_rejected` records that
pay alone changes size but does not change the engine term. Constructors
guard both forms of growth. These are engine terms; user surface projection
can remove private scaffolding and need not preserve this distinction.

`used_exact` verifies that all syntactic tokens remain reached even when a
product has no currently known finite member. `closedWith_tokens` proves
that grouped-family closing retains supplied enclosing-recursion flags.
`knot_fields` records that the source's fresh metadata wrapper preserves
counts and both decoder fields. It does not claim that replacing metadata
alone establishes their semantic invariants.

Occurrence minimum assumptions are explicit. Their standard-operation
convergence and fixed-point laws are in `RecursionProbe`. Turning these
context properties into a proof about GHC lazy forcing, arbitrary Haskell
builders, fresh runtime tokens, and recursive family key discovery remains
separate work. A count-field theorem does not certify IORef or StableName
behavior.

Validation: `lake build MicroCFTA.OccurrenceGuard` succeeds with the pinned
toolchain and no `sorry` or additional axioms.
