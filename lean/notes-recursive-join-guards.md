# Original occurrence metadata for composite joins

`RecursiveJoinGuards` decorates `RecursiveJoinBodyFields.CheckedBody` with
the original occurrence shape. It derives the minimum, size-unguarded set,
and used set through every constructor. The constructors are `ofNary`,
`map`, `pay`, `label`, `ap`, flat `nary`, and heterogeneous `join`. A join can
occur inside another join, an argument, a label, a pay, an application, or
a choice. No complete family guard theorem is a constructor premise.

The source is `Gen/Internal/Chain.hs:recursiveChainProduct`,
`Gen/Internal/Join.hs:recursiveJoin`, and
`Ranked/Internal/Size.hs:productIndex`. The source folds products from the
operation through the arguments in order. A nullary join returns the
operation index unchanged. Each product clears the termless set and unions
the used sets. The size-unguarded set uses the minimum of the opposite
operand. The final `JoinN` term map does not clear flags independently.

`Chain.accumulate_size` derives the local correspondence through every
typed argument. `fold_minimum`, `fold_termless`, and `fold_used` prove the
source fold equations. `join_nil_summary` preserves all operation flags.
`join_cons_public_guard` proves that a nonempty join needs only its size
guard because the product clears all termless tokens. Empty operands still
retain syntactically used tokens.

Labels use `OccurrenceGuard.Shape.constructor`. Plain pay uses `.pay`.
The module does not recover termless flags from the erased value recipe.
`public_guard_exact` uses the original shape for this second guard and the
proved value lowering for the size guard. `public_value_guards` and
`public_family_guards` derive all value, term, and paired family guards from
the combined public rejection check. `family_minima_equal` proves that all
three compilers discover the same minimum table. `public_paired_exact`
then proves exact independent finite derivations of the complete correlated
family. These results use the local constructor laws, not an assumed
whole-family correspondence.

The metadata shapes count abstract product and constructor steps. The
`context_growth` theorem applies to those contexts. It does not assert that
the height or node count of an actual `JoinN` term equals the number of
product steps. The existing term and callback composition modules establish
the private term structure separately.

Examples check nullary pay versus label, zero and positive siblings, empty
products, and a decorated nested join with Boolean and natural arguments.
The last example computes minimum two, public acceptance, and the retained
family used token from the actual decorated constructors.

Validation uses the pinned Lean 4.34.1 toolchain. The targeted module build
and isolated dependency audit use no admitted proofs or native-evaluation
axioms. No Haskell source or aggregate ledger is changed by this module.
