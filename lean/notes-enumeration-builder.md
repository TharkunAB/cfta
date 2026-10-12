# Finite bounded-row builder

`EnumerationBuilder` now constructs the finite row cache and the memo table.
It starts with empty tables. It accepts a finite list of requested pairs.
Each pair contains a remaining height and a source node identity.

`build` checks the memo before it visits a constructor's children. It uses
the source's shallow-depth filter. It visits the retained ordered child
lists at the next lower height. It then interns the completed parent rows
and records the returned identity. `Cache.intern` can reuse an identity.
The builder does not encode a memo key as a unique node identity.

The executable definitions take decidable equality for row keys. The
semantics treats height zero as empty. A positive Lean height is one greater
than the Haskell `Depth` limit, because a Haskell leaf has depth zero.

The new proofs derive the construction invariant from empty tables:

- `buildAll_correct` proves cache validity, canonical memo entries, issued
  child identities, child closure, and exact row readback.
- `final_readback` proves the final row equation for every requested key.
- `construct_grows` proves that later memo and cache entries cannot change a
  completed constructor's rows. It checks only the retained child requests.
- `final_scope_exact` identifies the final memo domain with a finite list.
  The list contains the requested keys and their bounded child traversals.
- `final_cache_bounded` bounds every issued identity by the final supply.
- `identities_equal_iff` proves that completed keys share an identity exactly
  when their stored row keys agree.

`EnumerationBuilderLanguage` proves language equivalence on that finite
memo domain. `normalized_exact_on` needs copied rows only at keys in the
domain. `scope_closed` derives child closure from the completed traversal.
`scoped_members` and `scoped_rejected` derive the actual constructor-row
relation and the empty-child cleanup rule.

`requested_accepted_exact` proves that each requested output accepts exactly
the original finite terms within its height bound. Its premises contain no
readback, trace, or language-preservation assumption. They require valid
source edge tries and decidable row-key equality.

`requested_runs_exact` connects the builder to the proved enumeration
driver. It retains the separate checked intersection-row premise. It also
retains interpretation of residual guards. The builder theorem alone does
not implement intersection or decide guards.

## Remaining source correspondence

The source constructor branch is in
`microcfta/src/Data/CFTA/Interned/Operations.hs`, in `boundDepth`.
The Lean builder starts from exposed constructor rows. It does not execute
`Mu` unfolding or resolve an unexpected `Rec`. Binder exposure remains a
separate obligation.

The row-level model records empty and zero-height results in the memo.
The Haskell `EmptyNode` and negative-depth paths return directly. A proof
that removes these extra terminal memo entries from the trace remains.
The model has exact final language semantics for these results.

The cache key is an ordered row list. The source also interns individual
edges and sorts and deduplicates node edge identities. The model does not
prove that representation adapter or reproduce its identity allocation
order. Its canonical sharing theorem concerns equal modeled row keys.

The source uses machine identities and concrete maps and caches. Their
storage and equality implementations remain correspondence obligations.
No theorem requires an infinite cache or injective output identities.

## Validation

`lake build MicroCFTA.EnumerationBuilderLanguage` checks both new modules
and their dependencies. The principal builder and finite-domain theorems use
only `propext` and `Quot.sound`. The language theorem also uses
`Classical.choice` through the existing semantic edge view. No new axiom,
`sorry`, or partial definition is used.
