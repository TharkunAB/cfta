# Finite bounded-row builder

`EnumerationBuilder` is the first, row-level construction model.
It starts with empty tables. It accepts a finite list of requested pairs.
Each pair contains a remaining height and a source node identity.

`EnumerationBuilder.build` checks the memo before it visits children. It uses
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

## Concrete source constructor and traversal

`EnumerationBuilderCaches` replaces direct row-list interning with the two
source caches. It interns copied edges in source order. It removes edges
with an `EmptyNode` child. It sorts and deduplicates the surviving edge
identities, then interns that list as the node key. Empty output returns the
distinguished empty reference without a node-cache insertion.

`construct_rows` derives exact row membership for this executable sequence.
`construct_final_rows` preserves that result after later cache growth.
`construct_language` proves the corresponding constructor language.
`construct_same_identity` proves that reordered or repeated retained edges
reuse the same canonical node in a growing cache. These results do not
assume a constructor readback or language-preservation contract.

`EnumerationBuilderRuntime` uses this concrete constructor in the complete
finite child and memo traversal. Its `buildAll_correct` derives canonical
cache entries, valid copied edges, child closure, and exact row membership.
Its `final_scope_exact` derives the finite memo domain. Row readback uses
membership equivalence, so it permits the source's sorting and deduplication.

`EnumerationBuilderFastPaths` also models the source's terminal exits.
`fastBuild` returns before memo lookup at an empty source node or height zero.
`fastBuildAll_exact` proves that the fast run equals the concrete run with
only terminal memo entries removed. Both edge and node caches are identical.
`fast_scope_exact` identifies exactly which nonterminal keys remain.

`fast_requested_readback` proves row membership at every requested root,
including terminal roots that have no memo entry. `fast_requested_exact`
proves the full bounded language at those roots. `fast_requested_runs_exact`
connects the concrete fast builder to the enumeration driver. That final
connection retains the separate intersection-row premise.

`initial_valid` and `fast_requested_from_state` permit valid preexisting
caches. The finite traversal can therefore reuse previously interned edges
and nodes. It does not require an empty global cache.

## Remaining source correspondence

The source constructor branch is in
`microcfta/src/Data/CFTA/Interned/Operations.hs`, in `boundDepth`.
The constructor cache operations are in
`microcfta/src/Data/CFTA/Interned/Type.hs`, in `setChildren` and `mkNode`.
The Lean builder starts from exposed constructor rows. It does not execute
`Mu` unfolding or resolve an unexpected `Rec`. Binder exposure remains a
separate obligation.

The concrete builder represents `EmptyNode` by zero and a stored node by
one plus its cache identity. The source's machine identities need the
corresponding representation map. Both caches use structural key equality
and mathematical supplies. Hashing, machine overflow, actual storage,
runtime casts, and concurrent host-cache correspondence remain separate.
The proofs require valid source edge tries and decidable copied-edge key
equality. They retain symbols, ordered children, equalities, and residual
guards in each key. No theorem assumes an infinite cache or injective
output identities.

## Validation

`lake build MicroCFTA.EnumerationBuilderFastPaths` checks all five builder
modules and their dependencies. The current target has 106 dependency jobs.
The principal theorem audit reports only `propext`, `Quot.sound`, and
`Classical.choice`. The latter is used by existing permutation and semantic
view proofs. No new axiom, `sorry`, or partial definition is used.
