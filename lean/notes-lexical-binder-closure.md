# Finite lexical binder closure and bounded enumeration

`LexicalBinderClosure` constructs the finite request domain from a closed
`Binding.Shape`. It does not take a finite closure set as a premise.

`inventory` visits each non-reference occurrence of the original lexical
syntax. It substitutes the closed ancestor environment at that occurrence.
At a binder, it first constructs the finite closed binder instance. It then
visits the original body with that instance bound to its name. A reference
returns an existing ancestor instance and adds no new inventory entry.
`inventory_length` proves that environment values do not affect the number
of entries. Substitution can enlarge an individual instance, but it cannot
add lexical occurrences to this traversal.

`substitute_compose` proves that later substitutions do not expand previously
inserted closed values. `unfold_instance` then identifies self-unfolding with
entry into the original body under the extended ancestor environment.
`inventory_step` proves closure under self-unfolding, union selection, and
constructor-child selection. `finite_request_domain` and
`reachable_inventory` derive a finite closed domain for every closed input.
The proofs permit nested binders, repeated names, self-references, empty
cycles, and references from a nested binder to an outer binder.

`visited_exact` applies `EpsilonUnion.visit` to the derived inventory. It
proves that the terminating visited worker returns exactly the epsilon-reachable
instances. `visited_distinct` excludes repeated visits. `exposed_rows_exact`
retains precisely the constructor rows reached through that closure.
`exposed_child_in_inventory` proves that every emitted child remains closed
and in the same finite inventory. `self_rows` checks that a retained self-cycle
has no outgoing constructor row.

## Confirmed source termination defect

`createMuDontCleanup id :: Node String` is a closed public input. Its callback
satisfies the documented parametricity condition. The public constructor
intentionally retains binders before cleanup, including this binder whose
least language is empty. A second example retains an outer binder and an
unused inner binder whose body returns the outer variable.

Before the repair, `nodeEdges` returned no rows for both examples immediately.
`boundDepth 0` did not finish within a one-second timeout. Its root `Mu` branch
called itself at the same depth before inserting the memo entry. The retained
self-cycle therefore repeated the same request. Ordinary `createMu id`
finished because its constructor cleanup replaced the self-cycle by empty.

The repair removes the separate `Mu` branch from `boundDepth`. All interned
node forms now expose constructor rows through `nodeEdges`. Its visited epsilon
closure resolves the cycle before bounded recursion visits constructor
children. Each child still consumes exactly one unit of constructor depth.
The original negative-depth behavior and unresolved `Rec` error remain.

The existing equality specification now checks both retained empty cycles and
a productive nested binder with epsilon references and unary `f` and `g` rows.
`repro/BoundRetainedBinders.hs` checks the public APIs. After repair, both empty
cases finish. The productive language has counts 1, 3, 7, and 15 at depths
0 through 3. Every decoded term has its own inverse rank.

## Representation boundary

The lexical proof retains names while the Haskell substitution plan rebuilds
nested binders with `createMu`. That rebuild can allocate a different binder
identity and remove a redundant binder. Connecting that representation to the
lexical instances requires the interning and alpha-renaming adapter. The proof
does not assume that fresh runtime identities are stable merely because their
languages are equal.

`finite_identity_image` proves a finite image for any fixed identity function
on the derived lexical instances. It does not prove that the Haskell allocator
implements such a function modulo alpha-renaming and cleanup. This is the
remaining runtime boundary. The visited worker also requires decidable shape
equality; source identity equality must implement a faithful representation.
This module does not claim full Haskell extraction or memo-trace equivalence.

Validation on 2026-10-12: pinned Lean 4.34.1, 19 build jobs. All three Haskell
suites pass in `nix-shell`: 282 core examples, 194 generator examples, and
138 refinement examples. The retained public repro passes. Fourmolu and
cabal-gild ran. No additional axioms, `sorry`, or `native_decide` are used.
