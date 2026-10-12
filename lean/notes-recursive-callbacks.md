# Recursive callback and decoder correspondence

The recursive callback modules follow the source term-position workers.
They do not find inverse ranks by enumerating size classes. The supported
body has finite leaves, one recursive occurrence type, maps, pays, binary
choices, applications, and labels. Intermediate application types can differ.

## Complete recursive queries

`RecursiveCallbackTermination.positions` follows `staticTerms`, `productTerms`,
`choiceTerms`, `labelRecursive`, `payRecursive`, and `Recur.tiedPositions`.
It handles whole, spine, and labelled views. It retains each checked-symbol
flag and performs the source sorts and rank arithmetic.

The termination measure is the requested forest height followed by recipe
depth. Returning to the recursive body consumes a private `Recursion` node.
Other calls either consume part of the requested view or visit smaller recipe
syntax. Finite leaf callbacks are supplied as total functions. The source
callbacks for the finite constructor algebra have separate checked proofs.

`Selects` is an independent finite forward rank derivation. It includes the
actual pay, choice-prefix, and mixed-radix position formulas.
`certified_exact` proves that a callback returns a true certificate exactly
when this relation produces a term with the requested view.

`positions_ordered` proves ascending source order. `positions_bound` covers
both checked and unchecked candidates. `RecursiveCallbackDistinct` proves
that no two callback rows have the same class position. The product proof
uses the mixed-radix inverse. Choice branches have disjoint count intervals.

## Actual forward tables

`RecursiveCallbackTables` defines the ordered classes corresponding to the
source constructor operations. Its finite table reads only the declared
finite class interval. Valid leaf selectors never use the fallback term.
`finite_lookup`, `class_length`, `product_replay`, and `product_lookup`
establish the leaf and product correspondence in both directions.

`RecursiveCallbackCompleteness.table_complete` proves that every table lookup
appears in every appropriate callback view with a true certificate. It uses
the same forest-height and recipe-depth decrease as the source callback.
It does not use term height alone: a label can remove private choice or
application syntax from a child term.

`RecursiveCallbackAlignment.compile` constructs callback count and selector
fields from the typed finite source classes. It erases only value functions.
`compiled_indexed` derives every local count/selector interval.
`compiled_classes` identifies the resulting table with the independent typed
term compiler. `selects_lookup` connects forward rank derivations to it.

The recursive table equation is derived, not assumed at the public adapter.
`RecursiveSourceUnfolding` proves that the bounded proof evaluator equals
one unfolding over the full class family in exact list order. The source
guard and its computed minimum justify this equation. A positive sibling
makes a product empty at the size where an equal-size recursive read would
otherwise matter. Duplicate members retain their original positions.

`RecursiveSamplerUnfolding` proves the corresponding complete count, ranked
sampler, and value-only sampler equations. Empty product components discard
the other component's rank law. These are equations for the source fields;
they do not establish GHC lazy evaluation or runtime table productivity.

## Public query composition

`RecursiveCallbackAPI.certified_query` compares the callback with the actual
typed term decoder. Its count field comes from the independent value index.
`query_exact` proves the source checked-flag filter, including fallback replay
for false flags. It returns all and only matching class positions.

`global_replay` preserves a class rank at every sufficient bound.
`bounded_position` recovers the class of every bounded decoder result.
`bounded_query_exact` therefore gives all and only matching global ranks.
`bounded_query_nodup` and `bounded_query_ordered` prove uniqueness and ascending
order. The global rank is the source sum of preceding class counts plus the
class rank. It is independent of sampling weight.

These are member ranks. A value or term can occur at several member ranks.
The separate finite and cyclic automaton adapters prove distinct-term ranks
on their supported input domains.

## Local producer contracts and remaining scope

The generic finite-leaf contracts are exact certified views, declared class
bounds, ascending candidates, and distinct candidate positions. The module
does not infer them for arbitrary user callbacks. `static_terms_exact`,
`static_terms_indexed`, `static_terms_bound`, `static_terms_ordered`, and
`static_terms_distinct` discharge them for the existing finite source callback
algebra and its `SourcePlanPositions` conversion. Ordinary and atomic source
plans have concrete specializations.

The typed adapter receives finite callbacks separately from finite value and
term classes. Its local callback contracts must match those classes. No
whole recursive inverse correctness property is an input premise.

The recursive syntax here has binary choices. The source also has arbitrary
n-way choices with branch labels above one. `RecursiveNaryChoice` proves
the local n-way adapter from child producer laws. A complete n-way recursive
syntax extension remains a separate statement. Mutually
recursive heterogeneous runtime families, diagnostic inspection graphs,
refinement-imported callback wiring, and physical lazy tables remain outside
this single-knot theorem.

Validation: the callback API builds with pinned Lean 4.34.1 in 95 jobs. The
source-unfolding modules also build. The aggregate audit checks all theorem
dependencies. No production Haskell source changed.
