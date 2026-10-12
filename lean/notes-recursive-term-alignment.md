# Recursive value and term index alignment

`RecursiveTermAlignment` connects independent value and term construction
for a typed recursive body. The body can contain finite sources, maps, pays,
binary choices, applications, labels, and any number of occurrences of its
recursive root. Applications can have different intermediate value types.

The source constructs `recursiveIndex` and `recursiveTermIndex` separately.
Equal class counts alone would not show that a rank selects corresponding
fields. The proof constructs a third index that retains each value and its
term together. Projection recovers the complete ordered class lists of the
two independent indexes. This preserves every member occurrence.

## Source operations

The value interpretation follows `RecursiveSource`. The term interpretation
uses the operations in `Recursive.productTerms`, `choiceTerms`,
`labelRecursive`, and `payRecursive`. Choice inserts the branch index.
Application inserts `Apply` with the function term and argument term.
Labelling uses the proved source `labelTerm` operation and adds one unit of
size. Mapping values keeps terms unchanged.

`termBody` inserts `Recursion` at the knot. This matches `Recur.tiedTermIndex`.
Every occurrence reads that complete wrapped term. This preserves the
private occurrence boundary through labels and applications.

## Checked results

`body_values` and `body_terms` establish both projections for an arbitrary
class environment. `family_values` and `family_terms` lift them through the
recursive size schedule. `class_counts` derives equal class cardinalities.
`decode_value`, `decode_term`, and `rank_alignment` prove that every valid
value rank selects the corresponding term at the same position.

`minimum_expressions` and `body_guards` derive the same minimum-size probe
and occurrence guard for the three interpretations. `paired_exact` therefore
uses the actual value guard to prove that the correlated index contains all
finite typed derivations and only those derivations. It does not assume a
complete index invariant as a premise.

`bounded_values`, `bounded_terms`, and `bounded_rank_alignment` compose all
classes through a size bound. No valid bounded member lacks a term.

The kernel examples use a binary tree body with two recursive arguments.
At size five it has two ranks. Both values are `3`, but their constructor
terms differ. Equal user values do not require rank collapse.

## Probability and replay masses

`RecursiveTermMass` projects the exact recursive probability recurrence.
The independently built value and term samplers are the two marginals of
the correlated sampler. This includes their complete bounded prefixes.
Choices and product splits use class counts. Finite atomic sources retain
their internal distributions.

Equal value distributions alone could conceal a change in rank weights.
`RecursiveRankMass` therefore proves equality before discarding ranks.
It follows the actual choice-part filter, including offsets advanced past
skipped branches, product radices, maps, and every recursive class.
`bounded_rank_masses` proves that the value and term samplers assign the
same exact mass to each structural rank.

`ranked_projection` combines rank-mass equality with decoder replay. The
result fixes the full ranked distribution even when values repeat.
`ranked_values`, `ranked_terms`, and their bounded versions derive the actual
rank/value/mass and rank/term/mass fields from the correlated record. No
injectivity assumption on user values or constructor terms is required.

## Boundaries

Finite inputs retain correlated values and terms in one `FiniteSource.Source`.
The existing finite constructor proofs justify that input relation for their
supported source fragments. This module does not validate an arbitrary user
callback that supplies inconsistent values, terms, or counts.

The recursive class schedule is the guarded, smaller-size schedule in
`RecursiveSource`. Its existing proof derives finite derivation completeness.
The GHC lazy knot and runtime table representation still need correspondence.
One root can have heterogeneous intermediate application types. This is not
a proof of arbitrary mutually recursive heterogeneous runtime families.

This module proves forward index alignment. The full inverse callback for
arbitrary recursive bodies, all term views, and its checked-symbol flags
remains separate. The earlier `RecursiveCheckedRanks` results cover local
product, pay, and choice flags and complete guarded unary families.

Validation: the focused pinned Lean build passes with 24 jobs. The aggregate
audit checks these results with every other proof. No Haskell source changed.
