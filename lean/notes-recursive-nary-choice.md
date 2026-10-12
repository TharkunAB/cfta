# Arbitrary-arity recursive term choices

`RecursiveNaryChoice` models `choiceTerms` in
`microcfta-generator/src/Data/CFTA/Gen/Internal/Recursive.hs`.
Each child supplies its value count, term selector, and checked callback in
one record. The adapter uses that same ordered list for every field.
It permits an empty list, zero-count branches, and every natural branch
index. Private `Choice` labels retain the actual branch number.

## Source operations

Whole requests require `Choice branch [child]`. Only that branch receives
the whole child request. A singleton spine request uses the same whole
request. The formal spine path retains both source sorts. Other whole and
spine shapes produce no rows.

Labelled requests send the same view to every child. They concatenate the
child rows before sorting. Each row receives the sum of earlier branch
counts at its size. Its checked flag remains unchanged. The source sort
compares size, class rank, and checked flag in that order.

`select` uses the source prefix split and the selected child's term decoder.
`classTerms` independently maps each finite class with its private branch
label and concatenates the classes in branch order. The callback does not
enumerate these tables.

## Checked results

- `split_sound` and `split_total` establish exact branch decoding and its
  valid interval. `offset_injective` separates valid branch intervals.
- `field_indexed` derives the complete class count and selector contract
  from child count and selector contracts. `class_length` and `select_table`
  connect those fields to the independent forward class table.
- `field_exact` proves the complete certified preimage for all three views.
  `query_exact` and `whole_query` prove the actual checked-flag filter.
- `field_bounded` includes unchecked rows. `field_unique` proves that no
  candidate position repeats. `query_nodup` and `query_ordered` preserve
  distinctness and ascending order through the public filter.
- `recursiveField` uses the actual compiled recursive value count, the
  independent term decoder, and the tied callback. `recursive_indexed`
  derives its count correspondence. `recursive_exact`, `recursive_bounded`,
  and `recursive_unique` derive its callback contracts from the accepted
  source guard and local finite-leaf contracts. `recursive_choices_exact`,
  `recursive_choices_bounded`, and `recursive_choices_unique` compose any
  finite list of these recursive children.

The inverse proof does not assume an inverse law for the resulting choice.
Its premises concern individual child producers. The recursive
instantiation reduces those premises to finite-leaf laws proved by the
existing producer modules. Distinct positions can still select equal terms
inside an ambiguous child.

## Boundaries

This module closes the local arbitrary-arity `choiceTerms` adapter. It does
not add an arbitrary-arity constructor to `RecursiveTermAlignment.Recipe`
or `RecursiveCallbackTermination.Recipe`. Those recursive body languages
still contain binary choices. The later `RecursiveNaryBody`, `RecursiveNaryInverse`,
`RecursiveNaryCausality`, and `RecursiveNaryQuery` modules close the full
single-knot arbitrary-arity syntax and its actual inverse. See
[the n-ary body notes](notes-recursive-nary-body.md).
It also does not prove arbitrary mutually recursive heterogeneous runtime
families. Natural ranks and branch indices retain the existing boundary
with runtime numeric conversions and lazy storage.

Validation: the focused pinned Lean build passes. The new proofs use no
placeholder, project axiom, or native evaluation axiom. No Haskell source
changed.
