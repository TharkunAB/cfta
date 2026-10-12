# Recursive join field adapter

The source baseline is `origin/microcfta` at `de910ea`.
The source operations are `recursiveChainTerms` in
`microcfta-generator/src/Data/CFTA/Gen/Internal/Chain.hs` and `recursiveJoin`
in `microcfta-generator/src/Data/CFTA/Gen/Internal/Join.hs`.

## Model and source correspondence

`RecursiveJoinFields.ValueIndex` contains the independent count and selector
fields. `start` retains the operation term and an empty argument forest.
`extend` uses `productSplit` and appends one argument. `accumulate` follows
the source left fold. It does not replace the join with binary `Apply` terms.

`requests` combines the operation callback with each argument callback.
`requests_schedule` proves equality with the source's separate `scanl`
prefix-count construction and `zip3` callback schedule. The theorem holds
before the length guard. The parser then requires the complete declared
argument count. Thus a shorter query cannot silently truncate the product.

`RecursiveJoinCallbacks.field` uses `JoinN`, `CenterKeyed`, `ArgKeyed`, and
component and position keys. `source_selected` proves equality with the
source constructor that fixes the key list before selecting a payload.
`accumulate_length` proves that every selected payload has the declared
arity. `zipped_keys` then proves that the source `zipWith` retains every
selected argument.

The parser first requires an exact binary `ArgKeyed` wrapper for each
argument. It ignores the key while reading the payload. The separate
`joinKeysMatch` check changes the operation certificate flags before the
product fold. Wrong keys retain unchecked candidates. Malformed wrappers
and wrong argument counts return no candidates. The model retains this
source distinction. A spine request sorts the whole-term result again.

## Established field laws

- `accumulate_indexed` and `field_indexed` prove that each size class selects
  exactly its interval `0 .. count - 1`, for every finite arity.
- `requests_exact`, `children_exact`, and `field_exact` prove both directions
  between checked candidates and the independent selector. All three views
  are covered. A checked candidate cannot decode to a different join.
- `field_bounded`, `field_ordered`, and `field_distinct` cover every candidate
  row, including false flags. Their premises are local operand bounds and
  distinctness. They do not assume correctness of the complete join.
- `children_exact_local` needs operand whole-term contracts only for terms
  strictly shorter than the requested child forest. `collect_height`,
  `operation_below`, and `argument_below` prove that restriction from the
  parsed source wrappers.
- `RecursiveJoinLocal.field_exact_below` preserves restricted callback
  exactness. `field_agree` preserves complete ordered callback rows when
  operand counts agree and operand callbacks agree below the request bound.
  This law includes false flags. It supplies the local condition for a
  mutual recursive callback height induction.

The nullary branch retains the operation count and rank. Its term is
`JoinN [CenterKeyed [operation]]`. It does not add a synthetic product member
or require an argument key.

## Typed values and independent term fields

`RecursiveJoinTyped.Chain` models the curried `ArgChain`. Each argument can
have a different value type. Each local `Leaf` supplies a correlated value
and term index plus its independently supplied term callback.

`Chain.values` applies user functions through its own product indexes.
`Chain.paired` applies the same functions while it collects the operation
term and ordered argument forest. `paired_values` and `paired_terms` prove
both projections as complete index equalities. `counts_aligned` follows
from these equations. `rank_aligned` then connects a selected user value to
the private join term at the same size and rank. `rank_complete` derives a
correlated value and term for every valid rank from local leaf interval
contracts. It does not assume a whole-chain correspondence theorem.

This local model represents a leaf's correlation explicitly. It does not
claim that arbitrary externally supplied `SizeIndex` and `RecursiveTerms`
records have matching count or selector fields. The existing finite and
keyed paired-source compilers can establish that provenance for their
constructed leaves.

## Grouped records and whole-body composition

`RecursiveJoinMass` constructs separate value, term, and correlated grouped
records. It proves mass convolution, ordered projections, complete ranked
sampler projections, record validity, and zero mass below a valid minimum.
`RecursiveJoinRecordBridge.product_realizes` connects those records to the
direct mixed-radix selector. `paired_realizes` and `values_realizes` extend
that connection through every heterogeneous argument.

`RecursiveJoinComposition` supplies typed compiled bodies. `ofNary` imports
the existing keyed n-ary constructors. `map`, `pay`, `label`, `ap`, `nary`,
and `join` compose them. A join can occur inside any other constructor or
another join. Intermediate products retain an operation term and an ordered
argument forest. Only the final term map constructs `JoinN`. The ordinary
`ap` constructor continues to construct `Apply`.

Each constructor derives its local value and term projections, mass and
rank laws, minimum expression, and size guard. These local laws quantify
over arbitrary related recursive environments. They do not assume any
whole-family projection or sampler law. `RecursiveJoinFamily.family_values`
and `family_terms` derive those laws by simultaneous size induction.
`rank_complete` and `decode_aligned` identify the shared member at each
valid rank. `ranked_values`, `ranked_terms`, and their bounded variants
identify the complete rank probabilities. `value_knot`, `term_knot`, and
`paired_knot` prove the untruncated source record equations. `paired_exact`
identifies the independent finite derivations of the lowered source program.

These family theorems initially require `KeyedSource.guarded`. This is the
size guard. It is not the complete public term-growth check.
`RecursiveJoinGuards` retains the original occurrence metadata and derives
all three family guards from the combined public check. See
`notes-recursive-join-guards.md` for its exact source correspondence.

## Recursive callbacks and public queries

`RecursiveJoinCompiledFields.term_selector` connects the direct source
join selector to the independent compiled term record. Its local callback
law uses each operand's callback law against that operand's term record.

`RecursiveJoinBodyFields.CheckedBody` retains a structural callback compiler
next to the typed lowering. Each constructor derives local count/selector
realization, successful rank intervals, restricted inverse laws, and
callback causality. The heterogeneous `Chain` retains all of these laws
through its source product fold. Finite leaves supply only their own
inverse contract through `ofNary`.

The separate `candidates` obligation records each finite leaf's bounds,
order, and distinctness contracts. Composite constructors propagate only
their child obligations. Their `bounded`, `ordered`, and `distinct` fields
derive the corresponding body laws. An inverse law for true certificates
alone cannot establish any restriction on a finite callback's false rows.

`RecursiveJoinInverse.fuel_exact` closes the simultaneous callback induction
for all keys. Each `AtKey`/`Family` boundary decreases the requested forest
height. `positions_exact` proves both directions against the independent
term-family decoder in whole, labelled, and spine views. `fuel_stable` and
`positions_equation` prove equality of complete candidate rows with the
source callback equation. This equality includes false flags and list order.
No whole-family inverse law is a premise.

`fuel_bounded`, `fuel_ordered`, and `fuel_distinct` derive all three candidate
properties by mutual fuel induction. The corresponding `positions_*`
theorems establish them for the complete family callback. These theorems
use only the local finite-leaf `candidates` obligations and the source size
guard where required. The bounds include both checked flags.

`RecursiveJoinQuery.query_exact` proves the public checked-flag and replay
filter. `bounded_query_exact` identifies every bounded global rank with its
independent bounded decoder preimage. `global_source_counts` uses the
value-index counts for the source size prefix. `public_query_exact` and
`public_bounded_query_exact` derive the required guards from the combined
public occurrence check, including the original term-growth metadata.
`query_nodup`, `query_ordered`, `bounded_query_nodup`, and
`bounded_query_ordered` preserve distinctness and source order through
replay filtering and conversion to global ranks. `public_bounded_query_order`
connects both properties to the original combined public check.

## Validation

Pinned Lean 4.34.1 builds `MicroCFTA.RecursiveJoinFamilyExamples` in 150 jobs.
The isolated dependency audit allows only `propext`, `Classical.choice`, and
`Quot.sound`. It checks the original adapter, the record bridge, all new
composition modules, the public metadata module, and the examples. This
check excludes admitted proofs and native-evaluation axioms. It does not
establish source correspondence by itself.

The original kernel examples cover nullary and ternary joins, invalid
ranks, all three callback views, wrong component keys, missing arguments,
malformed wrappers, two size splits, and a heterogeneous `Bool`/`Nat` chain.
The new examples include two mutually recursive keys, a heterogeneous join
with a nested nullary argument, retained masses nine and one, all-view
inverse replay, a false candidate with wrong join keys, the public replay
filter, and bounded global ranks. Labels use the source `labelTerm` rule,
which replaces a join's outer label and retains its keyed children.
The concrete mutual family discharges every local candidate obligation.
Its `all_queries_ordered` theorem proves distinct ascending ranks for every
query, view, key, and size bound.

An independent Haskell probe is in
`/tmp/mcfta-heterogeneous-join-replay.hs`. It checks eight classes and 37
member inverses, exact rational masses, and support acceptance through the
public generator API. It includes nonuniform atomic flags, operations, and
a delayed leaf. This execution supports the source comparison. It is not a
Lean-to-Haskell refinement theorem. No Haskell source changed for this work.

## Remaining integration boundary

`RecursiveJoinSupportFamily.family_exact` now connects the actual shared
support binder to the complete independent term-family language.
`RecursiveJoinInspectionBody` compiles the separate named diagnostic knot
and derives its constructor invariants. See
[the support and inspection notes](notes-recursive-join-support-inspection.md)
for finite-leaf premises, exact theorem scope, and graph representation
boundaries.

The retained mass and ranked sampler laws are proved here. Weighted flags
and absent term fields use the separate runtime modules. This body
interface models the successful branch with every term field present.
It does not establish arbitrary schema stability when the Haskell builder
runs in different recursive contexts. Host integer overflow and Haskell
lazy-knot productivity remain outside these finite, total Lean records.
