# Open choice routing and finite weights

`OpenChoiceRouting` models the metadata decisions in `compileOpen Chosen`
and `compileOpen Uniform`. It also models `chooseGroups` empty filtering
and the status checks at the start of grouped `frequencies`.

The input contains the completed child compiler results in source order.
The source performs the IO traversal before it sequences those results.
`sequence_first_error`, `chosen_child_error`, and `uniform_child_error`
preserve the first outer child error. This model does not replace that IO
traversal with short-circuit IO.

Each `Family` retains recursive status and an embedded source result.
`cardinalities` follows `finiteGroups`: embedded errors survive, recursive
success gives `UnboundedGenerator`, and finite success exposes the ordered
bucket records. `empty` recognizes `EmptyGenerator` and finite all-zero
counts. Other errors and successful recursive families are live.

For `Chosen`, the source compares live alternatives before it checks their
weights. More than one live alternative triggers an ordered scan of all
finite keys. The first key with `openPoints = Nothing` produces the error
from `countPoints`; an unexpected successful recount uses the explicit
`UnboundedGenerator` fallback. `chosen_first_unknown` identifies that key.
`chosen_known` and `unknown_chosen_single` prove that accepted unknown
points cannot be compared across multiple live alternatives.

For `Uniform`, two or more live alternatives use member counts only when
no input family is recursive. `pointsOf` multiplies the original outcome
count by the stored point count. `sumPoints_first_unknown` preserves the
first unknown-key error. `members` uses weight one when `cardinalities`
fails; the later grouped gate still reports an embedded source error.
Otherwise the source gives every alternative weight one. `uniform_single`
and `uniform_recursive` prove those routes without invoking a recount.
`unknown_uniform_route` proves that successful unknown-point routing must
have at most one live alternative or contain a recursive family.

`Uniform` traverses all finite records on its counting route, including
ones that `chooseGroups` will later remove. `Chosen` excludes empty records
from its unknown-key scan. Two kernel examples preserve this distinction.
They are operational metadata cases, not a claim that an empty unknown
bucket is reachable through every public constructor.

`chooseFrom` assigns occurrence identifiers before it filters empty
alternatives. `choose_complete` preserves every nonempty occurrence.
`choose_records` retains its family and weight. `choose_bounds` and
`choose_ordered` prove the original identifier bounds and strict order.
`choose_gap` proves that removal leaves an identifier gap. An empty branch's
unused nonpositive weight cannot reach grouped validation.

`frequenciesGate` models the subsequent checks on these retained branches:
first nonpositive weight, first embedded error, no alternatives, and unequal
recursive weights. A successful result records finite or recursive routing.
It does not assert that downstream bucket merges or closure succeed.
`unknown_precedes_weight` checks the distinct outer-preflight priority.

For finite buckets, `closedPositions` uses the actual successful lattice
table's `pointDomain`. It pairs every original replay position with every
point. `pointsOf_positions` and `members_positions` derive the source count
from those lists. `uniform_finite_positions` composes the actual Uniform
counting route with all child tables. It gives the precise resulting list
of alternative weights. These are member counts. Repeated decoded values
retain separate occurrences.

`bucketShare` records the source bucket scaling factor: external weight
divided by retained total weight, times the incoming bucket mass.
`distribution_event` gives the exact finite event equation.
`distribution_probability` states its normalization with explicit valid
child-distribution premises. `uniform_counting` proves that count-weighted
alternatives become globally uniform when their children are internally
uniform. Arbitrary child weights remain inside each branch's share.
No finite distribution theorem applies to an unbounded family.

`intervals` separates source occurrence identifiers from cumulative finite
member offsets. Its bounds and disjointness laws apply to a finite merge's
ordered inputs. Weights do not enter that rank arithmetic. They do not
assert that a later `repositionOpen` regrouping keeps this global order.
The actual finite static callback and tuple rank inverses are modeled in
`StaticCompositeCandidateRanks`, `IntegerTermViews`, and
`CompiledIntegerSpine`.

The point recount callback remains explicit. It is the result of the
source `countPoints` operation, including its readable-name diagnostic
retry. The successful finite count bridge uses actual `LatticeAPI.points`
and the proved decoder cardinality. The status model erases values,
observations, sampler records, and the uninspected recursive payload.
It does not prove the full `repositionOpen` map driver or recursive closure.
The separate recursive key-discovery repair and its lookup proof address
that caller boundary. A singleton unknown branch can later receive parent
bounds; passing preflight alone defines no uniform measure on an infinite
set and guarantees no final compilation success.

Validation: `lake build MicroCFTA.OpenChoiceRouting` passes with the pinned
Lean 4.34.1 toolchain. The proof uses no admitted declaration or native proof
evaluation. No Haskell source changed for this module.
