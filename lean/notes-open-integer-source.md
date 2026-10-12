# Generated open spines, child tables, and source rank discovery

`OpenIntegerSource.Recipe` is the bare open-spine fragment: pure values,
integer domains, maps, pays, and applicative products. An integer domain is
the Formula returned by the source `integerDomain` extraction. The model
does not accept arbitrary Guard constructors at this boundary. The source
extractor accepts Top, And, and root Satisfies only and throws for other
integer-leaf guards.

`integerGroup` calls the actual modeled public lattice constructor on the
source value name. A zero count removes the group. An unbounded-variable
failure retains a width-one group with an unknown count. Other failures are
returned. A finite group stores the actual count and the source's checked
value-name-to-coordinate-zero substitution. `compileKeys` follows the
source bare-spine recursion. Pure creates no keys. Map and pay retain the
keys. Application concatenates function keys before argument keys. The first
error is retained. An empty function group stops before the argument branch.
An empty argument group makes the product empty.

`compileKeys_width` derives the sum of the output widths from the generating
recipe. `source` constructs an ordinary Apply reference callback tree in
`StaticCandidateRanks`. The actual grouped compiler uses keyed JoinN
wrappers through relateGroupsM and pairBucket; this reference callback tree
is not its concrete output. `source_count` derives its single original outcome.
`source_select` identifies its typed reference term with the
`OpenIntegerReaders` template. `source_compatible` proves that every callback
accepts filling. `source_dimension` derives the key/template hole agreement
for every selected outcome. It does not assume that agreement as an output
contract.

`compiled_ranks_exact` composes this reference applicative tree with the successful
public closure table, the actual source candidate search, private view
projection, integer reader, tuple ranker, and final view check. Its valid
ranks are exactly the closure table's interval. It covers WholeTerm,
SpineView, and LabelledView for that reference tree. It does not establish
the keyed JoinN output of compileOpenSpine. `compiled_decode_injective` proves distinct
projected terms at distinct ranks for this fragment. `compiled_value_total`
proves that the generated reader returns a value at every rank. User maps
can repeat values. Value injectivity is not assumed or claimed.

`assignTuple_read` proves the exact coordinate-map writes made by the
lattice decoder. `pointDomain` enumerates its actual Fin interval.
`pointDomain_exact`, `pointDomain_distinct`, and `pointDomain_count` derive
all three finite child-table properties from successful public compilation.
They do not assume a child's count or decoder postcondition. The source
lattice name table and the concrete tuple environment are related by the
proved sequential assignment equation.

`LeafScoped` states the public integer-domain input convention: its only
free name is the source value name. Under this input condition,
`integerKey_formula` proves the actual leaf renaming preserves all integer
solutions. `integerGroup_domain`, `integerGroup_finite`, and
`integerGroup_distinct` derive the retained finite leaf's exact renamed tuple
language, stored count, and unique decoder domain. `LatticeDeclaredNames.points_leafScoped` now derives that convention from
every successful public leaf parse. Its `retained_leafScoped` also covers
unbounded leaves that passed parsing. No solver alpha-stability premise is used.

`Shape` records the constructor-generated static hole dimension. Its rules
cover pure, placeholder, indexed sources, map, pay, application, same-width
binary choice, and flexible labels. `shape_selected` proves the dimension
for every source-selected member. `source_shape` derives it for the bare
recipe. `joined_shape` uses the actual joined key width. `merged_shape`
shows that combining components of one regrouped key preserves its width.
`labelled_shape_compatible` derives the actual flexible label callback from
successful `IntegerLabelCodec.exactLabel` calls, and derives width
preservation from typed source labelling.

The scope is explicit. The complete map regrouping schedule and n-way
frequency callback are outside this generated recipe. The binary choice and
label results are local preservation laws, not a proof of every
compileOpen choice or constructor dispatch. Full constructor settlement must
still derive its parent guard formula, observations, label computation,
kept-mass ratio, and possible variable closure. Built imports, recursive
sources, and arbitrary user-supplied static callbacks are excluded. Closure
success remains an actual checked lattice API result; this model does not
claim that every mathematically finite formula is accepted by the supported
lattice fragment. Unsupported and unbounded failures remain observable.
The source label-specialization exception is also an explicit boundary.
Sampling masses are separate from these cardinality and replay laws.

Validation: `lake build MicroCFTA.OpenIntegerSource` passes with the pinned
Lean 4.34.1 toolchain. No admitted declarations or native proof evaluation
are used. No Haskell source changed for this proof milestone.
