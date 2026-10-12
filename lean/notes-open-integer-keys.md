# Open integer keys and disjoint tuple blocks

`OpenIntegerKeys` models the integer fields read by `Compile.offsets`,
`renameFrom`, `renamedFormulas`, and `joinOpenKeys`. The observation field is
not part of these operations. `joinOpenKeys` clears it. Widths are natural
numbers in the model. Source width arithmetic uses Int, so this model covers
nonnegative widths without machine overflow.

`integerName_injective` proves that the actual reserved prefix and decimal
index names do not collide. `renamePairs` uses the source range and offset.
`renameFrom` executes the complete checked, capture-avoiding name-only
substitution. `positive_replacements` and `zero_replacements` account for the
source identity filter. `renamed_coordinate` proves that each local name
reads exactly its offset coordinate. A replacement is simultaneous; a new
name is not substituted again. Quantified formulas use the existing complete
substitution correctness theorem and its explicit nullary-application law.

`placedFrom_scan` proves that the executable block allocation equals the
source zip of keys with their prefix-sum scan. The final scan entry is unused.
`placed_bounds`, `placed_ordered`, and `block_names_disjoint` prove that all
blocks fit in the total width and that different blocks have no shared
coordinate name. Zero-width blocks are included.

`conjoin` executes the source binary conjunction simplifier. `join_exact`
proves that the joined formula retains every child condition after actual
renaming. `Scoped` requires each key formula's free names to belong to its
local coordinate block. Under this input invariant, `join_blocks` gives the
independent block formula law. The primitive interpretation and its relation
laws are explicit. No operational alpha-stability property of a supplied
solver is assumed.

`variableOf_integer` derives the exact source lattice name lookup.
`tupleEnv` uses `LatticeInput.nameValues`, rather than an assumed name-to-index
bijection. `slice_coordinate` connects a child's local tuple to its global
offset. `join_tuple_exact` then states the complete formula law for concrete
integer tuples and their actual source slices.

`cut` follows the take/drop reader split. `flatten_cut` and `cut_flatten`
prove both reconstruction directions. `joinedTuples_exact` recognizes
exactly the tuples whose slices belong to each child domain. Fixed component
widths make concatenation injective. `joinedTuples_nodup` and
`joinedTuples_count` derive distinct tuple enumeration and its product count.
`join_finite_exact` combines these results: exact distinct child domains and
correct child count records produce the exact joined formula language, a
distinct enumeration, and the actual `productPoints` record. It assumes the
child invariants, not the result of the joining operation.

`productPoints_unknown` preserves an unavailable count as None, including
when a different child might have zero points. It does not interpret None as
an empty language. The semantic formula law also applies when counts are
unavailable. These are cardinality results. They do not assign probabilities
to user alternatives or replace branch masses with point counts.

Remaining caller invariants are explicit. The full compiler must establish
`Scoped` and each child's exact domain/count record at `integerGroup`,
constructor settlement, and every regrouping boundary. Successful lattice
API decoding can supply the child domain enumeration; the automatic
instantiation across all OpenKey-producing source branches is not in this
module. Formula-derived parent restrictions and their kept-mass ratio are
separate from independent `joinOpenKeys`. Complete observation transport,
computed labels, and outer original-outcome candidate search remain in their
own models.

Validation: `lake build MicroCFTA.OpenIntegerKeys` passes with the pinned
Lean 4.34.1 toolchain. The module has no admitted declarations or native proof
evaluation. No Haskell source changed for this proof milestone.
