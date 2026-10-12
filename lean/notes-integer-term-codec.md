# Integer closure terms and tuple ranks

The source path is `Compile.closePoints` through `Static.pointsStatic`.
`fillHoles` writes coordinates at placeholder leaves in traversal order.
`pointsStatic` first finds candidate original outcomes from the requested
term view. For each candidate, `holeSymbols` reads only the original
placeholder positions. `rankPoint` applies `onlyPoint` to those symbols and
then calls the lattice tuple ranker. Finally, `hasView` compares the complete
rewritten term with the requested view. This last check also checks labels
which were not coordinate leaves.

`IntegerTermCodec.holeSymbols` and `holesIn` follow the source extraction
recursion for a whole-term view. Private label tags are retained as natural
numbers; neither filling nor whole-term extraction branches on those tags.
The source placeholder leaf case precedes the general child traversal.
Arity mismatch returns None. The model uses the existing exact `fillTerm`
and `fillForest` traversal from `RecipeCompile`.

`holeSymbols_fill` proves that extraction returns exactly the consumed
coordinate prefix, in order. `read_fill` then derives the complete fill/read
inverse from the literal reader equation. `fill_injective` proves that two
different coordinate tuples cannot produce the same filled term for one
fixed original template. User-label specialization need not be injective.
The proof reads the coordinates at the original placeholder positions.

`IntegerLiteral` discharges the literal reader equation for the actual
source singleton API. For every integer, `parsed_exact` executes the equality
parser. `compiled_terms` computes its two normalized unit inequalities.
`levels_exist` proves that the actual elimination succeeds. `points_exist`
proves success of the public constructor, including its integral-count check.
`onlyPoint_literal` then proves that the actual counter and decoder return
the literal. It assumes neither a precomputed count nor successful parsing
or elimination.

`IntegerLabelCodec.integerSymbol` and `leafValue` match the compiler's
literal label and refinement reader. `leafValue_integer` has no premises.
`exactLabel` executes the reserved-prefix test, ordered literal substitution,
and optional singleton refinement replacement. A checked substitution error
represents the source `substitute` wrapper's exception. It is not an empty
language. `exactLabel_name` and `exactLabel_matches` prove that every
successful specialization retains the constructor name and passes the
source `labelStaticMatching` predicate. `singleton_refinement_exact` proves
that replacement by a canonical singleton preserves all one-variable integer
solutions of the substituted formula.

`IntegerTermCodec.rankTerm` models the rank work for one known original
outcome under WholeTerm. It includes extraction, the actual lattice tuple
rank, and full rewritten-term equality. `rank_decode` composes this work with
a successful public `LatticeAPI.points` call. `rankTerm_sound` proves that
every returned rank is in range and decodes to the complete requested term.
`rankTerm_exact` gives exact recognition of the rewritten tuple language.
`decode_injective` gives distinct filled terms for distinct tuple ranks.
`IntegerLabelCodec.rank_decode` instantiates the theorem with the actual
integer labels and singleton reader. It assumes no term-codec inverse.

`OpenIntegerReaders` models the typed Lifted, Integers, Mapped, Paid, and
Applied cases of a bare open spine. `template_valid` derives that every
placeholder is a leaf. `template_holes` derives the key count from the actual
generated template. `source_split` and `fill_reader_split` prove that the
function-key prefix used by `compileOpenSpine` selects exactly the coordinates
consumed by its function term. `fill_extract` derives the whole coordinate
order. `evaluate_total` excludes the source empty-point integer exception
for every well-sized reader in this fragment. User maps are arbitrary total
functions and can repeat values.

The results are deliberately per original template. Multiple original
outcomes can produce the same filled term, or different terms can decode to
the same user value. These theorems do not turn member ranks into distinct-term
ranks across such outcomes. The source uses outcome-major pair ranks, with
the point rank changing fastest.

The remaining adapters are concrete. The complete `outcomeRanks` candidate
search must offer each relevant original outcome. SpineView and LabelledView
also require the source private-label projections before extraction; this
module proves WholeTerm only. The complete compiler must retain hole counts
and coordinate ordering through regrouping, choices, user constructors,
computed labels, and the formula renaming offsets. The reader proof covers
the listed bare-spine cases. It does not prove that arbitrary OpenKey records
have correct counts or formulas. The term inverse holds for any successful
label-specialization function; formula substitution semantics and error
handling remain the separately checked source operation.

Validation: the pinned Lean toolchain builds `IntegerLiteral`,
`IntegerTermCodec`, `IntegerLabelCodec`, and `OpenIntegerReaders`.
No theorem uses an admitted declaration or native proof evaluation.
No Haskell source changed for this proof milestone.
