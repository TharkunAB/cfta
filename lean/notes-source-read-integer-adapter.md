# Integer adapter evidence for current guard transport

`SourceReadLogicalIntegerAdapter` uses the actual pure `SolverAdapter.execute`
path. `prepared_integer` proves that an all-Int ambient declaration list
produces only Int ambient, fresh, and default declarations. It preserves
first-match lookup, duplicate declarations, and the exact preflight collision
rule. It does not assume that every fresh binding passes preflight.

`returned_supports` derives mathematical evidence for each returned verdict
from correctness of the external Sat or Unsat response. Ambient assumptions
are empty. Every value in the interpretation's integer carrier meets the
prepared declaration domains. A failed preflight returns Unknown and needs
no external response. `collision_unknown` proves this for an unused ambient
`__microcfta_actual_0` declaration and any supplied check function.

`Returned` connects a pure guard callback to the adapter's returned results.
It is an explicit premise. It does not turn an exception into Unknown or prove
that every query returns. `callback_sound` derives the solver contract from
that premise and external response correctness. `guard_supports`,
`prune_sound`, `confirmed_retained`, and `compile_exact` compose the adapter
with the current public guard, finite pruning loop, and successful compiler
classification. None requires spelling stability or global table unambiguity.

The interpretation is `FormulaLowering.sourceModel target`, as required by
the existing lowering and adapter proof. This distinction preserves source
sort normalization. A zero-argument function sort lowers to its result sort;
it cannot be identified with the separate `FullSyntax.integerModel` on all
raw syntax.

`SourceReadLogicalIntegerCore` supplies a concrete unbounded integer target
interpretation. `core_agreement` proves that the induced source model and
`FullSyntax.integerModel` agree on the complete embedded arithmetic core,
including Boolean connectives and conditional integer terms.
`returned_core_supports` gives exact adapter evidence in the established
integer meaning for those queries. The unused non-arithmetic primitives do
not add a claim about arbitrary SMT function or real-sort behavior.

The external boundary remains Sat/Unsat correctness, returned-call coverage,
and the existing pure-to-Haskell correspondence. There is no claim of solver
completeness, successful preflight for every fresh spelling, exception-free
execution, SMT serialization correctness, or exact backend-language equality.
