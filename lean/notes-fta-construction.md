# Explicit FTA construction and trimming

`FTAValidation` follows `Data.CFTA.mkFTA`. It merges repeated state rows in
input alternative order. `normalized_row_exact` proves that this merge keeps
exactly the same transitions. `normalized_language_exact` proves exact language
preservation, including cyclic graphs and retained guards.

The validation order is initial state, dangling child, then constructor arity.
`checkArities` follows the map-based arity loop. `check_sound` and
`check_complete` establish its stored-map invariant. `check_exact` states that
it succeeds exactly when a consistent arity assignment exists. `mkFTA_exact`
combines all three checks. `mkFTA_returns` proves that successful validation
returns the complete merged table.

`FromTerms` follows the source's `Nothing` root and `Just term` shared subterm
states. `subterm_exact` proves that each subterm state accepts its named term
only. `fromTerms_exact` proves exact root language. `graph_closed` proves that
no child state is missing. `build_exact` includes the public validation call:
every successful import accepts exactly the supplied terms. Inputs with an
inconsistent ranked alphabet can fail validation. Deduplication and ordered-set
iteration preserve term membership. The reference index does not specify the
source's exact rank order.

`GraphTrim` follows structural productivity, child filtering, then reachability
from the initial state. `live_exact` preserves every state's constrained
language. `trim_exact` preserves exactly the initial state's language. The
proofs apply to finite cyclic graphs. They do not treat a structurally
productive state as proof that its guards admit a term. `cardinality_stop`
justifies the source's fixed-point stopping test. `Productivity.finite_stability`
provides its finite iteration bound.

Lists and functional lookup model maps. A finite complete state type models
the keys of a validated closed table. Concrete map ordering, `Data.Graph`
reachability, interned conversion and machine representation remain adapters.
These proofs do not assume the graph operations preserve their language.
