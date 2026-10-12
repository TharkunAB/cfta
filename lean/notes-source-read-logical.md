# Logical evidence across planned reads without verdict stability

`SourceReadLogicalDomains` retains the existing ambient domain over all
`usedNames`. Planned reads fix formula free names and structurally observed
constructor names. They can change constructor names at refinement-only
positions. A source avoid list therefore need not equal its target list.
Read agreement alone gives no sort obligation for a name missing from one list.

`Compatible` states the additional sort condition explicitly. A name present
in only one avoid list must admit every value in its named sort domain. Shared
names impose their original restrictions. `forward_ambient` and
`backward_ambient` prove preservation under the actual finite spelling map.
The proofs use each allocator's own avoid list. They do not assume that the
allocator avoids unused declarations in the backend context. Equal avoid
lists satisfy the condition. The all-Int domain satisfies it automatically.

`SourceReadLogicalQueries` records the three executed scope stacks: the source
cell, exact observations of the term, and complete actual identification.
The ordinary and Holds theorems transport mathematical evidence through both
maps. They include actual assumptions, positional aliases, generated sort
domains, and the original ambient domains. No global query-transport premise
or exact backend-verdict assumption replaces those proofs.

`SourceReadLogicalGuards.worker_supports` composes the result through every
constructor and both polarities. Scope entry derives acceptance of the exact-
observation stack from equality of the two executed runtime checks.
`public_supports` follows the independent-table public dispatcher. Its domain
compatibility and solver-soundness premises cover only the scoped contexts
actually allocated by that dispatcher. `integer_supports` instantiates the
complete theorem for the integer environment and a sound callback.

These are logical evidence theorems. They do not require
`SourceQueryTransport.Stable`. They permit a callback to return Yes on one
spelling and Unknown on another. The unused ambient declaration collision
from `GuardAlphaBoundary` remains possible in `SolverAdapter`: preflight can
return Unknown before submission. These theorems do not turn a rejected query
into a returned Yes, or equate backend-confirmed languages.

`CurrentReadLogicalPrune` composes the result with the actual evaluator-first
pruning loop and compiler decision. Its ambient values are unrestricted;
formula quantifiers still use the supplied interpretation's sort semantics.
`prune_sound` proves complete logical safety. `confirmed_retained` keeps
every original backend-confirmed term. `prune_contains` retains every logical
term after candidate completion and requires a backend Yes only on original-
edge restoration. `prune_exact` isolates that fallback adequacy condition.
`compile_exact` proves successful Boolean classification iff complete logical
validity. All these results omit the old spelling-stability premise.
