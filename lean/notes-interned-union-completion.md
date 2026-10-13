# First-run completion through root unions

`InternedUnionReferences.Retains` describes an actual source path to a
lexical input. The path can be a bare variable, a unary node edge, or an
alternative below nested root unions. `build_retains` derives the returned
record's free-name membership. It uses the actual source child result and
all branches of `makeUnion`, including singleton collapse, ordinary-edge
merging, and canonical cache readback.

`InternedUnionConstruction.Retentive` requires such a path for each enclosing
input at each binder. The binder body can have any root constructor that
satisfies the declaration. A binder with no enclosing inputs can have a
nested binder as its immediate body.

`InternedUnionConstruction.closed_completes` in `InternedUnionCompletion`
proves first-run completion directly from empty tables. The proof executes
both source probes, reservation, callback, root self filtering, and raw or
smart return. It derives `Live` from source construction and derives
interned pending names from actual reservations. The depth sentinel differs
from every pending name. Thus self filtering preserves each declared pending
name, and the inner depth key cannot equal a pending ancestor key. The proof
does not assume a complete callback or a stable whole-family key.

`InternedUnionCompletionExamples.program_complete` applies this result to
arbitrarily long closed chains whose bodies retain their inputs as bare
union alternatives. It derives complete record facts, empty pending
coverage, result availability, and exact replay after later cache growth.
`program_not_pending` excludes every pending result. `selfUnion_complete`
proves completion of the existing consecutive-binder fixture from its
source declaration, without evaluating that fixture in the kernel.

The focused build has 181 jobs. The isolated audit checks 7,831 theorem
dependencies. It permits only `propext`, `Classical.choice`, and `Quot.sound`.
These checks validate the Lean statements. They do not establish automatic
Haskell-to-Lean translation.

A separate temporary Haskell probe checks the same raw and smart union
chains at depths one through seven. All 14 cases complete, have no free
references, and replay with the same canonical identity. Raw outputs have
the requested binder depth. Smart outputs are `EmptyNode`. This executable
evidence is separate from the Lean theorem.

The retained-path declaration remains a restriction. General source
expressions can erase an outer input through computed empty records,
cleanup, or normalization without a declared retained path. The separate
erasure and selective-completion modules cover some of those expressions.
General changed-dependency source-call correspondence remains open.
