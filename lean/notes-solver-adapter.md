# Liquid Fixpoint query adapter

`SolverAdapter.lean` models the pure decisions in
`microcfta/src/Data/CFTA/Refinement/LiquidFixpoint.hs`.
It reuses `FormulaLowering` for formula, term, and sort translation.
It does not change the source collision policy.

The model preserves the ambient declaration list. It adds
`__microcfta_value : Int` only when that name has no supplied declaration.
Declaration lookup uses the first matching name. A fresh binding receives
the original name's declared sort, or `Int` when the original is undeclared.
`fresh_rejected`, `fresh_sort`, and `fresh_all_accepted` give the exact
preflight conditions. A fresh name that is already ambient returns `Unknown`.
It does not submit a query. Duplicate ambient or fresh names are retained.
They can cause a later solver error; preflight does not reject them.

The symbol collector follows `exprSymbolsSet` in the local source archive
for Liquid Fixpoint 0.9.6.3.7, in
`Language/Fixpoint/Types/Refinements.hs`, lines 431–453.
`formula_symbols_lower` proves that the emitted expression collector reads
exactly the source formula's free names. It includes function heads and
removes quantified binders. `mentioned_exact` includes the antecedent,
consequent, and every ambient assumption. `undeclared_exact` proves that
only names outside both the ambient and fresh declaration sets receive a
default `Int` declaration. `prepared_names` proves that the actual prepared
request declares every mentioned name. Hash-set iteration order is abstracted.

The asserted formula is the conjunction of the ambient assumptions, the
antecedent, and the negated consequent. `assertion_exact` derives its meaning
from the existing lowering proof. `unsat_iff_entails` proves that this assertion
has no model exactly when the antecedent entails the consequent under the
prepared declaration domains and ambient assumptions. `execute_sound` then
derives sound returned verdicts from a correct external `Sat` or `Unsat`
answer. It does not assume that Z3 decides every query or returns a verdict.

`responseVerdict` keeps conservative uncertainty separate from exceptions:

| External result | Adapter result | Replace context |
| --- | --- | --- |
| `Unsat` | `Yes` | No |
| `Sat` | `No` | No |
| `Unknown`, before limit | `Unknown` | No |
| `Unknown`, at limit | `TimeLimitReached` exception | No |
| `Error` | Rejected-query exception | Yes |
| Other response | Unexpected-response exception | No |
| Exception during check | Original exception | Yes |
| Fresh name already ambient | `Unknown`, no check | No |

The time comparison is an input Boolean. In the source it is
`seconds * 1000 >= fromIntegral milliseconds`, using monotonic-clock `Double`
values. The default limit is 10000 milliseconds. A time-limit exception is
created after a completed check returns `Unknown`; that branch does not
replace the context. A thrown exception during the check does request a
replacement. `finish` models these distinct control paths.

Kernel-evaluated examples reproduce the ambient-name boundary. Declare the
unused name `__microcfta_actual_0 : Int`. Bindings using generated names 0 and
1 fail preflight and return `Unknown`, even for a valid `Top` query. Bindings
using names 1 and 2 reach the same query and map its `Unsat` response to `Yes`.
`top_entails` proves that the query is valid under every declared domain.
The examples use the complete pure `execute` function. The existing
`repro/GuardAlphaBoundary.hs` separately confirms `(Unknown,Yes)` with Z3.

The external boundary remains explicit. The proof does not certify SMT
serialization, name encoding, the solver, floating-point timing, `MVar`
locking, exception masking, bracket cleanup, or process replacement. A
`replaceContext = true` result specifies the requested control action. It
does not prove that process creation succeeds or that the next process has
no unread response. Those are IO properties. The executable preflight
counterexample needs none of those properties.

Validation: the pinned toolchain builds `MicroCFTA.SolverAdapter` without
`sorry`, custom axioms, or `native_decide`. No Haskell source changed.
