# Independent stored allocation review

Reviewed frozen `lean/MicroCFTA/InternedFreshOrdinaryStoredAllocationBudget.lean`,
46 lines, SHA-256 `e0693a5009bd94a3a4dd83dac1108183581bf605755ea3f2e0ed9b6c451b2691`.
No material issue was found. The production source was not changed.

## Exact contracts

`executeCharges` applies both full fresh-schedule budget functions to the initial
`encode (leaves value) [] value`. Repaired stored substitution uses exactly this
syntax. It maps replacements into the lexical capture environment. Variable
lookup returns a captured value without reconstructing that value. The allocation
bound therefore needs no bound on replacement sizes or environment size.

`execute_bound` follows the actual repaired `execute`, not the older executor or
its binder-free correspondence. It applies at every actual stopping outcome,
including pending readback. It requires no Facts, availability, successful return,
or `PreparedWithoutMu` premise. It covers nested encoded Mu through the full fresh
schedule theorem. It makes no claim that arbitrary malformed replacement records
have semantic validity or that an arbitrary current cache admits completion.

`unfoldCharges` charges the literal stored body of a Mu. Other input constructors
use `(0, 0)`. `unfold_bound` follows those exact cases. Mu uses the actual old
binder replacement environment. Every non-Mu case returns the identical value
and state. No successful callback or desired result bound is an input.

These are local input-value syntax bounds. They do not derive initial headroom
for a complete recursive Head, projection, editor, or native query. A later
produced body still needs a profile bound from the original caller inputs.
There is no whole-library Haskell correspondence claim.

## Imported integration

`stored-budget-public.lean` checks all four declarations with explicit full
signatures, proofs, universes, deep terms, and axiom reports. Final log
`stored-budget-public-1.log` has no diagnostics.

`stored-budget-kernels.lean` builds a raw outer Mu with a nested open Mu. Both
binders use local references, and the outer source captures an intersection
reference. The generated root remains open. Its stored body contains an open
nested Mu, so its stored reconstruction is not binder-free.

- `execute_arbitrary_replacements` derives the own literal build return and proves
  that this actual input is not `PreparedWithoutMu`. It bounds repaired execute
  for any replacement function and any current heap. The replacements have no
  size, availability, or closure restriction. No completed substitution is given.
- `constructed_unfold` derives physical facts, source Context, the depth heap,
  complete record coverage, and input availability from the own build. It proves
  that the actual stored body is not `PreparedWithoutMu`. It constructs its own
  successful unfolding and derives availability and both bounds at that same
  returned heap. No completed unfolding is given.

Final `stored-budget-kernels-2.log` passed with no diagnostics. The only reported
axioms are `propext`, `Classical.choice`, and `Quot.sound`. The failed first kernel
source and log remain present. It lacked an explicit completion import and used
a dependent match where a concrete stored-body witness was required.

Canonical `canonical-stored-budget-1.log` passed all 174 jobs. Root strict direct
two passed with an empty log. All reviewed source and probe bytes are frozen in
the separate stored-budget manifest.
