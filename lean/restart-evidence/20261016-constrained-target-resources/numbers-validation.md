# Initial Target budget numbers validation

Date: 2026-10-16 20:39 CEST.

Source: `lean/MicroCFTA/SourceCurrentAllocatedFiniteOrdinaryTargetBudgetNumbers.lean`.
The source has 255 lines. Its SHA256 is `c7980a8b6a136bc667a261c0f567446eeae67af43eaa32707e91744d94456e0e`.
The evidence copy is byte-identical. The production source is frozen.

## Checks

- Direct source check 1: terminal exit 0, no diagnostics.
- Parent canonical build 1: terminal exit 0, 1314 jobs. Parent confirmed the terminal result. The raw log retains the historical unused-input dependency warning. The new module has no diagnostics.
- Imported public checks: terminal exit 0. All 31 public declarations have an axiom probe and a full signature probe.
- Imported integration checks 1: terminal exit 0. All 4 kernels have an axiom probe and a full signature probe.
- Final imported logs contain no warnings, errors, or `sorryAx`. The reported axioms are subsets of `propext`, `Classical.choice`, and `Quot.sound`.

No production or probe correction was needed after the first direct checks.

## Recurrences

The original forest limits are rows R, arity A, count C, projection depth D, and height H. The common operand profile is `Q = envelope (forestRows R C D) H`. Native queries use arity `B = max A 1`, including the sentinel case.

The generic profile recurrence is `T(Q,0) = Q` and `T(Q,k+1) = max(Q,T(Q,k)) * max(Q,T(Q,k))`. The common operand profile fits every tail result. Each step and every input row-limit increase retain earlier profiles. Since Q fits every tail, the successor also equals the square of the previous tail profile.

The generic node recurrence starts with the operand node cost. Its successor is the current operand cost plus the shorter tail cost plus `Native.nodeBudget (max Q (T Q k)) B H`. The edge recurrence uses its own operand edge base cost and the same conservative native Work limit. Native.nodeBudget bounds all constructor Work, so it bounds each supply's requests separately. The height argument H stays fixed through every step.

Initial aliases are `targetRows R C D H k`, `nodeBudget R A C D H k`, and `edgeBudget R A C D H k`. They substitute the actual OperandResources profile and cost functions. Here k is the number of additional operands after the seed. The fold has k+1 operand evaluations and k native queries. These aliases concern the nonempty, first-seeded Target fold. Empty Target execution remains a separate identity branch.

The public API includes base and step equations, the original operand profile inclusion, additional-operand count monotonicity, and joint monotonicity in all original limits. The parameter proofs include the original Projection profile, literal occurrence bound, Merge budget, and native Work bound. They require no physical or semantic premise.

## Integration checks

1. Two additional operands grow the row profile from 2 through 4 to 16. Distinct operand node and edge costs produce the expected totals 51 and 45. The base operand is counted once and each successor adds one more operand.
2. Initial arity zero widens to native arity one. At two additional operands, the concrete initial aliases compute 15 node and 9 edge requests while retaining row limit one.
3. Widening every initial forest limit and increasing the additional-operand count retains all earlier output-profile and request budgets.
4. OperandResources.complete constructs the actual seed operand from initial full checked readiness, inventory admission, resident captured profiles, and legitimate warm tables. The kernel derives the k=0 profile, both budgets, actual Work trace, and both final supplies at the same returned checked state. It supplies no intermediate profile, output count, or completion premise.

## Scope

The production module is pure budget algebra. It assumes no execution, successful result, returned profile, numeric capacity plan, or callback. It does not alone prove the whole Target execution or layout capacity. The separate actual Target resource proof must connect each source-ordered prefix to these recurrences.

Both supply bounds use the complete native Work budget conservatively. They do not claim separate tight native node and edge counts. Equality operation allocation, host demand, instruction counts, repeated passes, and complete outer cumulative capacity remain separate.

No older source, Haskell, Audit, root document, or earlier frozen evidence file was edited. This owner ran no Git or Lake command. New owned text has one final newline and no blank line at EOF. Derived compiled objects remain outside the evidence directory.
