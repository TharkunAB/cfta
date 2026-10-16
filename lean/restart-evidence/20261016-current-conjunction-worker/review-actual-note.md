# Independent review of the literal checked conjunction endpoint

Reviewed on 2026-10-16 at 12:56 CEST.

Result: no material defect found.

Reviewed source: `lean/MicroCFTA/SourceCurrentAllocatedConjunctionWorkerActual.lean`.
SHA256: `4538d8437ae655e32bccc7bd2398575837450aa918a99be7fcb14fc6eacf7fc8`.

## Actual graph and returned state

`verified` extracts the completed raw observation from the supplied literal
checked success. `call_sound` derives the current `Call` at that same heap,
equality-operation state, Boolean, and fourth memo. `Caller.actual` derives
its logical global read receipt and the returned `Post` from the initial
`Context` and query residency. It does not take a future context or result
language as an input.

`finite` constructs a finite current `Call` from those initial facts. Its
actual graph supplies sufficient projection and read bounds. The checked
lift uses its exact returned physical state. The caller retains both native
table families, domain cache, both outer table families, warm merge memo,
and the same input inventory. The actual fourth result memo extends the
initial fourth memo. The initial fourth `Correct` invariant is part of
`Context`; it is not derived from arbitrary warm Boolean entries.

`call_done_stable` and `call_done_unique` compare complete literal checked
returns. They do not require a semantic law. Uniqueness includes the whole
checked state and the entire fourth memo. The admission budget stays fixed
when projection and read bounds increase.

## Semantic and source boundaries

`AnswerSound` proves that true excludes every independently accepted term.
False has no acceptance or nonemptiness conclusion. Open queries can return
false without exploration. A fourth-memo hit precedes the body guard.
Failures retain the reached physical state and the initial fourth memo;
they install no completed answer.

The worker follows a selected completed sequential read schedule. Source
`Enumeration.hs` uses lazy rows and lazy `Map.insert` values. The proof does
not equate that schedule with GHC demand, host publication, or actual host
global-table events. Its global receipts are constructed logical evidence.
Source `emptinessBudget` is an `Int` constant; the worker takes a fixed
natural-number budget. The module does not claim a general signed-budget
conversion. It does not complete the outer recursive reduction worker.

## Direct checks

Pinned Lean 4.34.1 checked the imported final canonical module. There was no
canonical build in this review.

- Four public axiom probes and four public signatures passed with exit 0.
- All public dependencies use only `propext`, `Classical.choice`, and `Quot.sound`.
- Four external integration kernels passed with exit 0 and no warnings.
- No probe log contains `sorryAx` or an error.

The kernels check complete-state uniqueness at incomparable bounds; finite
literal execution with the same inventory and native tables; a supplied
true success with its own actual call, reads, fourth correctness and
extension; and two successive literal calls from one initial context.
The second call consumes the context and query residency derived by the
first call. No completed graph or supplied future postcondition is needed.

The earlier `review-manifest.json` and its recorded evidence remain unchanged.
