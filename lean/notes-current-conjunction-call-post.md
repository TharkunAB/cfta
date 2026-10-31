# Full context preservation for actual conjunction calls

The actual modeled allocated conjunction call now produces the complete caller
postcondition on every outcome. The original caller context, resident query,
and closed query are its only logical input gates. The budgets remain arbitrary.
The theorem keeps the same original inventory and the same external memos.
The complete system theorem remains open. Goal ACTIVE.

The source checkpoint is `1e574b48a1561357890d3b6c3cc6ba0518b0f088` on `formalize`.
Seven modules contain 794 lines and 18 public theorems.

The strongest local theorem is `SourceCurrentConjunctionCallPost.call_post`:

```lean
let actual := SourceCurrentAllocatedConjunctionWorker.call
  p h budget query before.checked before.fourth
let after := SourceCurrentAllocatedPartialState.advance
  before actual.state actual.memo before.merge
SourceCurrentAllocatedPartialInvariant.Post
  formulas solver inventory before after memos
```

Its original inputs are `Context formulas solver inventory before memos`,
`Available before.checked.native.machine.heap query`, and `query.free = []`.
It covers successful and failed outcomes at their literal returned states.
It takes no future Context, Post, Ready, probe, trace, callback, or Fits premise.
It adds no ordinary-only restriction or NoNewMu premise.

The returned Context has all eight required fields:

- `ready`: complete ClassScan readiness, including native `good`, scoped cache,
  semantic facts, cost facts, and idle facts.
- `admitted`: the same original inventory remains valid at the actual state.
- `sound`: both caller result tables retain their exact semantic laws.
- `stored`: the original merge entries remain stored in the actual heap.
- `covered`: the same merge entries retain their language coverage.
- `correct`: the actual returned fourth memo remains correct.
- `globals`: the same external unfolding and endpoint memos remain valid.
- `probes`: every completed Mu record retains its clean filtered probes.

Post also retains actual physical Effects and both cache-extension guarantees.
The merge cache is unchanged by this caller advance. The returned fourth memo
extends the original fourth memo. The native heap and equality cache are the
actual returned components.

The compatible completed-answer theorem remains conservative. True excludes
every satisfying term. False supplies no nonempty witness. Arbitrary-budget
safety does not establish completion or sufficient original resources.

## Actual probe composition

`ExposureProbes` retains probes through actual collection, node-edge exposure,
and ordered exposures. Stored unfolding uses the checked source builder. It
handles new nested Mu records from the original context and resident input.

`ProjectionProbes` follows actual reader, node, row, list, and fuel recursion.
It covers arbitrary signed paths and every actual outcome. Mu and Union remain
in scope. Completed graph facts provide later residency only after an observed
actual success.

`RowsProbes` retains probes through actual projections, classes, requirements,
tuple folding, tuple lists, and rows. Tuple folding changes the cache at the
initial heap. Requirements then uses that actual cache. The separate warm
Effects laws provide reached readiness for each subsequent operation.

`WorkerProbes` follows actual worklist and budget recursion. It derives the
actual generated groups from successful row results. It retains probes at
every actual exploration, decision, memo-call, and allocated-call endpoint.

The result-table and full-readiness wrappers supply their separate fields.
`ClassScan.advance_ready` derives native `good` from the original readiness
and actual physical effects. Physical Ready alone does not imply that field.
The final 54-line theorem constructs the complete Context and Post directly.

The public equality-decision instance remains general. The proof eliminates
its subsingleton equality with the canonical instance before it applies the
older soundness theorem. It does not change the original context or endpoint.

## Verification and retained repairs

All seven modules pass their final default and strict checks. Audit passes
4820 jobs and 83881 theorem dependencies. Public readback passes 1369 checks,
159 definition prints, and 18 new standard axiom reports. The new reports use
only propext, Classical.choice, and Quot.sound. This is not an axiom-free claim.

The complete readback has 5157554 bytes. Its SHA256 is
`189651a332311693b2e8d28ed0e1520c2c9483dc6169a424f4a8e7cbbfaf5ba8`.
The prior 5138887 bytes remain an exact prefix. The new 18667-byte suffix has
267 lines. All new source bodies and new public lines were read completely.

Nineteen actual commands retain 17 passes, two initial failures, and 139 input
snapshots. The worker proof needed literal empty-list reduction and distributed
dictionary congruence. The Post proof needed equality-decision alignment.
Both original failures and their exact source snapshots remain retained.
No linter or invariant requirement was disabled.

Every actual Lean command uses serial heavy-management execution, a five-minute
timeout, memory.max and memory.high of 4294967296, and zero swap. Each command
records the effective limits before and after execution.

All 614 prior protected sources and 835 native inputs remain exact. The Lean
inventory grows from 4813 to 4820. Audit has only seven added imports and its
complete old body as an exact suffix. The protected inventory grows to 621.

## Remaining complete-system proof

Existing worker laws construct stable actual outcomes and resource paths for
each supplied finite depth D under their stated gates. Such an outcome can
still exhaust. These laws do not choose a depth that gives the requested prefix.
The largest gap is sufficient original depth and progress for both workers.
Each sibling must restore the same captured cache at the actual post-hook
Caller/query. Admissions, identities, Fits, annotations, reservations, and
common resource bounds must follow from the original inputs.
Prepared endpoint None supplies no hidden outer Caller.

Selected-step completion and captured-cache restoration already have local
Post producers. The remaining induction must derive their actual cache and
resource premises at every recursive callback from the original inputs.

Generic native prefixes still need actual operand and evaluating-frame
producers. A trace or InputsThrough premise that already asks for those future
properties does not construct them. The full local conjunction Post theorem
does not prove that every native prefix or recursive worker satisfies it.

The top theorem must cover original admissible public inputs and the optimized
interned core. It must prove sound accepted outputs, exact finite ordered
prefixes and configured stops, and sufficient original depth and resources.
Mu, Union, opaque values, originalMap, domain, order, SCC and row history remain
in scope. Keep constructor-sensitive NodeEq and default, Map, Set, signed,
weighted, alias, renewal and writer branches. Size, node-count, order,
rank/unrank, prefix, table, count and checkpoint APIs remain required.
Public adapters, global coverage, and host/Haskell correspondence remain open.

No Haskell source changed. No Haskell or native product program ran. No new
Haskell defect or fix was established. Record every later Haskell fix in root
FINDINGS with its source location, reason, and verification evidence.
