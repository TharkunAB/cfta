# Full physical readiness at actual conjunction call endpoints

Source head: `3c356b0738bf1bd4674693b3b8ba43d48c7dc755` on `formalize`.
Base checkpoint: `00c5297ced7f6c9941530b43ecd29e69d1ea4cc7`.
The goal is ACTIVE. The full original-input theorem remains open.

## Strongest current statement

For the modeled interned conjunction call, the original current caller context
and a resident closed query supply the inputs to the checked safety laws.
For any supplied projection, exposure, and worklist budgets, the literal call
retains full physical readiness at its actual returned heap and equality cache.
This includes failed outcomes. The same external unfolding and endpoint-query
memos remain valid. The returned fourth memo remains correct.
A completed `True` answer excludes every satisfying term.
A completed `False` answer supplies no nonempty witness.

These statements are separate compatible laws. No new theorem constructs the
complete returned `Context/Post`. Physical readiness includes semantic heap,
coverage, depth, cost, equality-cache validity, and reached field annotations.
It does not provide a sufficient original depth or a complete execution trace.

## Four checked modules

- `SourceCurrentConjunctionProjectionWarmEffects.lean`: 206 lines.
  `forest_effects` proves full physical `Effects` for the literal forest worker.
  Its inputs are current `Ready` and resident forest operands.
  Symbol and Formula are generic. Both budgets and the signed path are arbitrary.
- `SourceCurrentConjunctionRowsWarmEffects.lean`: 177 lines.
  Seven laws cover projections, their completed-value availability, classes,
  requirements, tuple, tuple list, and the literal rows pipeline.
  `rows_effects` takes current `Ready` and available input nodes.
- `SourceCurrentConjunctionWorkerWarmEffects.lean`: 140 lines.
  Four laws cover exploration, decision, call, and the allocated-call wrapper.
  Exploration takes current resident closed pending groups.
  The call laws take current readiness and the original resident closed query.
  Their conclusions name the actual returned physical heap and equality cache.
- `SourceCurrentConjunctionProbeBirth.lean`: 64 lines.
  Two laws cover actual stored unfolding, including newly created nested Mu rows.
  The generic law uses the initial source context, probe heap, and resident value.
  The current-caller law derives those inputs from the original `Context`.

The four modules have 587 lines and 14 public laws.
They add no future readiness, trace, completion, callback, probe-cleanliness,
`Fits`, sufficient-fuel ceiling, or ordinary-only caller premise.
The call's closed-query condition is an existing original condition.
The forest and rows laws add no closedness condition.

## Actual state and input production

The forest proof follows actual reader, constructor, list, and fuel recursion.
Each failure keeps its literal returned state.
Completed graph facts are derived only after an observed actual success.
Those facts supply resident constructor rows or available recursive inputs.
They are not public assumptions about a future run.

The tuple proof obtains the actual fold result and cache growth from current
resident rows. It constructs readiness at the INITIAL heap with that actual
post-fold cache. It then runs the requirements proof from this derived state.
The warm effects supply fields at the reached allocated heap.
This closes the previous initial-heap-only field gap for the actual rows route.

The exploration proof follows the actual budget and pending worklist.
The old cold rows law supplies only successful new-group residency and closedness.
Its semantic and coverage gates come from the current readiness.
The new rows law supplies full reached readiness on every outcome.
The allocated wrapper uses `physical_advance` for both returned components.

The stored-unfold executor is the actual source builder on encoded stored syntax.
The birth proof derives the exact replacement inputs from original residency.
It applies the existing all-outcome builder probe theorem.
It does not assume `NoNewMu` for unfolding.

## Verification and preservation

All four modules pass production builds and strict Lean checks.
Full Audit passes in default and strict modes: 4813 jobs and 83820 dependencies.
The public readback passes 1351 declaration checks and 159 definition prints.
All 14 new axiom reports list only `propext`, `Classical.choice`, and `Quot.sound`.
There is no axiom-free claim.

Eleven production commands pass. They retain 45 source-input snapshots.
Every actual Lean command uses verified serial 4 GiB memory.max and memory.high,
zero swap, and a five-minute timeout. Strict flags remain enabled.
The old unused-input warning from `InternedFreshOrdinaryClosedCompletion` is
retained in default build logs. The new strict module checks have no diagnostics.

All 610 prior protected sources and all 835 native inputs remain byte-exact.
Only four added Audit imports change an old Lean source.
The final protected and Lean inventories have 614 and 4813 files.
The previous 5125851-byte public output is an exact prefix of 5138887 bytes.
The complete new suffix has 13036 bytes and 203 lines. Root read all of it.
The full output SHA256 is
`7870c123c71ed4268ed5a31d57ec2ce3aa5bb74ae1375485d0dfe9dc2374f0ee`.

The original and repaired candidates, complete failure logs, source scopes,
provider closures, and actual execution receipts remain separate evidence.
The current rows and worker isolated probes retain five actual commands:
two pass, three fail, and all 23 preservation snapshots remain.
The unsupported isolated dispatch in the production harness ran no Lean command.
Its metadata error and the corrected separate probe route remain recorded.

## Next work and full objective

Full returned `Context/Post` still needs exact assembly of every caller field.
Physical `Ready` is one field. Table meaning and probe cleanliness are distinct.
The caller uses `ClassScan.Ready`. Its native `good` component is a separate gate.
There is no proved reverse conversion from the physical pair alone.
The actual inventory admission, stored and covered merge rows, fourth correctness,
global memo validity, and the Post extension fields must use their exact producers.
The next-stage table wrapper and exposure-list probe proofs pass isolated checks.
They are outside this four-module production checkpoint.
Their exact sources and status are recorded in `next-phase-status.json` in the
current control area. Actual forest and whole-call probe composition is next.

The local conjunction route uses actual stored unfolding and ordinary construction.
It has a direct probe-composition route through those operation-specific laws.
Generic native request prefixes still need actual operand and memo-frame production.
`Operands` excludes finish controls. A supplied `InputsThrough` or rich trace
does not produce the missing original-input frame invariant.
This generic native gap is separate from the local conjunction route.

The largest system gap remains actual recursion at fixed ORIGINAL depth for BOTH
native and prepared workers. Restore the SAME captured sibling cache at the
ACTUAL after-hook caller/query. Derive admissions, memo identity, annotations,
reservations, and one sufficient bound from ORIGINAL inputs and resources.
`PreparedNone` supplies no hidden outer caller certificate.

Keep generic Mu, Union, opaque, alias, renewal, writer, default, weighted, signed,
Set, originalMap/domain/SCC, and public adapter branches in scope.
The goal includes sound accepted outputs, exact finite ordered prefixes and
configured stops, size/node-count/order, rank/unrank, prefix/table/count/checkpoint,
global coverage, and host/Haskell correspondence.
Local budget safety does not establish original resource sufficiency or completion.

No Haskell source changed. No Haskell or native product program ran.
No new Haskell defect or fix was established.
Record every later Haskell fix in root `FINDINGS.md`, with locations and evidence.
