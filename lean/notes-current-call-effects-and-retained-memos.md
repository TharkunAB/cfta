# Actual call effects and sound returned memos

Date: 2026-10-31. Branch: `formalize`. Goal: ACTIVE.
Source checkpoint: `8efe735ba7fad5a030ba63c9daf5eff8d8733713`.
Previous published evidence: `572dd4f7198c7bcf3502b73ad99552819698d220`.

## Strongest new statement

Start with the current `Context` and a resident, closed query.
Run the literal allocated conjunction call with its actual projection, exposure, and table budgets.
The returned fourth memo satisfies `SourceCurrentEmptinessMemo.Correct` at the actual returned heap.
This statement covers completed and failed calls.
Every completed answer satisfies `AnswerSound` for the original query.
A `True` answer excludes every term from the query language.
A `False` answer gives no proof of nonemptiness.

The call also retains the same inventory admission.
The old merge memo remains `Stored` at the returned heap.
The old fourth memo remains `Correct` there.
Every earlier fourth-table entry remains in the returned memo.
These facts consume the current invariant and current query facts.
They do not consume a future output invariant or a future row certificate.

The separate incoming-node theorem now retains every old pending handle through every actual incoming outcome.
It includes failure of the physical emptiness check.
It returns native `Stored` and the old cache's original `KnownOrdinary bound` at the literal returned Caller.
It retains the original Context, PendingRealized, Available, closed, Known, Fits, Room, and Stored input gates.
It adds no ordinary-domain gate on the incoming query.
It does not certify the newly returned enumeration Core.

## Checked implementation

| New module | Lines | Public laws | Result |
| --- | ---: | ---: | --- |
| `SourceCurrentConjunctionRowsWorkerEffects` | 186 | 1 | Actual rows retain SemanticHeap, Covered, heap growth, and issued-node history. Completed requirements are resident and closed. |
| `SourceCurrentConjunctionWorkerEffects` | 153 | 4 | Actual explore, decision, call, and allocated call retain the four heap facts on every outcome. |
| `SourceCurrentAllocatedNativeIncomingOldKnownAll` | 150 | 2 | Actual calls preserve old lookups. Actual incoming outcomes preserve the old pending cache. |
| `SourceCurrentConjunctionCallRetained` | 125 | 3 | Actual calls retain inventory and old memo facts. Failures return a correct fourth memo. |
| `SourceCurrentConjunctionCallSound` | 70 | 1 | Every actual returned fourth memo is correct. Every completed answer is sound. |

The five modules contain 684 lines and eleven public theorems.
The heap laws use the actual `SourcePruningTemplates.Symbol`.
The rows, explore, and decision heap laws remain generic in Formula.
The allocated and memo laws use `FullSyntax.Formula`.
The call laws cover cache hits, completed misses, and failed misses.
The cold heap laws cover Mu, Union, and resource exhaustion in the actual route.
They make no new equality-cache validity claim.

`SourceCurrentConjunctionCallSound.call_correct` first retains the entire checked lower-field result.
For a completed call, `WorkerCompletion.call_sound` derives the actual semantic receipt.
`SourceCurrentConjunctionMemo.verified` consumes that receipt, current readiness, current availability, and the old memo's correctness.
The current Context supplies the readiness and old correctness.
The failed branch uses actual old-memo preservation.
No new success, completion, row, table, or output-Context premise is added.

## Remaining call invariant

Returned fourth-memo correctness is now a checked actual-call result.
Full reached `Context` and full `Post` remain open on the general route.
The remaining obligations include complete physical readiness on failed outcomes.
They include reached OpenDepthReadback, CostHeap, equality-cache Valid and Fields, and equality-cache growth.
They include result-table Sound transport, global memo validity, and Mu probe cleanliness.
Heap growth alone does not prove these facts.
Fourth-table extension alone does not prove answer semantics.
The new actual semantic receipt proves the answer clause for this call.

The next physical proof should derive full `RowsAllocation.Effects` from current admissions.
Any partial equality result must state its exact heap and endpoint.
Fields on the old heap do not establish Fields on newly allocated edges.
NoNewMu must come from the actual route when a transport theorem needs it.

## Full proof objective

Prove the system result for the original admissible public inputs.
Every accepted output must satisfy the intended constraints.
Enumeration must produce the exact intended finite ordered prefix and configured stops.
Sufficiency must use the ORIGINAL depth and ORIGINAL resource bounds.
The proof must cover the optimized interned core and BOTH Native and Prepared workers.
It must include generic Mu, Union, and opaque inputs.
It must cover originalMap, domain, order, and SCC behavior.
It must cover signed, Set, default and weighted getters, row history, and constructor-sensitive NodeEq.
It must cover size, node count, order, rank, unrank, Prefix, tables, counts, and checkpoints.
It must establish the public, host, and Haskell correspondence.

The largest remaining proof is the actual fixed-original-depth recursive worker induction.
It must produce the reached Context/Post, admissions, memo identity, Fits, annotations, reservations, and resource lineage.
It must use the SAME captured sibling cache at the hook's actual Caller and query.
It must cover BOTH workers and every alias, renewal, writer, and opaque/default-source branch.
Prepared endpoint None supplies no hidden outer Caller certificate.
An inner preparation heap does not change that boundary.
Local callback fuel and per-step forecasts do not prove sufficient original global resources.
Fixed-work prefix laws do not prove termination or complete coverage.
Local conditional theorems and finite carriers do not replace this objective.

## Validation and evidence

All five modules pass focused default and strict checks.
Strict checks use `warningAsError=true` and `linter.all=true`.
Full Audit passes at 4,806 jobs and 83,739 checked theorem dependencies.
The public readback passes 1,332 declaration checks and 159 definition prints.
All eleven new axiom reports use only propext, Classical.choice, and Quot.sound.
The final public readback has 5,120,002 bytes.
Its SHA256 is `b28b24b11c7e290c56761aa070f186dc9e32f58234bed0c21d2f39d96b4f00b0`.
The prior 5,102,922-byte readback remains an exact prefix.
The intermediate 5,118,161-byte readback also remains an exact prefix.
Root read the complete new 17,080-byte, 243-line suffix.

All 602 prior protected sources remain exact.
The protected set now has 607 sources.
All 4,801 prior Lean files remain exact except Audit with five added imports and its exact old body.
All 835 native inputs remain exact.
Root retains eighteen actual production checks: sixteen pass and two failed drafts remain with full raw diagnostics.
Those checks retain ninety input snapshots.
The separate frozen probe owner retains thirteen earlier checks and 103 snapshots.
Its five passes, eight failures, source versions, generated dependencies, and diagnostic read scopes remain separate.
Every actual Lean command has verified 4 GiB memory.max/high, zero swap, and a five-minute timeout.
The checks run serially through heavy-management.

Root read all 684 final new source lines.
Root acquired two old repository cuts with 34 lines in total.
They are CurrentConjunctionWorker 49–74 of 108 and EmptinessMemo AnswerSound 28–35 of 129.
Root acquired no old whole source.
The separate installed stdlib acquisition has twelve explicit lines.
Owner scopes use cumulative ORIGINAL source vectors and retain complete immutable provider closures.

No Haskell defect, edit, or fix is established by this checkpoint.
No Haskell or native product execution is reported here.
FINDINGS retains this status for external implementation work.

Control: `/tmp/mcfta-current-call-control-20261031`.
Publication records: `/tmp/mcfta-current-call-packaging-20261031`.
Portable archive: `lean/restart-evidence/20261031-current-call-control`.
The goal remains ACTIVE. The full objective remains unproved.
