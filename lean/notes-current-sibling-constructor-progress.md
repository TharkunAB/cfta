# Strict progress at the actual prepared sibling event

Date: 2026-10-29 23:54 CET. Branch: formalize.
Source and Audit: c7bc62b5f0f0080369f13ce738b469589521658c.
Last fetched main: 7b8db072fbde44f20ce9a803736de5624050f038.
The full formalization goal remains ACTIVE.

The actual prepared finite sibling scan now gives strict constructor progress
at its chosen accepting event. The event retains one compatible accepting
assignment, ProperState, the complete recursive Packet and a strict decrease
in pending-term cost. It also retains its actual native Post and query endpoint.
The scan keeps every earlier receipt, ordered output and resource certificate.
It can instead retain an exact earlier failed hook before the chosen event.

The whole-system result remains conditional rendered-output soundness under
the checked semantic and resource contracts and the fixed PCS interpretation.
Whole-state Discharged remains separate. DONE does not imply Discharged.
General finite-value coverage and public Haskell correspondence remain open.

## Full objective and next control problem

Prove sound output and intended finite-value coverage for the actual system.
Derive sufficient resources and controls from original admitted public inputs.
Retain exact configured order, callbacks and stops. Connect the optimized
interned core, recursive enumeration, unfolding and public APIs to Haskell.
Preserve the earlier constructor/equality laws and exact size/rank contracts.

The largest coverage gap is a uniform bound for earlier recursive alternatives.
A chosen accepting assignment can rank its own constructor branch.
It need not satisfy an earlier incompatible or unproductive alternative.
Each sibling starts from the same captured enumeration cache. Only native
caller/query effects advance. Pending-term cost cannot telescope across siblings.

Recursive fuel has a different recurrence from native work and reservations.
Each expansion consumes one recursive level. Its siblings all receive the same
remaining fuel. For a finite actual expansion tree, sufficient fuel has the
shape 1 plus the maximum continuation bound, including parked restarts.
Native work and resources still compose in their actual order.
This recurrence is a source-derived proof plan, not a checked new theorem.
The missing step is to derive a finite tree or equivalent bound from original
inputs, including earlier branches with no accepting assignment.

Investigate a finite universe of reachable boundary handles and trie path sets.
Combine unused recursion keys with ordinary height and exact neutral-step laws.
MergedOrdinaryHeight.child_lt already covers every ordinary child without an
accepting model. Model-relative key ancestry bounds only trie shape. It does
not supply one original native-handle universe for incompatible branches.
Do not add future completion or endpoint-model suppliers as public premises.
No fully admitted all-capacity earlier-failure counterexample was established.

Global resource derivation, neutral-step control, symbolic unfolding/public
coverage, exact public order/stops and Haskell correspondence remain open.
The known initial_boundary_done example retains recursive placeholders at
EVERY worker/recursive fuel. More fuel alone cannot establish discharge.

## Configured stopping and actual failure

A configured stopping predicate makes Restart.decision return none.
Both workers return complete with one metadata-bearing partial output.
A successful callback that rejects returns complete with no output.
These complete outcomes permit the next sibling to run.

An earlier stopped hook is an operational failure. It can retain exhausted
recursive fuel, an unsupported observation or a failed callback observation.
The scan keeps that hook's outputs and stops its suffix.
Exclude that failure to reach a later chosen edge. Keep intentional partial
outputs and their configured order.

The existing finite_complete laws stabilize exact outcomes, including failures.
The prepared moreDepth laws preserve complete results and output prefixes.
They do not prove that some complete recursive fuel exists.
Repeated boundary parking and recursion keys that omit union-find IDs invalidate
simple looping/fresh-ID counterexamples. See the earlier-stops report for gates.

## New checked head result

Read SourcePruningEnumerationPreparedFiniteHeadProgress.lean.
Its namespace is SourcePruningEnumerationPreparedNativeHookResources.
The new theorem is head_finite_complete_resources_accepting_progress.

The theorem keeps the entire old operational head resource result.
It adds original ProperState before.core. Packet alone does not imply it.
For each original accepting assignment, the proof derives the projection,
arity and exact edge reservation from original Packet/Fits/knownHeap and
HeadReserved at that head input.

The existing constructor Packet producer gives one compatible extension,
the actual captured execution, full returned Packet, ProperState and strict
pendingSize+1 decrease. The prepared parent stays separate from its stored handle.

The old operational producer fixes a receipt and bound B before it quantifies
accepting assignments. The constructive producer gives indices r,n,p,h,k.
Compare both CapturedEdge equations at B+r+n+p+h+k. Injectivity identifies
the fixed actual receipt, caller, query and cache. Transfer all added model,
cost and Packet facts from that SAME constructive assignment.
The original operational bound B remains unchanged.

The progress Packet retains its own explicit inventory and full memo witness.
Its query equals the actual receipt query. Its Post starts at the actual head
caller. It is not identified with the resource producer's auxiliary witnesses.

## New checked whole sibling result

Read SourcePruningEnumerationPreparedFiniteSiblingProgress.lean.
Its namespace is SourcePruningEnumerationPreparedFiniteSiblingResources.
The theorem is alternatives_finite_complete_resources_accepting_progress.

The proof retains the complete old ordered scan induction and original bound.
It uses the stronger head observer. The same captured ProperState passes
through every sibling. Parent availability and Satisfies pass through actual
native Posts. Each event keeps its exact adaptive stage seed and HeadReserved.
The tail uses the original common-work identity. No semantic bound is inserted.

The chosen-event case now includes SAME-model strict pendingSize+1 decrease,
ProperState and full recursive Packet with exact progress Post/query.
It keeps those head facts even if that chosen event's later hook fails.
The earlier-failure case remains exact. It retains the full failed hook,
prefixOutputs++hookOutputs, stopped result, native endpoint and OutcomeResources.
No chosen model or cost is claimed for an incompatible earlier failed edge.

Both old Coverage modules remain byte-exact. Remove only the added ProperState
input, added chosen-result clauses and new theorem names from the new headers.
The complete 6009-byte head and 9269-byte sibling old headers recover literally.
The old 2340-byte and 1880-byte operational result blocks remain literal.
The complete 784-byte earlier-failure result remains literal.

## Actual callback reuse and remaining composition

The old local ConstructorCallback/PreparedConstructorForecast continuation uses
Recursive.Failure. The prepared scan uses PreparedRecursive.Failure.
The direct and prepared workers also have different ordinary dispatch.
Do not instantiate the old continuation with the prepared worker.

Existing PreparedCallbackModels.callback_finite_complete_resources_models and
PreparedCallbackProgress.callback_record_progress already use the actual
prepared worker and its failure type. Their namespace is
SourcePruningEnumerationPreparedRecursive. They retain the same model, exact
callback/resume equations, Packet, ProperState and not-stuck facts.
Original Refutes/Avoids/ProgramEncoding gates derive callback=false and updated
refutations. Reuse these APIs at the new actual chosen head.
The present two laws stop their added semantic progress at the captured head.
They do not prove the future recursive result or whole-worker completion.

## Verification and preserved evidence

Strict Audit passes: 4672 jobs and 82377 theorem axiom checks.
Public readback passes 981 checks and 78 definition prints.
Its complete prior 4088038-byte output remains an exact prefix.
Root read all 39503 new bytes through three reversible indent-count parts.
Both new axiom lists use only standard Lean axioms.
The full 4127541-byte log has SHA256
7247b96b068bb5334170d4b609406019c599b9b756e4804c3929338aa5250697.

Nine measured Root proof commands retain seven passes and two failed drafts.
The first head build lacked a direct import. The first Audit build put its
import at EOF. The repaired inputs pass. Neither repair changed a theorem
statement or proof body.
All 24 command input snapshots verify. Three strict mappings bind final sources.
Every command has measured 4 GiB memory.max/high, zero swap and a five-minute cap.
The old unused-input warning remains unchanged. No suppression was added.

All 471 prior protected proofs and 831 Haskell-related identities remain unchanged.
Of 4670 old Lean sources, only Audit changed. Its entire old body follows one
new import. final-strong-sources.json binds 473 current protected identities.
All earlier NEXT-PROMPT, HANDOFF and FINDINGS bodies remain exact suffixes.

Root read all three complete final review reports. It verified 93 pinned
payloads, all 52 source scopes and 15 Root source scopes.
The earlier-stops review retains its failed out-of-range request and exact
replacement. The stage-model review retains its whole CapturedEdge display
truncation and exact run-definition reread. No whole-body claim relies on it.
The final review read both complete new sources without truncation and verified
their exact successful strict inputs and complete contract recovery.
All requested/actual endpoints and original budget counts remain explicit.
The earlier timestamp estimates and their correction remain in the report.

No Haskell source change, fix or new executable defect was established.
Retain every earlier Haskell fix and pickup item in FINDINGS.
Prior native/formatter evidence applies to unchanged inputs. No rerun was needed.

Evidence: lean/restart-evidence/20261029-sibling-constructor-progress.
The archive contains every sealed regular file without filtering.
Keep source and restored evidence immutable. Continue in a fresh writable area.
