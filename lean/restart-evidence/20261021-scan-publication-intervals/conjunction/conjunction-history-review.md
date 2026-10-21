# Actual conjunction publication intervals

The sole public theorem is SourceCurrentConjunctionPublicationHistory.call.
It consumes an actual ConjunctionMemo.Call, physical RowsAllocation.Ready at
entry, and availability of the actual query. It derives a causal Mu publication
History from that exact entry heap to that exact returned heap. It requires no
input cap, guard predicate, memo correctness, or earlier publication history.

The private proof follows the literal graph. Each actual exposure uses public
RequiredPublicationHistory.read. Each projection job uses its actual Forest
and public RequiredPublicationHistory.forest. Their physical effects supply
semantic readiness, costs, and retained input availability at the next cut.
Class requirements retain the original forests in their source order.
Tuple requirements consume the actual resident closed rows. Equality-cache
folds change no constructor heap. Tuples compose their own histories in order.
Rows compose the SAME exposure and allocation graphs.

Worklist empty and skip branches retain the entry heap. An actual admit branch
uses its real skip=false receipt to derive admitted operand closedness. Public
RowsSoundness.rows_verified derives the SAME middle Ready and availability of
the generated pending requirements. Its Keeps retains the earlier pending
inputs. The induction composes the actual row interval with the actual tail
interval. No completed row supplier or future invariant is assumed.

An open Decision and a memo hit retain the constructor heap literally. A closed
Decision and a memo miss consume their actual worklist. The theorem concerns
causal physical publication intervals. It does not require a sound memo answer
and does not prove one. It does not equate the chosen graph schedule with lazy
GHC evaluation or prove unfinished Parent/Scan preservation.

The reviewed first source had 179 lines. Strict1 and FULL1 returned zero, but both logs reported unused private
section typeclass parameters. FULL1 retained standard axioms and the same
public type. The final source moves
only those instance binders to the declarations that use them. Every proof
body remains unchanged. It has 178 lines. The checked and printed public types
are identical within the selected readback and across both source versions.

Selected checks are conjunction-history-direct-2 and conjunction-history-public-2.
The selected strict log is empty. The selected FULL log has all eight printer
settings, no omission or warning, and only propext, Classical.choice, and
Quot.sound. All four actual Lean commands returned zero. Both warning-bearing
successes remain unselected and archived. There is no elaboration failure,
canonical job, fixture, or official edit. Every command retains its source,
raw log, usage observation, and effective max/high 4 GiB, swap zero, five-minute
limits. Metadata diagnostics also remain archived. One rejected the legitimate
Worklist.admit constructor with an overly broad token check. Another corrected
the first strict log accounting. Neither diagnostic is a Lean failure. The portable verifier checks all these facts from its own files.
