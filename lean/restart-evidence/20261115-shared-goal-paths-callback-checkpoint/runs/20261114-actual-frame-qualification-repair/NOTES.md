# Frame source name resolution and callback equation repair

Status: UNCOMPILED. Root's combined36 check found three frame diagnostics.
The first was an unknown resumeWithNarrow in the runtime frame definition.
The second was an invalid Typing named argument in the captured generation
header. That unqualified header name lacked its intended source namespace.
The third was the selected-frame callback rfl. It was not the captured-generation
proof: the full diagnostic shows the selected-frame equation at line11867.
All error forms in the complete log were inspected.

The repair adds one scoped explicit open of
SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.resumeWithNarrow.
It resolves both existing occurrences to the intended literal source function.
The Typing := Unit argument stays exact. All six new theorem headers and all
runtime definition bodies remain byte for byte. No new premise or weaker type
is introduced. The raw captured-generation header is preserved separately.

The selected-frame callback proof now unfolds its source frame equation and
uses the existing consume_complete equation explicitly. It retains the same
proposition, receipt, parent tail and actual endpoint. It does not add an
operational hypothesis. The other five proof bodies are unchanged.

The candidate derives from frozen bbc, including both generation proofs and
the current inner-tail reservation handoff. It adds no new theorem. Root must
rerun the complete strict module before assigning any new credit. The private
static capacity proof is independent and absent from this candidate.
All original targets and the prepared16 source/header remain byte exact.
No compiler, live source, Git, board, Haskell or tmp write occurred.
No Haskell defect was found. Clear-writing checks were applied.
