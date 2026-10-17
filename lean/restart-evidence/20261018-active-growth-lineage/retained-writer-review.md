# Retained Mu writer alignment

The final production source is `SourceCurrentRetainedMuWriterAlignment.lean`.
Its SHA256 is `7b90472203150878f29a7df43a0af2868f3789dd8a73427cb9d042284b98b6d0`.

The private mutual build, many, and edges proof produces the actual first writer.
It retains the exact key and candidate payload.
It retains the source prefix and all three callback histories.
It derives physical growth and issued-reference extension from the writer body return to the reader.
The reservation and completion cases preserve an earlier winner.
They install the current candidate only when the actual record slot is absent.

`Writer` contains no output comparison law.
It is separate from current selected-record membership.
The `retained` theorem derives both facts from the past source execution and later `Keeps`.
The `initial` theorem constructs the source execution from empty.
Its caller supplies no completed source graph or future callback.

Reconstruction requires `BinderFree` only for the recovered writer expression.
It permits recursive captured values and any available replacement.
It constructs both sequential stored calls, both final warm replays, availability, local histories, and `Related`.
`Related` includes physical-empty agreement and observations at every finite depth and view.
It does not assert physical Value equality.
The unused cleanup equation comes from the actual source-history unused law.
The warm request returns the selected stored payload and leaves the full reader unchanged for any callback.

This is a source-started selected-record consumer with explicit later `Keeps`.
It does not recover every later native publication from an arbitrary ready heap.
It does not prove that every recovered writer is BinderFree.
It does not close the recursive binder-body induction or general outer progress.
Existing Mu growth paths retain physical growth, but do not include the issued-reference extension needed here for `Keeps`.

The constructed witness uses a real closed source publication with live local use.
The later requester changes node row order and duplicate rows, and adds an Empty union member.
It preserves the mixed union order, so its exact warm source execution leaves the reader unchanged.
An ignored callback would return Empty, while the retained stored body is nonempty.
The replacement is the actual recursive Mu result.
The second constructed theorem invokes the initial producer without supplied writer or completion evidence.

Selected source check `retained-writer-direct-5` has zero bytes of output.
Selected canonical build `retained-writer-canonical-2` completes 630 jobs.
Selected public probe `retained-writer-public-2` covers all seven public heads.
Selected fixture check `retained-writer-kernels-3` has zero bytes of output.
Selected fixture probe `retained-writer-kernels-public-1` prints both complete proofs, signatures, and axioms.
Both probe sources contain all eight explicit options.
All selected runs use Lean 4.34.1 with verified 4GiB max/high and zero swap.

Direct attempt 4 and canonical attempt 1 contain an unused simp argument warning.
They remain preserved and are not selected.
The final correction removes only that unused argument.
Fixture attempt 1 asserts an incorrect unchanged heap after reordered mixed-union intermediates.
Its original failed log is preserved losslessly by `retained-writer-kernels-1.log.gz` and `raw-log-archives.json`.
The uncompressed original is also retained at the mapped path in `/tmp`.
Fixture attempt 2 corrects that order but leaves two negation goals open.
Fixture attempt 3 closes those goals and is the selected printer-free check.
