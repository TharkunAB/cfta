# Initial current filter interval

Status: frozen source draft. Root has not checked this source.

The 148-line source has one private theorem, `current_initial_filter_interval`.
Its 42-line header is byte-identical to approved header `1eef0b75bf26ea896b3379027e508211789480ea6e770b2c59c4e921dc9362df`.
Source SHA256: `022cd270da57d3fb7197653bf17d8f117e433e6fb1fceb30f60be7d182a8e7e7`.

The proof calls public `current_candidate_app_operands` once. It retains the same source chunks and factory facts.
It applies `build_row_origin` to the observed initial root row and the same completed whole build.
The singleton filter source fixes the row index to zero. Its recorded empty prefix fixes `call.current = empty`.
The same `call.called` supplies the adjacent goal and candidate builds. Their endpoint is `call.middle`.
The same `call.made` supplies the actual filter edge. Its singleton row build aligns the actual root makeNode return.
The goal build derives the candidate-start CapSourceHistory.Context through `Context.build`.
The original call's middle_growth supplies growth from the candidate endpoint to the whole final heap.
No independent build witness or desired source-parent equation is used.

Likely elaboration sites are dependent `SourceRow.node` elimination, the singleton source equality, and simplification of recorded `buildMany`/`buildEdges` equations.
The draft retains actual initial root-row membership as an observation. It covers the first filter only.
Identity membership, later app edits, output survival, default coverage, and finite semantic witnesses are not conclusions.

`source-pins.json` records the exact current dependencies. `draft-receipt.json` records the static header check.
No compiler, live source, Git, Haskell, board, or cleanup action was run.
