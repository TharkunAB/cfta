# Complete Local public printing

The first imported public log omitted one dependent proof argument in the
`Receipt.reads` signature. The text was `saved ⋯ memos final`.
This was a printer omission. It was not a production error.

The frozen `local-check-manifest.json` and all of its 55 entries remain
unchanged. Its first public log is retained as historical evidence. It is
not counted as the final 12-pair public check.

The new `local-check-public-2.source.lean` adds only
`set_option pp.proofs.threshold 254` to the first public source.
The same pinned strict Lean command executes this immutable snapshot.
The new log contains all 12 explicit signatures, proof prints, and axiom
checks. It has no ellipsis, truncation marker, diagnostic, or `sorryAx`.
All axioms belong to `propext`, `Classical.choice`, and `Quot.sound`.
The final production files remain unchanged.

The earlier three constructed integration pairs remain final. Their log
contains no ellipsis or truncation marker. Their stripped source passed
strict Lean with an empty log. This formatting repair changes no theorem,
proof, premise, resource forecast, or integration result.
