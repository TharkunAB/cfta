# Complete TYPE whitespace handling

This package changes saved-output metadata only.
The original reader requires identical raw TYPE bytes and stopped at pair_fold.
Root inspected all nine checked TYPEs and both differently wrapped printed TYPEs.
The new reader compares complete TYPEs after four-character ASCII whitespace normalization.
The rule preserves token separation. It does not remove non-ASCII whitespace.
Both raw TYPE views remain unchanged. Each head reports its actual byte equality.
Both raw hashes and the canonical TYPE hash are recorded.
The unique complete TYPE/body delimiter, privacy, actual axiom subset, receipt and output guards remain.
The materializer and diagnostic tail are byte-identical to V1.
The whole frozen V1 and six actual failed reader artifacts are retained.
The reader failure is a metadata failure. It is not a Lean failure.
The source, printer and sole successful FULL output stay unchanged.
No reader, prepared script, Lean, Git, network or repository write ran here.
Root and independent review must precede the second reader run.
