# Static token-detection correction

The first inline assembly stopped at its token-set completeness assertion before package freeze.
The scanner used [A-Z_]+. It omitted the digits in __H23_CONTRACT_SHA256__.
The corrected scanner uses [A-Z0-9_]+ and finds 33 distinct tokens in the nine tools.
The original frozen binding-basis count of 32 is retained as historical metadata and corrected here.
The bound draft with the remaining token is retained. The selected verifier now binds the exact repaired contract SHA.
No prepared tool, Lean job or repository action ran. This was an inline packaging assertion, not a proof failure.
