# Shared language compatibility

This packet checks the complete Audit import frontier. The frontier includes
every changed module and every affected importer. The previous source bytes
remain unchanged. Audit adds imports before the previous bytes.

Run check.py from any working directory under the existing serial 4 GiB cap.
The checker verifies the exact source hashes, source diagnostics, and standard
axioms. This check does not establish end-to-end source completeness or
full Haskell correspondence.
