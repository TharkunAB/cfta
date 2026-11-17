# Record layout repair

FROZEN UNCOMPILED. No theorem credit. Original64eab/header34a9 and failed82550 check are preserved.

The public header moves `values :=` to a new record-field line. The entire `.values.set` expression is on that same line. This repairs Lean record-field layout; it changes only whitespace. The proof-local afterShape repeats the same record expression, so its layout receives the identical repair before the next check.

The old/new public-header strings and old/new proof bodies are exactly equal after removing whitespace. All tokens, binders, premises, native/cache endpoints, five supplied fuels, full scs bucket and conclusions are unchanged. The original header is retained in ORIGINAL-PUBLIC-HEADER.lean.txt. The exact two layout hunks are in REPAIR.diff. No other proof byte is changed. Probes are byte-exact.

No compiler, Source, Audit, Git, board or tmp action was performed. Default limits remain unchanged. This is a local shared-dispatch mark receipt; the whole chronological role invariant and joint finite accepted model remain open.
