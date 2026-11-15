[2026-11-15 05:35 CET]

UNCOMPILED proof-only repair. The original packet stays frozen.

The strict check failed at two impossibility branches. Their calls used
`(EnumerationExpandableIndex.frame folded recovered).core`. The observed incoming
call used `folded`. The simp rules unfolded the cache adapter but did not reduce
the framed core, so incomingObserved did not match. The resulting equation still
contained a match, and cases could not eliminate it.

The repair adds only `EnumerationExpandableIndex.frame` to the two affected simp
lists. The actual incoming observation then matches. Each retained-cache equation
reduces to none = some after. No premise or conclusion changes. The one public
header is byte-identical. All private helper source is unchanged. REPAIR.patch
records the two line changes. Probes.lean has the same public axiom probe.

Root owns validation. No compiler, live source, Git, board, Haskell or /tmp writes
were made. The all-retained theorem receives no mathematical credit until the
whole repaired module passes the strict check. The full same-root historical
finite-assignment goal remains open.
