# Documentation-comment parser repair

UNCOMPILED. Preserve the original87 candidate and failed73179 log.

The only changes replace two Haddock-style documentation delimiters with ordinary block-comment delimiters immediately before `omit ... in`. Lean requires a declaration after a documentation comment. Both complete headers, both proofs, all premises, all runtime budgets and all probes remain byte-exact. Reversing the two delimiter changes reproduces the full original append exactly.
