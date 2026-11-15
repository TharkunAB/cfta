# Typed reference code and abstract actual read-step repair

Status: NEW UNCOMPILED proof-only repair. The original failed packet and its
complete 446-line diagnostic remain unchanged at their original paths.
No credit is claimed before Root's strict recheck.

The public header is byte-for-byte unchanged:
3db0cdaa2eb972c9b466a32d8e418e6572b34594d1df8642fc310c11f48e1a06.
All original source, full-P, identity/kind, domain-cache, later heap and exact
current read/full-state endpoint premises and conclusions are retained.

The complete Root diagnostic has three underlying effects:

1. The private reference_code conclusion built a fresh literal NodeRequest
   without Symbol/Guard annotation. Its typeclass metavariable was stuck.
   The conclusion now annotates that literal as NodeRequest Symbol Guard.
2. The missing reference_code identifier was a cascade from that failed
   declaration. No alternate theorem or additional premise is introduced.
3. The final broad simp expanded the public goal's deep source entry lets.
   It could not match compiled/bound/read and left a large raw step match.
   It also reported those unused simp arguments.

A tiny PRIVATE reference_read_step proves the actual compileReference/read
transition at an ABSTRACT domain/name/other/value/current, using the existing
bound-name and ACTUAL payload-read equations. The main proof applies congrArg
to its already selected compiled equation, then composes this abstract step.
There is no deep-let selector matching in the final operation. The actual full
current state stays unchanged, including native/domain and operation caches.

All source selection, genuine diagonal freshness, body-name binding, original
stored-U availability and exact current read proofs remain unchanged. No P at
the later current heap, current/old cache equality, future state, semantic child
law, admitted native history or model provider is added.

Only the NEW packet was written. No compiler, live Source, Git, board, Haskell
or /tmp operation was used. No Haskell fix was found. Original full C/M, source
admission and SAME-root finite joint accepted completion remain open.
