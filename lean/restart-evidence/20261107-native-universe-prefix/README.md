# Returned graphs over the actual synthesis universe

AllTypesPrefixClosure.hs reads literal stored children from one public
rawSearchSpace call per case. Its poly component supplies the actual U.
Other component annotations supply generalized prefixes. The rigid query
annotation supplies the missing-var_e case. No private kernel environment
or separately constructed replacement grammar is supplied.

Seven fixed cases cover Int, List, Pair/function types, unequal-depth
variable repetition, arrow/catalog overlap, rigid var_e, and unary Fun.
Each checks both U/P intersection orders, one repeated intersection, and
P/Q intersection. A separate occurs-check case reduces equated Pair a a
and Pair b (List b). Each case has a three-second observation limit.

The current-source run completed all eight cases and all 58 returned graph
observations. Every returned graph was closed. Each reachable stored Mu had
the identity of that case's actual U. Both intersection orders and repeated
intersection had equal returned identities in the seven cases. The
occurs-check case reduced to Empty. Missing rigid var_e and unary Fun can
also produce Empty. These are finite observations, not general theorems.

The walker reads stored Mu bodies and union members. It skips Rec leaves.
It does not count depth/ordinary probes, unused records, domains, memo cells,
or transient allocations. The run does not establish semantic closure,
native constructor correspondence, general termination, or a work bound.

An initial extraction through getPath failed its Mu-tag checks. It supplied
no closure evidence. The final fixture reads literal edgeChildren after
stored-shape checks. The checker rejects incomplete input extraction,
timeouts, and exceptions. Its sharing assertion is diagnostic; a violation
does not by itself establish a language bug.

The local generator build passed with GHC 9.14.1 -O0 in the project-derived
Nix shell with GMP. fourmolu passed for the final fixture. cabal-gild checked
the unchanged generator Cabal file. No full test suite or CI is claimed.
observed.json contains exact source hashes, source trees, outputs, and case
summaries. No build archive is needed.

Run check.py serially under the repository's 4 GiB capped proof workflow.
Use --case NAME on the Haskell fixture for a fresh-process observation after
a timeout. Keep runtime logs small.
