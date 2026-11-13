# Isolation through the actual shared child

The new public theorem is
`MicroCFTA.SourcePruningEnumerationSharedChildIsolation.observed_isolated_pending`.
It observes the exact successful shared `ChildDispatch.run` singleton.

A safe input state has an isolated pending slot. Its stored native handle has
an empty suspended bucket, and no stored suspended reference names its union-find
class. The child input constraints are bounded and avoid that class. Under these
conditions, the same slot retains its complete isolation certificate in the
actual returned cache. The theorem does not run a second worker or choose a
second endpoint. It requires no future model or output-state invariant.

Five private helpers follow the actual shared dispatcher, fold, incoming read
and write, and terminal path. The terminal path uses the same pure prefix
operation as the implementation. It does not cast a nonshared worker receipt.
The public theorem retains its exact reviewed thirteen-line interface, including
`bits + 2`. It does not generalize the width or add a resource/model premise.

The source has 369 lines, SHA256
`ada94bee92a6de405cd29f1d0c38a0858f8d13bb161f1a73634f256b04134aa2`.
Its six proof bodies are exact extractions from the checked private version.
Only the final theorem's name and visibility change. The four imports have an
acyclic closure of 2109 project modules without SharedEagerReservation.

The own checker builds the actual Lake module. Its strict report checks the
one exact public theorem name and accepts only `propext`, `Classical.choice`
and `Quot.sound`. It also replays the three archived fragment reverse patches
with GNU patch and fuzz disabled. The new module and its axiom report pass.

[source-history.json](source-history.json) preserves four private source trials,
the failed diagnostics, exact fragment hashes and reverse patches. A dependent
wildcard split first prevented equation generation. Exhaustive constructor cases
fixed that issue. The remaining error was an unused error wrapper restricted to
Type 0, while the actual shared error carrier has a higher universe. The final
private write lemma takes the raw successful-state equality directly. The caller
injects that same actual equality. This removes the unused wrapper and changes
no state premise, worker or endpoint.

To recover each complete old trial, take the pinned 6861-line eager resource
source at `c35b242b5fd2947553ced68243fd19a4cfc38ce6`. Apply the archived enclosing
forward patch. Replace its placeholder with the archived fragment for that stage.
The current fragment is obtained by reversing the final public name and visibility
change in this module. The three reverse patches recover the earlier fragments.
All four complete trial hashes were reconstructed and checked. No executable or
large execution archive is retained here.

From the repository root, run the standalone checker under the existing serial
Nix 4 GiB max/high scope, with swap 0 and one Lean thread:

```sh
python3 lean/restart-evidence/20261113-shared-child-isolation/check.py
```

This theorem proves a local structural effect. Whole eager-marker preservation,
finite output-model existence, original-library/query typing and the remaining
full-system obligations stay open. Native handle lookup at a changed caller is
transported separately by its actual native Post. No Haskell/Cabal/test-suite
file changes are part of this proof.
