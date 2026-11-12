# Accepted native term size from current height and physical arity

accepted_size uses current SemanticReady, Available, DeepOrdinary, and a
numerical cap at every physical edge record. Every independently accepted term
has NumberedTerms.size at most the EXISTING nodeCount 1 arity (height value).
The proof reuses child_lt, current child availability, resident edge bounds,
and the existing finite sum bound. One accepted term selects one row per node.
The full guard interpretation and ambient environment remain arbitrary.

This is unweighted finite term size. It does not bound size sigma, total
allocation, all row occurrences, logical P/A/W, elapsed time, or default
Mu-representative synthesis. It calls no completion producer.

The strict checker checks every public theorem by its exact namespace and
emits an explicit #check and axiom report. Own-source warnings are errors.
checked.json pins the source. Reproduce under the existing serial 4 GiB cap:

```sh
python3 lean/restart-evidence/20261112-native-ordinary-term-size/check.py
```
