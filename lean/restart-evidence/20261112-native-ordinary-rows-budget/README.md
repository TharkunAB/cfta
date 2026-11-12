# A structural budget for the current ordinary native snapshot

rank reads the existing ordinary height from the actual current payload.
Empty and omitted records have rank zero. rank_encode uses current Facts
and Available. rank_strict proves strict decrease at every child of EVERY
snapshot row before guard evaluation. It also covers unrelated ordinary nodes.
Mu, union, and reference records have no ordinary snapshot rows.

budget instantiates the EXISTING structuralBudget with this rank. It needs
no future supplier, width premise, completion call, or DeepOrdinary premise.
The native component language theorem still needs DeepOrdinary. The budget
is for this snapshot graph; it does not assert the language of all retained
native Mu records or complete enumeration work.

The strict checker checks every public theorem by its exact namespace and
emits an explicit #check and axiom report. Own-source warnings are errors.
checked.json pins the source. Reproduce under the existing serial 4 GiB cap:

```sh
python3 lean/restart-evidence/20261112-native-ordinary-rows-budget/check.py
```
