# Finite full-guard rows from current native payloads

The snapshot reads the actual issued structural keys and immutable payloads.
Only ordinary node records contribute rows. Empty is none; actual native
identity zero is some 0. The snapshot retains exact row order, symbols,
ordered child identities, and FULL guards.

heap_closed derives the domain List.range state.nodes.next from current Facts.
toRows_finite derives one stable finite traversal of the SAME snapshot.
language_exact and table_language identify its component language with the
independent native language from current SemanticReady, Available, DeepOrdinary.
finite combines these facts. It calls no copy or completion producer.

The language claim is local to the recursively ordinary available component.
The retained heap can contain old Mu and union records. No global native-Mu
language preservation or global Prepared premise is asserted.

The strict checker checks every public theorem by its exact namespace and
emits an explicit #check and axiom report. Own-source warnings are errors.
checked.json pins the source. Reproduce under the existing serial 4 GiB cap:

```sh
python3 lean/restart-evidence/20261112-native-ordinary-rows/check.py
```
