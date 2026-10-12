# Source structural order

`StructuralOrder` compares finite constructor trees. Constructor tags precede
their fields. Field lists use lexicographic comparison. Finite comparison
approximations inherit the standard sum, product, and list order laws.
`fuel_exact` proves that sufficient depth gives the complete comparison.
This derives transitivity without assuming it for recursive fields.

`FormulaStructuralOrder` encodes every current sort, term, and formula.
`formula_exact` proves that key comparison is exactly `FormulaOrder`'s source
comparison. Function signatures, application arguments, conditionals, casts,
and quantified binder lists retain their field order and repetitions.

`GuardStructuralOrder` encodes every guard and substitution constructor in
Haskell declaration order. `guard_exact` proves comparison correspondence.
`guard_eq` proves that comparison returns equality exactly for identical
guards. Paths use the existing model's nonnegative child indexes. Haskell
machine index conversion remains a representation boundary.

`le_trans`, `le_total`, and `le_antisymm` discharge the order-law premises of
canonical conjunction. `normalize_idempotent` and `merge_absorbs` use this
actual source comparison. They do not assume that an unspecified comparator
is lawful. These are syntactic results; the separate current-entry proof
establishes all-verdict semantic preservation.

The source uses `Set`, while the model uses sorted duplicate-free lists.
Set implementation and host comparison correspondence remain runtime
boundaries. The comparator algorithms and their order laws are kernel checked.
