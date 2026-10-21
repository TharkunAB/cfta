# One-rank equality through the public definition

The target equality uses the header's exact local `images`, `slotStep`, and `rowStep` expressions:
`envelope budget count mass seed = (1 + completed.1, completed.2.1, rebuild completed.2.2)`,
where `completed = (List.range mass).foldl rowStep (0,0,seed)`.
This equation is a proof target, not a supplied recurrence or a second definition of C.

1. Unfold only the root occurrence of PUBLIC `envelope`. Apply core `WellFounded.fix_eq` to that occurrence.
2. Preserve the actual fixed-point step as the expression obtained by unfolding. Do not refer to a guessed friendly private name.
3. Identify the recursive functions by function extensionality. Case-split the rank pair so `child` and `(child.1,child.2)` coincide. The smaller-rank proof is ignored after `fix_eq`; proof irrelevance identifies alternative proofs.
4. Expand only the finite wrappers definitionally into the explicit attached-list expression. A typed `change` may expose this expression without naming private constants. This is finite delta reduction, not unfolding recursive C calls.
5. At each current seed, apply `List.attach_map_val` to replace the attached map by the ordinary map of PUBLIC envelope values. Its exact installed signature is `(l.attach.map fun (i : {i // i∈l}) => f i) = l.map f`.
6. Lift that image equality through the slot function, then the fixed-length slot fold, row function, and fixed-length row fold by congruence. Parent and rebuild are the SAME expressions on both sides.

The proof may use a local congruence statement about arbitrary recursive functions to isolate step 3. Such a statement has no assumed recurrence or output property.
For matching a row, first generalize the actual Parent expression with its genuine equality before exposing its mass/range. This avoids normalizing the large forecast under a `change`, as the checked envelope's strict history demonstrates.
No generated private constant identifier is part of the proposed source contract.
This route is source-grounded but unelaborated. If transparent reduction cannot expose the attached expression within the budget, report that access obstruction before proposing any API change.
