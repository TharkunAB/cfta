# Exact unproved grouping bridge
Let P_x update a matching optional bucket with Some([x] ++ old.getD []), and let A_x be the existing singleton `insertWith` update with Some(old.getD [] ++ [x]).
Let R act pointwise on optional buckets by Option.map List.reverse. It fixes None and sends Some bucket to Some bucket.reverse.
Required one-step law: R(P_x table) = A_x(R table). The singleton input is essential to this literal equation.
Required empty-fold law: R(prependFold key rows) = SourceCurrentMergeGrouping.fromRows key rows.
For an arbitrary initial table, the fold generalization starts the append fold at R(initialTable); it does not discard prior buckets.
Required iterator law: an Iteration of prependFold at entries transports to an Iteration of fromRows at entries.map (key, bucket.reverse).
The final Haskell list of reversed buckets then permutes Sized.groups key rows by existing Iteration.permutation.
No equality of raw prependFold and fromRows is claimed. No key order is fixed.
A HashMap boundary still must connect actual fromListWith (++) and elems to this optional lookup/insertion/finite-iteration model.
No HashMap source, library law or Haskell-to-Lean implementation refinement was checked or assumed by this inventory.
These are mathematical route statements only. No Lean header, declaration, body or check was created.
