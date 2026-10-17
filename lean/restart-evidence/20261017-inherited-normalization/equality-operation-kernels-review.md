# Independent actual equality-operation check

The reviewed source is `SourceCurrentEqualityOperationFixed.lean`.
Its SHA256 is `92f47da8c9fce4debeb7a56983b74a73f24ad37880b54fdc1ef26b486628060e`.
The module derives FixedPayload from actual normalization and combination.
Completed memo hits use their exact existing pure-operation receipt.
Descent retains fixedness under the explicit Ready and FixedPayload premises.
The full inherited_prefix and prefix_descend producers derive fixedness from initial Ready and field availability.
They do not require fixedness of the initial inherited payload.

The constructed theorem has no caller premises.
It allocates the empty own field from the empty operation state.
It constructs physical raw classes `[[[0,0],[0,1]],[[0,1],[0,2]]]`.
These classes satisfy the existing physical Cached invariant.
The actual constructor derives Ready at live identity 1.
The theorem also proves that this input does not satisfy FixedPayload.
A two-step array receipt establishes the exact normalized merged class.
The actual full inherited prefix returns live identity 2 with `[[[0,0],[0,1],[0,2]]]`.
The actual index 0 descent returns live identity 3 with `[[[0],[1],[2]]]`.
The prefix_descend theorem derives Valid, Ready, and FixedPayload at that exact result.
The fixture supplies no future completion, output relation, or fixed result premise.

The second prefix uses the full state returned by descent.
The second prefix, repeated combination, and repeated descent each retain that exact full state.
This includes the physical equality interner and both completed operation tables.
The raw physical constructor is tested directly. The fixture does not claim that every public guard constructor can store arbitrary unsaturated raw classes.
The theorem does not prove a global active-owner order or general outer completion.

Selected integration: `equality-operation-kernels-2.source.lean` and its raw log.
It contains one check/print/axiom group and all eight explicit printer options.
Selected body-only strict check: `equality-operation-kernels-strict-1`.
Its raw log is empty. Both executions use actual 4 GiB memory.max/high and zero swap.
The selected theorem uses only propext, Classical.choice, and Quot.sound.
Attempt 1 retains the failed source and raw elaboration log.
The seven production public probes belong to the root component and are not counted again here.
