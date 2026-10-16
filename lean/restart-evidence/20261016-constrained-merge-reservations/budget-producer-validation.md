# Actual recursive Merge constructor budgets

Validated at 2026-10-16 20:24 CEST with pinned Lean 4.34.1.

The three public endpoints are `run_budget`, `call_budget`, and `cold`. The actual Run/Call graph fixes the same output, constructor heap, and merge memo as the profile producer. The proof returns physical effects, physical stored entries, profile stored entries, and the stronger request contract. The resource part of that contract gives an actual constructor Work trace with input-only node and edge request limits.

`call_budget` takes the actual completed Call, initial semantic and cost heap facts, initial physical and profile table invariants, and input availability. It has no initial finite-ordinary premise, resource table invariant, future callback, result law, or count premise. Its universal resource certificate applies when the caller supplies a supported original profile and height bound. `cold` derives both initial invariants for the literal empty merge table.

The Run proof follows the actual mutual recursor. At each hit or miss it reuses the already proved, independent profile producer on that exact Call. This supplies the physical effects, both stored invariants, and the complete profile contract. A warm hit supplies a reflexive zero-Work budget. A miss applies the smaller actual body Run induction hypothesis to the local budget body certificate for arbitrary original row, arity, and height limits. Numeric height monotonicity widens the bound. The resulting budget connects the actual initial and body-return heaps. It therefore retains body Work even if completion keeps an earlier winner.

The first standalone direct check passed, but canonical build 1 exposed a decision-instance inference mismatch in the mutual Call motive. The budget contains a Trace indexed by its edge-key equality instance. The final proof names that instance and pins the exact same instance in the Call motive. `budget-producer-direct-2.log` passes with the actual canonical setup JSON and both unused-variable linters enabled. `budget-producer-pre-instance-fix.lean` preserves the superseded source; it is not the final proof.

Canonical build 2 successfully builds this Producer at job 1326/1328. That aggregate then reports independent errors in the separate root-owned Finite and Operand modules. The Producer target itself passes with no new warnings. The historical `InternedFreshOrdinaryClosedCompletion.inputs` dependency warning is unchanged.

All three public full-signature/axiom pairs pass in `budget-producer-public-1.log`. Three substantive integration pairs pass in `budget-producer-kernels-2.log`:

- A cold actual Call yields its request trace, both returned table invariants, and input-only upper bounds for both final constructor supplies.
- A constructed warm hit returns the exact stored result and unchanged heap/memo. Its explicit trace is empty and both reservation counts are zero.
- An actual body with an earlier winner retains that winner while deriving its complete before-to-after Work trace. Exact counter equations include every reservation in the trace; completion does not refund them.

Kernel attempt 1 failed because one probe used a namespace as a predicate. The final probe uses `Profiles.Stored`. The failed log remains. The final public and kernel logs have no errors, warnings, or `sorryAx`. The source and current probes have one terminal newline and no trailing whitespace.

The budgets bound constructor node and edge requests, then their reservation counts. They do not bound equality allocations, native query requests, instructions, host evaluations, or total runtime. The proof retains the existing completed-serial Merge scope. It does not establish pending-publication or GHC forcing-order correspondence. The root owns the independently constructed finite, full-caller, and Projection-to-Merge wrappers.

This component changes only the new Producer source and its new evidence. It does not edit older proofs, Haskell, Audit, restart authorities, Git state, or older evidence.
