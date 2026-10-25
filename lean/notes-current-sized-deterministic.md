# Deterministic Sized dispatch

## Current result

Main `153e1a211b56dd78bd22f6b427fb78e673041d55` is imported by
`8ba84f0bd0150c85c295ca854172cfcf770562ca`.
The gate proof is `cb59a931b06e54bf217fca7cd86f4d8a2cacb998`.
The dispatcher integration is `01882288bb037712665f5d134b3005d2cc717da3`.
The Haskell documentation repair is `af6369a9e0ecd70acf4da1dffec45c32e6ce7b7b`.
The whole formalization goal stays ACTIVE.

Main adds a bottom-up deterministic shortcut to `Data.CFTA.Sized.sized`.
The plain-constraint scan still checks every original annotation.
The optimized branch then accepts either the new key check or the existing
product-minimum check. Failed gates still use the reference implementation.
The sorted rows, count table and four query implementations stay unchanged.
The other imported changes document the Specftacular comparison.
No performance matrix is run or formalized here.

## Key proof

`SourceSizedDeterministic.ownedRows` retains every transition occurrence and
its owner state. `rowKey` retains its symbol and complete ordered child list.
`bottomUpDeterministic` compares the total key count with the distinct count.
The list `eraseDups` operation supplies the mathematical set cardinality.
The proof starts from this executable Boolean check.
It does not assume semantic determinism or unambiguity.

`gate_keys` derives global key `Nodup`.
`accepted_state_unique` uses finite-term induction to derive state uniqueness.
The list induction relates the two ordered child-state lists.
Global key uniqueness then identifies the owner states.
`gate_disjoint` separates every pair of row occurrences at each owner state.
`gate_unique` derives distinct terms in every exact size class on plain rows.

The finite state list must contain every owner of a stored row.
The raw finite-map adapter supplies this fact with `sorted_supported`.
The state type itself can be infinite.
No acyclicity, productivity or nonempty-language premise is required.
Repeated occurrences stay in the key list before duplicate removal.
Even identical duplicate rows therefore fail the shortcut.
Dead or unreachable rows can make the check conservative.
Guard checks can only restrict the accepted-state uniqueness theorem.
The enumeration and optimized-query theorems still require plain rows.

## Dispatcher integration

`SourceSizedDispatcher.sized`, `SourceSizedPreprocessing.publicSized` and
`SourceSizedFiniteKeysDispatch.nativeSized` now contain the new disjunction.
Each branch retains the original no-constraint condition.
`optimizedApi_eq_deterministic` identifies the complete optimized record
with the reference record after a passing key check.
The raw adapter uses original finite map keys and original canonical rows.
It does not pass through a trimmed interned constructor.

`nativeSized_eq` identifies all four returned query functions and errors
with the public finite-carrier adapter.
The proof uses the exact reference sequence in both representations.
It does not assert equality of the two Boolean gates across representations.
It does not assert identical short-circuit execution or cost.
The physical `Data.Set` implementation and Haskell `Ord` laws stay outside
the list-cardinality model.

The finite rank theorem now accepts the actual composite optimized gate.
It retains the explicit finite count derivation and rank-map readback.
Both signed rank/selection inverse laws remain.
Existing guarded-language exactness retains its `ActiveOption` premise.

## Haskell documentation repair

Upstream describes the ordered-set check as linear in the transitions.
`Data.Set.fromList` does not establish that bound for arbitrary ordered keys.
The focused repair removes this claim from the module comment, helper
comment and changelog. It states that the check builds a set of keys.
No Haskell executable expression changes in this repair.
Root `FINDINGS.md` records the commit for external work on main.

## Verification

All five changed Lean modules pass with Lean 4.34.1, all linters and
warnings as errors. The first core attempt has list-witness and equality
proof errors. The first raw API attempt has reference-transport errors.
The first dispatcher and preprocessing attempts expose existing missing
field documentation. The first rank attempt exposes an existing `omit`
directive. The final sources fix these issues without disabling linters.
All ten strict inputs and full logs remain in the evidence.

Installed builds pass. Public readback covers fifteen declarations.
The full readback has 12413 bytes and SHA-256
`04b581330e62ae443c58fe41e4b1a539be18eb14c550069fd2b338448766997f`.
Every axiom set is a subset of `propext`, `Classical.choice` and `Quot.sound`.
The executable key gate uses no axioms.
The aggregate Audit passes with 3737 jobs and 76607 theorem dependencies.
The older unused `inputs` warning remains unchanged.

The existing native Sized suite passes: 11 examples, zero failures.
Four properties each pass 300 cases with seed 20261025.
The build compiles the current merged `Data.CFTA.Sized` source.
The cases include cyclic deterministic rows, large ranks, dead and repeated
rows, overlap fallback, equality constraints and residual-guard rejection.
Exact reference comparisons run through size six.
Fourmolu and cabal-gild checks pass inside `nix-shell`.
The native test precedes the documentation-only repair.
No repeated runtime test is needed for that comment change.

Checks run serially with the heavy-management cap.
Lean and formatting use 4 GiB. Native Haskell uses 8 GiB.
Each cap disables swap. Commands, source snapshots, raw logs, reports and
peak records are retained in `restart-evidence/20261025-sized-deterministic`.
Source review finds no semantic defect in the gate or its integration.

## Strongest claim and next work

H6, `SourceCurrentColdFiniteWarmCalls.constructed_node_calls`, remains the
strongest end-to-end result. Its source is unchanged.
For the covered closed construction, valid initial constraint cache and
original allocation history, every prescribed finite budget and number
of rounds has sufficient finite fuels and one mathematical width chosen
after construction. The modeled node-call trace completes. Its final
available value has exactly the original finite-tree language for every
ambient guard and term under the formal formula and entailment model.

The new Sized result extends a component guarantee to the new upstream gate.
It does not complete native enumeration or arbitrary Haskell correspondence.
The next target remains admitted ordered child traversal.
Compose genuine child completion with heap, root and waiting transport.
Keep the existing conditional numeric admission limits explicit.
Then connect the edge residual and original captured-slot final write.
Full typing/pruning, concrete solver correspondence, physical maps and
machine integers, extraction, practical bounds and convergence remain open.
