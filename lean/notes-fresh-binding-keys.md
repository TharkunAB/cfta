# Repaired substitution dependencies and physical binding keys

Updated: 2026-10-14 13:14 CEST. Proof checkpoint: `8598886f`.

## Exact used inputs

`InternedFreshOrdinaryDependencies.equivalent` derives equivalent full plans
from agreement at the original syntax's used lexical slots. The proof covers
ordered nodes, unions, and both binder forms. A binder introduces one equal
local reference and shifts the original external dependencies.

`build_congr` applies the proved repaired full-plan equality. Both ordinary
probe choices, all cache effects, successful values, and pending outcomes
are identical. `independent_replay` retains completed results after growth
when only unused lexical inputs change.

## Original free bindings

The original stored-plan slot proof applies to the repaired executor through
this derived lexical dependency theorem. Repaired `execute_congr` requires
agreement only on the original available record's free names.
`execute_restrict` derives exact restriction to those free names. It includes
arbitrary nested binders and exact cache effects. These statements previously
targeted the old constructor scheduler.

`execute_binding_replay` combines the derived restriction with repaired
completed-program replay. Equal original free bindings reuse the identical
completed result after cache growth without further allocation.

## Physical keys

For one fixed original body, `InternedFreshOrdinaryBindingKeys.key` records
the optional replacement identity at each original free name, in order.
`key_agree` derives full replacement equality from coherent available record
identity. It retains the difference between an absent replacement and a
present replacement. `execute_key` derives exact repaired computation from
that physical equality. `execute_key_replay` also permits cache growth after
the first completed result. No memo-correctness contract is supplied.

The vector uses the original body's fixed free-name order. It does not
formalize the concrete Map container or its serialized key representation.

## Finite current-cache keys

`choices` enumerates absence, empty, and the identities of actual complete
records in the current cache's issued inventory. `choices_bound` gives at
most `nodes.next + 2` entries. `choice_member` places every closed available
replacement in this finite list. A free reference cannot be closed.

`keys` takes the finite ordered Cartesian product over the original free
names. `key_member` derives membership for every environment whose present
replacements are closed and available in the current cache. Neither the
symbol type nor the guard type needs to be finite.

This list can include open record choices that the closed environment does
not use. It is a finite cover, not an exact set of closed environments.
Future cache growth can add new closed replacement records. A finite bound
on all such future values is still required for general physical closure.
Do not infer repeated cold-reader termination from the current-cache list.

## Validation

Lean 4.34.1 passes 1,370 aggregate jobs and 42,801 theorem dependency checks.
Only `propext`, `Classical.choice`, and `Quot.sound` are permitted. Log:
`/tmp/mcfta-fresh-binding-keys-20261014-audit.log`.
No Haskell source changed. Existing Nix and active-package formatter checks
remain valid.
