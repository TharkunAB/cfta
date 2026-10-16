# Independent shared structural review

Reviewed on 2026-10-16 at 16:51 CEST.

Verdict: no material defect found in the frozen 185-line
`SourceCurrentAllocatedFiniteOrdinaryShared.lean`, SHA256
`bdd435bb202e4813586eee4104968a0ab7b7f55f5e03455f25a8584cd0166c91`.
This was a read-only source review. It ran no build and changed no proof source.

## Exact stored values and current state

Stored separates native returned-request certificates, completed merge-entry
certificates, and the domain of each actual target slot (lines 32–36).
initial_stored clears only slots through the actual State.initial. It keeps
the supplied complete checked state and merge memo. It does not infer warm
structural facts from semantic readiness.

advance_stored keeps slots and merge entries and requires the new native
certificate. advance_heap_stored uses the literal constructor-only advance,
whose native cells are unchanged. These heap-independent structural lemmas
make no availability or physical-readiness claim for arbitrary heap changes.
store_stored uses the exact new path/value and preserves other slots.

The force hit uses stored.slots at the actual lookup result and keeps the
identical state (lines 97–98). The miss uses the actual Target graph from the
Force constructor (lines 99–104). Target.target derives the result domain and
new native/merge certificates at those exact endpoints before store_stored
installs the value. No independently chosen target result is substituted.

## Actual leaf and height orientation

leaf_structure decomposes the actual Leaf.apply into its Force and Step.
It verifies Step.run's exact physical trace under the readiness of the same
forced return (lines 140–149). The request is literally emptyDomain with
ordered operands target then input. It extracts the SECOND operand bound
checked.2.2.2. NodeNarrow input result is defined as domain(result) and
height(result)≤height(input), so this orientation is correct even when the
target is taller than the current input. The returned shared state is the
literal advance of the forced state with the Step's complete checked return.
Slots and the warm merge memo are retained through that native request.

Public leaf verifies the same supplied actual Leaf. Its existing receipt and
structural proof share the identical input/result/before/after parameters.
Input closedness is derived from initial coherent availability and input
domain. It is not a public output-law or closedness premise (lines 152–166).

## Constructed endpoints and assumptions

force_finite calls the existing physical complete endpoint, then proves
structure for its actual Force graph. leaf_finite similarly proves structure
for receipt.actual from the one constructed Leaf (lines 119–131, 168–183).
The receipts expose actual graphs; neither endpoint assumes successful future
execution, a future Ready state, a target-domain callback, or a native result
law. Recomputing logical verification receipts does not replay host effects.

Initial class Ready, At, captured source availability, coherent/nontrivial
class membership, global validity, structural warm tables, and reached range
plans remain explicit. selected_domains derives all required path domains from
the actual captured heap growth and the finite ordinary forest. The proofs do
not close unselected siblings by assumption, but this new domain itself admits
only finite ordinary recursive structure. Arbitrary/full guards and nonempty
equality classes remain permitted.

These endpoints establish current shared Force/Leaf domain preservation and
finite construction under the existing range and admission contracts. They do
not yet establish structural preservation for all edits, class passes, parent
rebuilds, or general constrained outer recursion. GHC demand order and host
map/runtime correspondence remain separate. No Haskell defect was found.

The old PlainRegion admits Mu and explicit union as opaque terminal cases.
The new finite ordinary domain excludes those constructors recursively. This
review does not transfer the latter exclusion to the old plain theorem.
