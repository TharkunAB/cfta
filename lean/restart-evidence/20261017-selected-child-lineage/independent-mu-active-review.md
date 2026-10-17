# Independent review of active ordinary reconstruction

Reviewed source: `SourceCurrentStoredMuActiveChildLineage.lean`.
SHA256: `951dccf930b2ec187ec09e819c33ba337af8d63fc45bb1953208b8bf7ff524ab`.
The review found no material proof or contract defect.
No production file changed. No Lean build or proof check was repeated.
The existing immutable-evidence verifier passed with 75 entries.

## Exact assumptions

`Compatible` at lines 37-40 requires equal resolved values for the two own names.
Each environment resolves a missing own name to its corresponding reference.
The maps must also agree, as Option-valued entries, on every free name of every fixed capture.
The list of captures contains the same complete values on both sides.
The maps need not agree elsewhere. The names need not be fresh or distinct.
Captured values may contain arbitrary Mu values.
This does not allow the fixed captured values themselves to differ between the two raw calls.

`Aligned` at lines 43-54 is a conditional source induction statement.
It takes Ready at one common heap, available lexical inputs, and available replacements.
Both actual raw builds and both actual reconstructed calls run warm at this common heap.
It concludes `Related` for the returned values.
It does not assume any relation between the two parent outputs.
The actual warm completion equations are observations in this conditional statement.
They are constructed, rather than assumed, by `node_complete` for the reconstruction stage.

`StrictChild` at lines 57-59 retains a source-row membership, a child membership, and strict size decrease.
It excludes unrelated smaller expressions and the enclosing node itself.
It uses membership rather than a public numeric occurrence index.
The ordinary proof constructs the strict size witness from these exact memberships.
Its child premise is a valid structural induction hypothesis, not a parent output premise.
The module does not discharge this premise for every possible child syntax.

## Base and ordinary cases

`reference` proves the active slot from the equal resolved replacements.
A fixed capture uses exact repaired-executor congruence on that capture's free names.
An absent lexical slot returns Empty on both sides.
The proof places no noDeep or closedness restriction on fixed captures.

`ordinary` at lines 381-452 derives warm raw row and child calls from the actual source calls.
The proof replays actual calls at the common heap. It does not use heap-growth antisymmetry.
The first row-survival test compares physical Empty in raw children.
This test comes from source empty semantics under the two own reference names.
It is independent of the desired reconstructed parent relation.
It ensures that the same source rows survive the first node normalization.

The proof then expands each actual stored reconstruction, including the closed shortcut.
It applies the strict child induction hypothesis to actual ordered child calls.
Those child results satisfy Related, which includes physical Empty agreement.
This supplies the second survival test for reconstructed rows.
Both directions retain exact symbols and complete guards.
Children match with All₂ in their original order.
Rows match by membership after survival and canonicalization.
The result does not promise a bijection, unchanged row indices, or row multiplicity.

`Related` contains physical root-Empty equivalence and Same at every finite depth in every fixed view.
The proof derives root Empty equivalence from ordinary output availability, Normal, and the depth-1 observation.
It does not infer physical Empty from unrestricted Same alone.
It does not prove complete Value equality, identical Mu atoms, or root-filter congruence.

## Initial reconstruction producer

`node_complete` at lines 455-508 still takes two actual past raw node builds.
Each build has its actual initial Context and growth from its returned heap to the common heap.
These are explicit provenance inputs. The theorem is not a producer for the original raw callbacks.
It derives their warm replays and availability at the common heap.
Initial Ready and Replacements construct the first stored call.
Actual Keeps from that call supplies the exact state and available inputs for the second call.
The theorem constructs both returned values, both heaps, both Keeps, and both local publication Histories.
It derives both exact warm reconstructed calls at the second returned heap.
It then applies the ordinary induction step there.
No future stored completion, returned heap, parent relation, Cap, or numerical forecast is a premise.
The two local Histories do not assert a source-started history for all records already at the common heap.

## Constructed evidence and remaining boundary

The selected fixture constructs a productive used Mu and Empty as fixed captures.
It builds two distinct ordinary parents under own references 0 and 9.
Its source includes a smaller ordinary child, ordered active/capture children, a duplicate row, and a dead row.
The fixture discharges the strict child hypothesis from reference and one smaller ordinary step.
It constructs both sequential stored calls through node_complete and proves a nonempty ordinary result.
The fixed Mu capture is closed in this fixture. Its free-name compatibility obligation is therefore vacuous.
The generic reference proof covers nonempty capture.free without that fixture restriction.

The selected six-public group prints full signatures, declarations, proofs, and axioms.
The selected one-theorem constructed group prints its signature and axioms, without a full theorem print.
The separate printer-free constructed source has an empty strict log.
This distinction agrees with the frozen component verifier and is not additional full-proof coverage.

An active nested binder is not proved Aligned here.
It may introduce paired probe names and may retain a Mu on one side while smart-erasing it on the other.
A warm selected winner may have been published by an older, different source callback.
Strict source-child induction does not select that writer or prove its reconstruction law.
The remaining general proof must connect actual chronological writer provenance to a sufficiently general binder invariant.
The module does not claim that histories returned by node_complete close this older-winner obligation.
It also does not close general union-source induction, retained-Mu reconstruction, or outer termination.
