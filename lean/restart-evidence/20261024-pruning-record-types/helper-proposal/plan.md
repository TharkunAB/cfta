# Pure pruning position helpers

Status: SOURCE_ONLY_UNCOMPILED_PROPOSAL.
The candidate uses namespace MicroCFTA.SourcePruningPositions.
It imports SourcePruningTemplates and EnumerationBuilderCaches.
The three requested interfaces are literal definitions, not callback parameters.
Symbol is the existing complete label/refinement alias from SourcePruningTemplates.
Only ordinary Top app/4 and filter/2 labels select program children.
Type-position insertion uses existing canonicalIds on raw Nat IDs.
Type-position child processing retains the exact native nested foldr expressions.
Program holes preserve raw IDs, function/argument order and duplicate occurrences.
openProgram preserves every concrete label and child order.
It emits ordinary ?, ?program# plus decimal raw Nat, and Mu markers.
Focused equations expose type/program branches, application/filter order and marker output.
Membership, sorting and duplicate theorems add explicit observable list contracts.
No state action, representative lookup, graph read, callback or new oracle is introduced.
Native signed Int values need a nonnegative, in-range extraction relation to Nat.
Native Int decimal show/Text conversion remains an explicit formatting boundary.
A native IntSet input must be represented by its ascending unique list view.
The optional global typePositions_canonical theorem remains future work.
Theorems for paired callback observations must not require that future theorem.
Root owns first compilation, required elaboration repairs and repository integration.
No compiler, prepared program or repository mutation was run by the proposal author.
