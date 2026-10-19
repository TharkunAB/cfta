# Supported observation below a two-row ordinary prefix

This component has one constructed theorem, `MicroCFTA.RecursiveEntryObservationKernels.ordinary_prefix`, and no production declarations. The public statement is identical to the private checked witness statement. The public proof forwards the checked witness.

The source has two ordinary rows. The first row has a finite leaf child. The second row has the plain used Mu `mu x. rec[x]` as its child. The source builds from an empty heap. The concrete root fields are extracted from that actual build. A literal successful build equation checks that the represented ordinary root is exactly the returned source value. The fixture derives SemanticReady, Available, costs and the causal plain guard heap from this source execution.

The literal Project worker follows path `[0]`. It scans both source rows in order. It projects the finite child and Mu with empty remaining paths, then reads both operands and constructs their ordinary union. The terminal actual Read returns exactly two rows. The second row is selected at outer index 1.

The explicit ProjectionFrame belongs to that exact projection and terminal read. Its source index is 1 and operand index is 1. Its selected Mu operand Read has index 0 and returns the same complete selected row. The frame retains the actual prefix, child call, suffix and all complete reader heaps. The resulting Entry is an ordinary prefix followed by a recursive root entry. Thus the example checks different outer and inner row indices. It does not assert a canonical reordering or an injective source map.

The fixture invokes `SourceCurrentRecursiveEntryObservation.entry` on this exact Entry. Actual projection effects derive the final reader semantics, costs and guard heap. Keeps is reflexive at the actual projection return. The theorem returns its supported Observation, the exact path split and the two surrounding Keeps intervals. The explicit frame checks internal index 0. The produced Observation remains the theorem's existential value; the fixture does not additionally assert that this existential value has position 0.

The fixture assumes no desired observation, annotation or semantic output equation. It has no primary-gate premise and makes no false-gate claim. It does not assert a whole event Project, a class fold, source-row observational coercion, general reader transport, language equality, finite productivity, termination or Haskell correspondence. The used Mu and two actual nonempty reader rows make the endpoint nonvacuous.

Selected evidence is `reader-kernels-direct-2`, whose log has literally zero bytes, and `reader-kernels-public-1`, with one full type/proof/axiom pair. All eight printer/linter settings are present. The full log has 97006 bytes, no omissions and only standard axioms. The source contains the full private witness proof.

All three owned jobs are retained. Strict attempt 1 failed root-type elaboration at the ordinary ProjectionFrame and reported proposition definitions that required theorem declarations. Attempt 2 represents the exact source-equal ordinary root explicitly and checks all frame fields and theorem declarations. The first public probe completes the full checks. Attempt 1 is unselected.

Every job runs under the 4 GiB / 5 minute cap and records memory.max = memory.high = 4294967296 and memory.swap.max = 0. The reused production canonical receipt terminates successfully and replays only the pre-existing `InternedFreshOrdinaryClosedCompletion.lean:24:5` warning. The selected fixture strict and public outputs have no warning. No production pair or canonical job is counted as owned.

The explicit immutable manifest pins the final production source, proof dependencies, all owned attempts and a dedicated three-row peaks snapshot. It excludes mutable peaks, shared runners and selections, current root packaging files and all earlier frozen fixture components. No old source or evidence file is changed.
