# Existing APIs used

- CachedOwn.prepare_scalars derives the same suspendedState endpoint from the literal singleton receipt.
- CachedOwn.prepare_inputs derives the actual staged list and preserves ordered inherited and own descents.
- EnumerationDriver.suspension_protected retains any original allocated root and its value/class.
- EnumerationDependencies.suspension_origin rules out newly expanded slots.
- EnumerationReferences.suspension_allowed retains original reference predicates through fresh allocations.
- EnumerationCorrectness.fresh_avoids and descend_avoids establish every actual child bucket's avoidance.

The already-existing PreparedSharedChildIsolation.prepared_stored_child_inputs proves a related selected-child receipt. It requires an actual selected child position, so it alone does not handle an empty staged list. The new proof reuses the same public scalar and shape APIs directly and returns the complete all-staged history receipt required by the current structural induction. No worker engine or cache framework is copied.

A read-only import-closure scan confirmed OwnInputShape, EdgeScalarBounds, and EdgeInputs are normal transitive imports of the existing resource owner. PreparedSharedChildIsolation itself is not required by the candidate.
