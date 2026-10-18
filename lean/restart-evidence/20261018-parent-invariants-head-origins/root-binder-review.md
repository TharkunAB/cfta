# Independent review of the root-alternative relation

Reviewed at 2026-10-18 02:15 CEST.
SourceCurrentUsedBinderRootAlternatives source SHA256:
47d9c3eace5b6cc328ff293db218cf13a85f5c23ae2bd1418c37cc568586b27b.

No material proof defect is found by source inspection. RootMatch compares
immediate literal alternatives and complete ordinary rows in both directions.
It permits union permutation and duplicate removal. RowMatch retains the
complete symbol, guard, and ordered child relation. AtomMatch keeps Mu atoms
distinct from ordinary roots and literal references. The supplied value
relation applies only to paired Mu atoms and row children. The supplied
reference relation is explicit.

The union producers use initial normality, availability, and input-member
relations. Their proofs derive result occurrences through actual makeUnion.
The filter producers derive the literal root alternatives of actual
withoutSelfReference. The explicit own-reference compatibility condition
separates own from captured references. The non-erased filter also needs
agreement of the bare-self input cases. No desired output RootMatch is a
premise. These theorems provide a compositional relation. They do not produce
that relation for arbitrary nested source binders or retained warm writers.

The relation does not state language equivalence by itself. The next source
induction must derive the Mu-atom and child relations at the same actual
heaps. Actual callback bare parity is a separate prior theorem. The alias
boundary example is not evidence of a Haskell defect in actual fresh
publication. All-ancestor key exclusion and recursive progress remain open.
