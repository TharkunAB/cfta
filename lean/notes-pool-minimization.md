# Pool minimization changes the distribution

The public `minimizePoolOn` documentation promises to retain the most
specific entries of each similarity class. It explicitly directs callers
to `pool` or `namedPool` when they need every entry. This is a representative
selection operation. It does not satisfy the full-language preservation
contract required of an optimization before distinct-term enumeration.

After the core minimizer returns, the function reads its retained symbols.
It filters the original entries in their original order and calls
`namedPool` again. That pool is uniform over the retained entry occurrences.
Removed occurrences contribute no probability mass to a representative.

`PoolMinimization.retained_member` proves the exact filter contract.
`distribution_event` derives the resulting event probabilities.
`retained_condition` identifies the result as conditioning the original
unit occurrence masses on retention. `representative_event` separately
derives the probabilities when all original members map to representatives.
The latter operation adds the original masses within each class.

A public three-entry reproduction uses values zero, one, and two, each
with the valid refinement Top. Zero and one share a similarity class.
The earlier equivalent entry zero stays; one is removed. The minimized
pool gives zero and two probability one half each. Mapping the original
uniform pool to the same representatives gives probabilities two thirds
and one third. The kernel-checked `class_mass_changes` theorem proves
this distinction. `removed_member` also records the changed term set.

This is an explicit API contract boundary, not an additional implementation
defect. No source behavior is changed. A caller that needs original class
probabilities must retain and aggregate those masses separately. The
current function has no option that promises that transport.

The proof starts after successful minimization with its retained-symbol
predicate. It does not prove which representatives the complete minimizer
will choose. That source schedule has its own model. The public
`repro/MinimizedPoolDistribution.hs` checks the concrete example with the
lattice solver. The pinned Lean build checks the distribution laws.
