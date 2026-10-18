# Tracked union fusion review

Production: `SourceCurrentTrackedFilteredUnionFusion.lean`.
Source SHA256: `3f86db1696f31084e7fb88e45698228db09feb980fec40d915b862f449827a35`.

The public `union` theorem derives the tracked fusion law from the laws for the actual immediate source members at the same original depth bound. It derives each original member bound from the actual historical `buildMany` and `makeUnion` calls. This includes duplicates and Empty members. It places no depth bound on replacement values or reconstructed results.

Two actual finite member preparations produce a common later Ready reader. The proof replays the original parent calls and the earlier member calls there. The lexical relation does not depend on the execution heap. The source contexts, raw return growth, reader availability, replacements, live aliases, and self tests remain explicit.

The private profile criteria apply to Normal available roots. A masked root is nonopaque exactly when it has no literal ordinary row and every literal atom is a tracked reference. Under that condition, each masked name is exactly a literal reference part. Normal.proper supplies a row for each ordinary node. The proof handles arbitrary root unions recursively and keeps Mu atoms opaque.

`FilteredUnionCoverage.parts` gives the exact retained member alternatives of both reconstructed parents. It derives parent opacity and tracked name sets from those actual member outputs. Retention keeps the bare-self exception: a bare self member survives only when the full raw parent is bare self. The proof derives corresponding retention on both sides from actual source self tests. It assumes no parent output relation.

The source-built fixture uses two distinct raw unions with duplicate subgroup and Empty source members. Both raw depths are zero. The excluded bare-self reconstruction is a nonempty used Mu with a used nested Mu child. Retained member reconstructions collapse to reference marker 90. The tracked observation is `some [marker90]`; the empty tracking list makes that same nonempty result opaque. The actual warm parent coexists with an initially cold proper subgroup filter.

Validation selects strict `tracked-union-direct-8`, canonical `tracked-union-canonical-2`, full public `tracked-union-public-1`, strict fixture `tracked-union-kernels-2`, and full constructed `tracked-union-kernels-public-1`. Both strict logs have zero bytes. Each full probe prints its explicit signature, complete proof, and axioms under all eight print options. Only propext, Classical.choice, and Quot.sound are allowed. Every selected Lean job uses the pinned 4.34.1 toolchain, memory.max=memory.high=4 GiB, memory.swap.max=0, and the five-minute wrapper.

Direct attempts 1 through 7 retain incomplete helper/proof attempts. Fixture attempt 1 retains the missing explicit reflexive profile proofs. Canonical attempt 1 succeeded but replayed warnings from then-current root dependencies. Canonical attempt 2 uses the final warning-free dependency bytes. These prior attempts remain unselected and unchanged.

This proves a conditional union constructor step. It does not prove the source binder case, a physical output grouping equality, language nonemptiness, general observation equivalence, or general traversal completion.
