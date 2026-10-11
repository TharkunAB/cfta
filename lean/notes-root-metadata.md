# Root-count metadata

`RootMetadata` follows `Static.termRootCount`, `addRootCounts`, and
`commonRootCount`. A private placeholder leaf contributes one root. This is
the root that integer closure will fill. A user label contributes one root.
Other private nodes contribute the sum of their children.

`roots_exact` proves that the count equals the length of the eventual user
forest, with an explicit unfilled leaf in place of each placeholder.
`common_sound`, `enumerated_sound`, `add_sound`, and `label_sound` prove the
metadata claims for choices, enumerated imports, products, and closed nodes.
Unknown metadata makes no false count claim. The empty-choice count of one is
sound because the choice has no members. `join_roots` proves that binary join
keys add no user roots.

`known_one_singleton` gives exactly one eventual tree for a position with
sound root count one. `aligned_spine_roots` gives one root per admitted
argument position. These results connect the compiler's shape checks to the
term callbacks. They do not certify an arbitrary externally supplied metadata
record. Haskell stores these counts in `Int`; representation correspondence
requires that the finite counts fit that type.
