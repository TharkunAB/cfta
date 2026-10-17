# Actual inherited descent and source normalization

The owned module is `SourceCurrentEqualityDescendFixed.lean`.
It uses the literal `SourceEqualityDescend.records` and `descend` functions.
It does not replace trie descent with a list operation.

The initial premise is actual source normalization fixedness of the stored class paths.
`SourceCurrentEqualityNormalizationFixed.normalize_idempotent` derives this premise from successful initial normalization.
Physical `WellFormed` supplies coherent ascending tries and nontrivial classes.
Physical `Ready` alone does not imply normalization fixedness.

The proof lifts each generated child suffix congruence to a generated parent suffix congruence.
Parent fixedness places that congruence inside one parent component.
Two distinct extended child paths force the component's actual descended trie to survive the source two-path test.
Thus every generated child class lies inside an existing child component.
The proof also derives child activity, canonical path sets, disjointness, and absence of strict-prefix contradictions.
Actual source-sort orderedness then identifies completion with the literal child list.
One executable fixed congruence step gives exact actual normalization fixedness.

The source adapter matches `cfta/src/Data/CFTA/Equality/Constraint.hs` lines 467–486.
It retains the empty and contradictory branches, the actual trie descent, the two-path filter, and path-set sorting.
The separate source-sort theorem proves ordering for the actual sorter.
Permutation alone is not used as an ordering theorem.

The integrations construct normalization results with small completed reference receipts.
The receipt identifies the actual source normalizer without evaluating its conservative sufficient fuel.
The first integration reads actual physical records and descends to classes in a different list order.
The second integration retains a source-generated suffix congruence through descent and then reaches an empty child payload.

This result permits repeated plain-prefix descent to retain normalization fixedness.
It does not prove that a parent has an empty own field.
It does not show that combination with nonempty local classes preserves a strict origin rank.
It does not exclude every active ancestor key or prove general outer completion.
No Haskell change or Haskell defect is claimed.

Final validation uses strict source attempt 4, full public attempt 1, integration attempt 1, and printer-free integration attempt 1.
The final canonical attempt 2 follows the source-sort dependency correction.
Its only warning is the inherited `InternedFreshOrdinaryClosedCompletion` unused-input warning.
Canonical attempt 1 retains the earlier source-sort unused-simp warning.
All earlier partial and failed attempts remain in this component and are not selected as final checks.
