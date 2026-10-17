# Open observation root-list algebra

The source adds two pure theorems. append combines two Same relations at
one finite depth and one view. of_members removes root-list order and
multiplicity. Both preserve bare references, full row symbols and guards,
and ordered child relations. Neither theorem requires a heap invariant.

The proofs use reference_seeds and origin_seeds. Append selects the same
side on each source list. Equal membership retains the exact row and
reference origins. No Mu execution or source completion is assumed.

The imported public probe prints both complete proofs and axioms. The pure
integration composes literal union expansion with duplicate removal and
root reordering. The integration permits arbitrary roots and view heaps.
It does not claim that unrelated Mu bodies satisfy Same.

Strict attempt 1 has an empty log. The single canonical target passes 546
jobs. Public attempt 1 and integration attempt 2 have no diagnostics and
use only standard axioms. Integration attempt 1 failed because the imported
Lean environment has no tauto tactic. Its source and raw log are retained.
All selected jobs verify memory.max and memory.high at 4294967296 bytes
and memory.swap.max at zero. No earlier source or evidence file changes.
