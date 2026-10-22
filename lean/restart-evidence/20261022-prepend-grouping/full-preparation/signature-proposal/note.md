# Prepend grouping declaration proposal
Status: FINAL/FROZEN SOURCE-ONLY DECLARATION PROPOSAL. No new theorem is checked.
The selected slice has three public definitions and six public theorems. There are no private helpers. Its only induction generalizes the initial optional table.
The literal clusterByHash expression uses singleton pairs, fromListWith (++), elems, and map reverse. The modeled insertWith uses new ++ old; the old MergeGrouping insertWith uses old ++ new.
Bucket reversal conjugates the two singleton schedules. The raw prepend table is not identified with the append table before reversal.
The iterator transport retains every literal key and its emitted position while reversing each bucket. It preserves absent keys, present empty buckets, repeated rows and all prior table entries.
The final permutation uses the existing Iteration.permutation. No HashMap iteration order, storage refinement, Eq/Hashable law or actual Haskell execution is assumed proved.
Key is generic in this slice. A later consumer must instantiate it with edge.entry.key.symbol only. The existing symbol-and-arity groupKey and specialized merge_grouping are not used here.
No stateful group traversal, H20 application, heap equality across bucket orders, Mu reconstruction or whole public pass is claimed. H6 remains the strongest combined trace theorem.
Root reports the H21 fresh pull and baseline complete at local H20 checkpoint d0cf685f461430a7c608ceb3b76da0fe568e4d84. Earlier H20 inventory status is retained verbatim as historical evidence.
I read all190 existing MergeGrouping lines and the cited Haskell/Lean/core ranges. I authored H20 mathematics and its tool audit, not the existing grouping APIs or the H20 grouping inventory.
Only source/metadata reads and external package writes were used. No compiler, prepared tool, Git, network or repository write ran. Newer local commits still require fresh push approval.
