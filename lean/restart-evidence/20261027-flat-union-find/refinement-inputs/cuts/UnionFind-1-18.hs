{- | Lightweight union-find implementation suitable for nondeterministic search.

Mutable union-find, as in @Data.Equivalence.Monad@, can be faster overall,
but enumeration branches in the list monad need a structure that can be copied
and backtracked cheaply. This module stores parent pointers in an 'IntMap' and
returns updated structures from 'union'. It is the linked-list
representation of disjoint sets with the weighted-union heuristic (Cormen et
al., Introduction to Algorithms): the representative of a set holds the size
and the members of the set, and a union points each member of the smaller
set at the representative of the larger set. So the parent of a variable is
always its representative, 'root' takes one lookup, and n unions point
O(n log n) members in all.

In a constrained enumeration of 20,000 terms of the typed-expression ECTA,
'find' takes 1.7% of the instructions, and all operations of @containers@
together take 5.5%. So a mutable union-find with an undo log could save at
most about 7%, which does not pay for the backtracking that it needs.
-}
