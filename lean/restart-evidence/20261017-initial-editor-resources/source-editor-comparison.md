# Current Haskell editor comparison

Source main is c0cc8a05. All starting Haskell bytes remain unchanged.

cfta/src/Data/CFTA/Equality/Operations.hs lines 317 to 334 compile edit pairs with a right fold.
An empty path replaces the previous trie. A deeper insertion under a
leaf retains that leaf. A child-list root leaf returns its input unchanged.
Node leaves call the selected callback before node inspection. Empty
nodes stay empty. Recursive nodes expose nodeEdges before the same trie
resumes. Ordinary rows retain their original edge and edit its children.
An entered recursion reference raises the explicit unexpected-Rec error.

cfta/src/Data/CFTA/Interned/Type.hs lines 395 to 400 use raw internEdge when setChildren
retains the original arity. The actual modeled child graph proves equal
length. Its raw makeEdge request therefore retains the same full guard.
The other setChildren branch uses mkEdge and remains a separate contract.

cfta/src/Data/CFTA/Internal/Tree.hs lines 263 to 268 define adjustAt. A negative index or an
index outside the original list leaves the list unchanged. The child
edit therefore makes no callback for those indexes.

These source branches match the retained handwritten edit model. The
initial producers construct the modeled serial execution. IntMap folding,
lazy callback demand, hash-consing, and memo publication still need the
separate Haskell runtime correspondence. This inspection does not prove
those runtime laws. No Haskell patch or new behavior defect is added.
Root FINDINGS retains all earlier repair handoff entries.
