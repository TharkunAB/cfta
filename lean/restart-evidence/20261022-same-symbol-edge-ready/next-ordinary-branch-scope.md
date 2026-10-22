# Actual ordinary branch scope

Updated: 2026-10-22 02:41 CEST. Source review only.

Root read cfta/src/Data/CFTA/Interned/Operations.hs, lines 745 to 768.
withoutRedundantEdges uses mapNodesStep before dropReds.
The ordinary Node branch calls dropRedundantEdges only when freeVars is empty.
The proposed direct-row completion theorem requires parent.free = [].
That requirement corresponds to this actual branch guard.
The formal correspondence from the guard to this parent fact is not added here.

The recursive Mu branch separately compares the edges of its unfolding.
It then retains the body alternatives whose unfolded edges remain.
This branch needs its own physical unfolding and kept-body correspondence.
A closed Mu does not by itself prove that its stored body parent is closed.
The proposed original-parent theorem does not replace that obligation.
No new theorem, Haskell change or runtime result is claimed by this note.
