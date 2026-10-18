# Finite fresh marker choice

The new module chooses an uninterned reference above every ordinary name in a finite list. The list contains the tracked names and the actual root profiles of the supplied values. `freeBound_lt` proves absence. Ordinary references are available at every reader, so the helper needs no `Ready` premise.

`choose` computes the marker. `fresh` proves availability, tracked-name absence, and absence from each supplied actual root profile. `bodies` applies this result to both lists of resolved original body leaves. Each environment can be arbitrary. The proof does not replace actual resolved root profiles with cached `free` metadata. It also does not require availability of every environment result to compute the finite choice.

The focused integration constructs a real nested raw Mu source and derives the reader's `Ready` invariant. The selected Mu has an actual body and an actual ordinary probe. Both are available at that reader. The two outer substitutions use references 101 and 205, and the tracked list contains reference 200. The marker choice is reference 206. The integration applies `SourceCurrentStoredMuTrackedProfile.complete` with the derived freshness premise. It constructs an actual strict-body call with root profile `[206,101]`. The whole Mu call returns reference 101. The exact marker erasure law, `Keeps`, and result availability are retained.

The first integration attempt failed only because the expected root-list order and the original self-reference list index were incorrect. Its source, diagnostics, limits, and peak receipt remain present. The second attempt is selected. No resource limit was reached.

This module supplies finite input freshness. It proves no comparison between a retained writer body and an ordinary probe. It proves no general source binder fusion, observation transport, recursive outer completion, or Haskell correspondence. Later executions still need their own initial availability, replacement, and reader invariants.
