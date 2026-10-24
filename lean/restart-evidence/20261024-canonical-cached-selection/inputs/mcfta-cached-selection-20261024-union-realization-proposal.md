# Actual terminal-union root-map realization

Source-only proposal, 2026-10-24 01:47 CEST. No compiler or repository write. The current HEAD is `a0c955144d91fe1a3ee759c864c7ecd0a9dcda77`; the source identities below are unchanged from the inspected definitions.

The smallest route reuses `EnumerationSchedule.Merging`. A new proof of the union implementation is unnecessary. `terminal_unions` derives `Merging` from the same observed terminal `forM`; `merging_representative` retains it through the same final representative read. Its fields give totality, the exact joined old classes, and the fact that every final root ID was an original root ID.

Define `mergedRoots roots selected target uv := if roots uv ∈ selected then target else roots uv`. The core readback interface is:

```lean
theorem merging_roots
    (values : List (UVarValue Symbol)) (roots : Nat → Nat) (selected : List Nat)
    (state : State Symbol Guard) (valid : Merging values roots selected state)
    (first target count : Nat) (firstSelected : roots first ∈ selected)
    (path : UnionFind.Reaches state.representatives first target count) :
    Roots state.representatives (mergedRoots roots selected target)
```

For a selected class, `Joined` relates the queried variable to `first`; path uniqueness identifies its final root with the observed `target`. For an unselected class, take its actual final path using totality. `oldRoots` fixes its endpoint under the old root map. `Joined` then identifies that endpoint with the unchanged old root. This proves the root map; it does not assume it.

The second helper equates the ghost redirect fold with `mergedRoots` when `key ∈ sources ↔ key ∈ selected ∧ key ≠ target`. This condition is exactly the source's `IntSet.delete target (IntSet.fromList recorded)`. It permits the actual ascending set order and duplicate-free representation. The fold equality itself holds for arbitrary root functions: once a value becomes `target`, every later redirect leaves it there. Root-map idempotence can be derived separately from actual original `Roots`; it need not be an extra assumption of the fold equation.

A useful public endpoint takes these actual observations:

```lean
(paths : Roots before.representatives roots)
(preScan : Success ((first :: rest).mapM fun sc => representative fuel sc.var)
  before recorded scanned)
(unions : Success (rest.forM fun sc => unionVariables fuel first.var sc.var)
  scanned () united)
(winner : Success (representative fuel first.var) united target resolved)
(keys : ∀ key, key ∈ sources ↔ key ∈ recorded ∧ key ≠ target)
```

It returns `Roots resolved.representatives` for the exact redirect fold on `sources`. `representatives_scan` derives `recorded = (first :: rest).map (fun sc => roots sc.var)`. `merging_initial`, `terminal_unions`, and `merging_representative` supply the readback inputs. `resolve_members` relates the selected accumulator to `recorded`, including duplicates. If the initial cached counts are correct, `moveMany_correct` then supplies the canonical-count equation for the same final forest and unchanged value array. A cached wrapper can construct this endpoint without another union execution.

The endpoint's `before`, `scanned`, `united`, and `resolved` are consecutive states of one supplied execution prefix. The final root is the actual returned root, not a chosen representative. No size accuracy, `LiveRoots`, dense domain, semantic assignment, or successful continuation premise is needed. Union changes stored sizes; this result preserves the actual selected root IDs and witnesses the actual final sizes through `Roots`. It does not assert that pre-union sizes stay equal.

The source takes `reps` before any unions, performs all unions, finds the actual winner, transfers the old waiting buckets, then assimilates the old slots. Immediately after the forest changes but before transfer, the old waiting table need not be correct for the new map. The new theorem covers the completed forest-plus-transfer endpoint. Assimilation and the subsequent node merge require their own actual delta/count correspondence; temporary intermediate writes are outside the invariant. Existing `terminal_assimilations` proves forest retention, but it does not by itself prove native waiting-count maintenance.

The conditional-write source kernel already has exact model correspondence: `SourceUnionFindCompression.union_eq` preserves the entire returned forest; `EnumerationCPSUnionFind.unionVariables_exact` and `representative_exact` preserve the actual source CPS result and final modeled state. These are primitive interfaces, not a supplied final root-map certificate. The native unbounded operation still needs its usual finite successful execution witness. Existing totality/termination and fuel-extension lemmas can supply a common finite bound; no equal-fuel claim across distinct forests is required.

Recommended implementation: one `mergedRoots` definition, a small root-idempotence fact from original `Roots` if exposed, two readback/algebra helpers, and one actual-prefix cached endpoint. Estimate 120–180 ordinary lines, hard 220 before review. No new state machine or union worker is required.

Exact inspected API cuts and identities:

- `EnumerationSchedule.lean`: 273–296 (`root_iff`, `class_iff`); 443–579 (`Joined`, actual representative scan, `Merging`, union loop, root-set readback); 692–708 (assimilation forest retention); 728–738 (actual winner readback); 758–800 (complete terminal prefix).
- `UnionFind.lean`: 201–231 (totality and exact compression paths); 245–332 (actual link and union); 367–421 (union correctness and termination).
- `SourceUnionFindCompression.lean`: 50–118 and 133–155 (conditional lookup and exact union); SHA `1a6d2adbf6c2886ffff91935f59b7cf9d68b32fc90593e3461af823af56b38e0`.
- `EnumerationCPSUnionFind.lean`: complete 68 lines; SHA `e4f2f6a29a5b1e686840b252d7618e8b0da698089e10f3a1be604028ac49e6b8`.
- `EnumerationSchedule.lean` SHA `3e84f2059725b3c0392d4df005574fde2918290cb393c4be0d549a62ad4a4e45`; `UnionFind.lean` SHA `3668867a41890e4721c301092a06c48d3bd757a8eede4b92340fe5db80119a14`.
- `cfta/src/Data/CFTA/Enumeration.hs`: 734–745, SHA `949c484539483f0e646b069899be127a57f0897353b24b92e51a5d90654cec07`.
- `cfta/src/Data/CFTA/Internal/UnionFind.hs`: 95–139, SHA `096db1d6a4d693cebfc9cb643486434baee93e3379c5a411d3edd556d102d434`.

Imports can remain `MicroCFTA.EnumerationPureSelection` and `MicroCFTA.EnumerationSchedule`. The new pure-selection dependency is still a candidate under Root review at this cut. Primitive CPS correspondence can be cited or imported separately; the root-map proof need not reimplement it.
