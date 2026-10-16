# Cross-view contextual cache transport

Timestamp: 2026-10-16 07:23 CEST.

Owned source: `lean/MicroCFTA/SourceCurrentAllocatedNativeContextRebase.lean`.
SHA256: `dba21c2a73176cb6d898eb77817ec760e2c6e7f423d264bd4c3ea4c80de74726`.
The 225-line source is frozen. Current Haskell main remains `8f85ddb6`.

Focused command:

```
/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lake -d lean build MicroCFTA.SourceCurrentAllocatedNativeContextRebase
```

Result: terminal exit 0, 1064 jobs. No new warnings. The existing unused `inputs` warning in `InternedFreshOrdinaryClosedCompletion.lean:24` replayed. Raw log: `rebase-build.log`. The canonical slot was coordinated with the parent and released at terminal completion. Earlier direct elaboration wrote only a temporary olean; its final log is `rebase-direct-build.log`.

Public probe command:

```
/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lake -d lean env lean /home/tritlo/Code/mcfta/lean/restart-evidence/20261016-semantic-admission/rebase-probe.lean
```

Result: terminal exit 0, no warnings. Twenty-three public declaration axiom checks and twenty-three signatures passed. Five kernel integration examples passed. All public declarations depend on at most `propext` and `Quot.sound`.

## Public contract

The namespace is `SourceCurrentAllocatedNativeContextRebase`.

`Agreement oldInputs newInputs` is generic over distinct old and new input views. Its `valid` field retains old valid inputs. Its `rank` field states exact new-to-old rank equivalence only for old valid inputs. There is no equality premise for unrelated names, default representatives, or whole language families.

`NameCovered oldInputs name` supplies an old valid nonempty input whose identity is `name`. `SeenCovered oldInputs domain` supplies both covered identities for every pair in `domain.seen`. `SeenAdmitted oldInputs state` records this property for each returned node and edge request, independently of result laws. `initial_seen` derives it for empty native tables. `advance_seen` retains it when only the actual machine changes.

The agreement derives input language equivalence by rank erasure. `name_rank` and `name_language` use the covered nonempty input to identify its exact identity-indexed rank and language. `sound_pairs` translates a new sound pair environment into the old one. `complete_pairs` translates the new completeness environment into the old one without changing the combined rank bound: an old bounded pair is first converted into the new ranks, then passed to the new environment.

`row_language` and `row_rank` retain the literal symbol, full guard, child order, term list, and shared rank bound of each original row. Only child input interpretation changes, under old child admission.

`node_law agreement holds request result oldNodeInputs oldSeen oldLaw` transfers the exact returned node law. `edge_law` has the analogous old child and seen admission premises. Both proofs first use the independently supplied OLD request admission. Thus they never obtain a usable result law from a formerly vacuous new-membership condition.

`contextual agreement holds state oldAdmitted oldSeenAdmitted oldContextual` transfers both returned cell families on the SAME native state. `Agreement.admitted` and `Agreement.seen_admitted` derive new coverage from valid-domain inclusion. `rebase` packages all three conclusions: new `Contextual`, new `Admitted`, and new `SeenAdmitted`. It allocates no new state and changes no table, request, result, domain cache, or heap.

## Kernel compositions

1. Both pair-environment directions retain their exact rank bound and derive new seen coverage.
2. Literal native machine advance composes with cross-view rebasing while retaining the same returned request records.
3. Empty native tables derive both old coverage premises and contextual rebasing without a cached-answer premise.
4. A common finite input term in the new view is retained by the exact old returned result through the transferred node completeness law.
5. Actual `GrownInventory.valid_grows` and `rank_exact` construct `Agreement` from physical record and issued-map growth. The example then transfers old warm cache laws and coverage and admits a newly listed closed resident target root. It does not assume old-domain membership of that new root or agreement on its fresh identity.

## Remaining obligations

Old returned-request admission and old seen-pair coverage remain explicit for nonempty warm caches. These certificates are not derived from physical validity, scope, or conditional `Contextual` alone. The module transports coverage of the SAME existing cells; it does not derive coverage for new cells created by a later native execution. Actual causal finish/lookup preservation must supply that additional invariant.

Physical heap validity, semantic readiness, costs, word ranges, and actual query completion are separate invariants and operations. This module does not execute native code, infer independent laws for a new query result, or prove the checked seeded common-subtree witness or stopped-class soundness. It makes no Haskell/GHC forcing, publication, allocation-order, concrete-container, or concurrency claim. No prior proof, Audit, documentation, Haskell source, or Git state was edited.
