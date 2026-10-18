# Stored Mu lexical inputs

The component proves three public declarations in `SourceCurrentStoredMuLexicalInputs`.

- `shadow` overrides one exact source reference. It retains the original optional map at every other name.
- `replacements` derives availability of every defined shadow replacement from initial replacements, physical record growth, issued-name extension, and availability of the new local value at the returned heap.
- `build_shadow` equates the actual encoded body call with repaired execution of the original body under the partial shadow map. The equality holds at any current heap and for every outcome. Its source context must be coherent and available and must cover the original body leaves. It requires no successful future body call.

The total map `fun name => some (resolve [self] [localValue] environment name)` cannot in general satisfy global `Replacements`. An unmapped interned name outside the source support resolves to its identity reference. That name need not have an issued reservation. Initial availability of the body does not reserve unrelated names. The partial map avoids this false premise. This is a proof-interface correction, not a Haskell defect.

The private `resolved` lemma proves exact name-resolution agreement. Local names shadow external aliases. Other names retain the original binding or identity fallback. `build_shadow` uses the existing mutual `SourceCurrentStoredPlanEquivalence.encode_equivalent` proof, then `InternedFreshOrdinaryPlanEquivalence.build_exact`. That proof covers closed captures and nested binders. No BinderFree, finite Cap, source word, or current-heap validity premise is added.

Prior art is `InternedStoredSubstitutionRebind.resolve_cons` and `rebind_build`. The sparse map also matches `SourceCurrentStoredMuBinderChildLineage.bind`. The new module avoids importing that larger lineage component. Original Mu body availability needs no additional declaration: `Available.children` extracts the stored body, and `Available.grows` transports it with the same growth and issued-extension premises.

Selected checks are strict `stored-mu-lexical-direct-1`, canonical `stored-mu-lexical-canonical-1`, and full public group `stored-mu-lexical-public-1`. The strict log has exactly zero bytes. The canonical build completed 175 jobs. Each execution records effective memory.max=4294967296, memory.high=4294967296, and memory.swap.max=0 under the five-minute wrapper. All three public declarations have explicit full checks, proof prints, and axiom reports with all eight required settings. Their axiom sets contain only the permitted standard axioms. No constructed integration is claimed by this helper component. No failed Lean attempts occurred.

This helper does not prove a recursive result relation, retained-winner alignment, a semantic result law, general outer completion, or termination.
