# Source API basis

These are source-only prospective references. No owner is frozen and no candidate has run.

| Whole source | SHA-256 | Relevant inclusive cuts |
|---|---|---|
| `/home/tritlo/Code/mcfta/cfta/src/Data/CFTA/Enumeration.hs` | `949c484539483f0e646b069899be127a57f0897353b24b92e51a5d90654cec07` | 432–474 current raw read and lost/gained count; 879–903 capture/reset/final store |
| `/home/tritlo/Code/mcfta/lean/MicroCFTA/SourcePruningEnumerationNativeIndex.lean` | `13c8b37a63e950f4b26d2e9c927cc3108b50b3024b96b3be70a8a539f6f7f160` | 16–51 classifier/count/write; 54–76 uniform finite count |
| `/home/tritlo/Code/mcfta/lean/MicroCFTA/EnumerationCanonicalWaiting.lean` | `a941b9b49e87115f26ecba015bc23e15a3d873410ac943ded77ff5f8963057bd` | 24–37 count/replace/Correct; 83–90 replace_correct |
| `/home/tritlo/Code/mcfta/lean/MicroCFTA/EnumerationCorrectness.lean` | `087b96d593bb42cea0b61b2742b43d4a41ce5a2d990e300c8d15700e2eb0672d` | 620–649 FragmentBound/SlotBound/StorageValid; 959–966 set_storage |
| `/home/tritlo/Code/mcfta/lean/MicroCFTA/SourcePruningEnumerationObservation.lean` | `5a7b858adc4febb75621b9836053f308924c22d5fd7662741da61cbdab629bf4` | 19–26 PendingRealized; 45–54 full-frame theorem has unchanged-values premise and is not applied across this write |
| `/home/tritlo/Code/mcfta/lean/MicroCFTA/SourcePruningEnumerationWrites.lean` | `32864f9158615ee7787c7490356471489978a5622ea984d904f7b03329510a7e` | 60–65 exact list-set old/fresh realization proof shape |
| `/home/tritlo/Code/mcfta/lean/MicroCFTA/EnumerationState.lean` | `83a898b883ec7b52469bccd87e8afa4f7abb320e3c935bf48f3d80ad77003cc4` | 67–73 core fields; 102–110 raw-target write/read |
| `/home/tritlo/Code/mcfta/lean/MicroCFTA/EnumerationSchedule.lean` | `3e84f2059725b3c0392d4df005574fde2918290cb393c4be0d549a62ad4a4e45` | 36–38 Roots; 201–204 references |

`complete` uses the current raw stored equation for the target bound. It uses `count_complete` on `references old` with change=-1, then the empty gained fold. The explicit waiting conclusion is the canonical removal count. `replace_correct` applies because the new enumerated slot has no references. `set_storage` needs exactly the supplied FragmentBound. The PendingRealized proof reuses the list-set membership argument; its fresh branch is impossible for an enumerated replacement. No invariant is inferred from Graph or from a desired successful suffix.
