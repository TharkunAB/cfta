# Native optional-binder generation: independent mathematical review

Read-only review on 2026-10-20 at 18:04 CEST. The reviewed source is SourceCurrentNativeMuOptionalGeneration.lean, SHA256 128066eb8303114ea7653f7257707c5c4a5e3c5628213599f19703cd09491b80. The official source and original prototype have identical bytes. No material mathematical issue was found.

## Local stopping endpoint

`maybeMu`, lines 20–58, takes a semantic heap, the actual available parent value, and an arbitrary selected full Mu at the actual optional call's Outcome.state. It does not take a successful-result equation.

The unused branch returns the parent at the unchanged heap. Thus its selected full cell is exactly initial. In the used branch, lines 35–37 derive the rich joint Context for the actual entry and leaves parent. The base Context comes from the semantic heap and actual leaves_available. The depth Context is the same entry's depth heap. No Context at a later reader is substituted.

The actual maybeMu_eq in SourceRecursiveIntersectionMaybeMu, lines 58–69, identifies every outcome with the exact generated binder build. The proof converts the selected cell to that build state and invokes the stopping producer once. The initial alternative retains the exact key, entry, body, depth and ordinary components. The generated alternative keeps one existing Written receipt. The local event can be nested in a probe or callback. It is not asserted to be the outer candidate publication.

The writer receipt retains the generated source root and its original leaves as captures. It retains the same event's Reached, candidate equality, first-write absence, actual issued callback paths, and physical and issued suffixes. There is no desired output law, prior writer premise, or source completion premise.

## Same-site trace composition

`trace`, lines 68–114, first calls the existing OptionalSite.trace locator, line 93. That locator retains one actual admitted trace prefix, one yielded optionalBinder step, the actual call equation and advance, and the exact suffix. It derives entry-cell absence and postcall presence for the same selected full Mu.

The bridge applies the local maybeMu theorem to this exact site and selected cell. The local prior arm contradicts that site's exact None. The other arm returns one context, build equation and Written witness. Line 106 uses compiled.symm.trans called. This is the actual generated source build's done equation, with the identical result and heap from the located native step. The proof reindexes the same returned Written to that heap. It does not choose another site or publication.

The existing locator excludes primitive Work jobs with actual WorkInputs and work_noNewMu. Its actual step and trace inductions retain semantic heaps and physical and issued growth. It does not factor arbitrary publication History backwards or infer any native memo History from Grows.

## Exact limits

The local maybeMu theorem includes pending Outcome.state. The trace theorem covers admitted yielded steps. It does not cover the physical effects of a terminal blocked optionalBinder step. The Native.step implementation advances to the pending constructor heap before it returns blocked, so that last interval remains a separate consumer obligation.

A generic admitted trace can begin with caller-supplied optionalBinder code. The result does not attach a captured compileMu owner, entered domain, or original open body query to the located instruction. It also does not infer source-program ancestry for encoded leaf captures. These are separate obligations. No closure, observation equivalence, recurrence decrease, renewal, termination, or Haskell correspondence claim follows from this module.

## Reviewed checks

The selected official strict receipt is generation-official-direct-3. Its log has zero bytes and its source matches the final module. The selected generation-official-public-1 group has two full public pairs. I ran its existing non-Lean probe checker read-only. All eight options, complete statement and proof prints, omission checks and standard-three-only axiom checks pass. The official canonical receipt returned zero. Its log replays only the known InternedFreshOrdinaryClosedCompletion unused-variable warning; this is not described as a warning-free canonical log.

This review owns zero new Lean runs and zero new proof pairs. The two public pairs and selected production receipts are reused. The earlier two root implementation failures remain owner evidence and are not selected by this review. The review does not alter their artifacts.
