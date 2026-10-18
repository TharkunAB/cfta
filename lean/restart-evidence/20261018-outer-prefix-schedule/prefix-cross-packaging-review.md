# Fixture ownership correction

The Prefix producer's frozen 54-entry component accidentally included the root-owned working fixture path `outer-prefix-kernels.lean` at the bytes of immutable `prefix-kernels-4.source.lean`. The root later advanced that working fixture to the checked final source. This changed the shared working path after the producer's freeze.

The correction retains the final source bytes under the root-owned name `root-prefix-kernels.lean`. They remain identical to selected `prefix-kernels-7.source.lean`, SHA 9f0f1865a9c79ab9f5ce1707a40551d4f55c4d3830212861d7250a2ae9cc6683. The former working path is restored from the exact earlier snapshot required by the frozen producer manifest. Selected strict, full public, and claim-definition snapshots and their metadata stay unchanged.

The original 72-entry cross-review manifest did not include either working fixture path. Its immutable snapshot pins therefore remained valid. Its exact bytes are retained in `prefix-cross-full-manifest-first-freeze.json`, SHA a207af32653fcb90f803937bdb88b0bfddfe3f107d51d1025a4ae8c7afa6847a. The updated full manifest also pins this preserved manifest, the final root-owned working fixture, the restored earlier working fixture, and this correction note. All earlier review reports and the frozen 41-entry base manifest remain unchanged.

This is a packaging correction. It changes no production Lean source, selected proof snapshot, mathematical statement, build, selected public count, or selected constructed count. The review still reuses 23 production public pairs, two constructed theorem pairs, and two private statement-definition pairs. It runs no new Lean check.
