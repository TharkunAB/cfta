# General stored-substitution cap transport

The source is `SourceCurrentConstrainedCapStoredSubstitution.lean`.
Its frozen SHA-256 is `75a50564313d590e9f1c238929791aa49af824b681f050ed03a1bee63e18008b`.

`execute` (line 162) proves a `HereditaryConstruction.Checked` contract for the actual repaired `InternedFreshOrdinaryStoredSubstitution.execute` outcome. It takes initial `Facts`, source availability, the source `Cap valid depth`, available replacements, hereditary replacement annotations, and the initial causal `MuStored`. It takes no actual successful return. The contract retains `MuStored` at the actual stopping state. Its result field proves the same cap depth when that outcome returns.

`complete` (line 176) derives its own literal successful execution from initial `RequiredCache.Ready`. It returns that execution, the same-depth cap, the causal Mu store, result availability, full `Ready`, physical growth, and issued-history extension at the same returned state. It has no future result, completion, readiness, profile, or resource premise. It uses the existing general repaired stored-substitution completion theorem. It does not use a binder-free execution fragment.

The proof derives `Construction.Typed` for the actual stored encoding. Global capture lookup uses `InternedStoredSubstitutionBindings.global_lookup` and actual coherent source records. An ordinary row uses one finite layer. A union keeps the same layer. A source Mu can enter a cap only through its hereditary annotation; its actual stored body therefore checks at depth zero for every fresh local reference. The proof does not require every captured value to be hereditary. It checks each actual lexical use. An unused constrained capture remains allowed.

The causal warm Mu invariant is the existing `MuStored`. This law connects annotated probe records to the stored body at that actual key. General `Facts` alone does not supply that law. No stronger warm invariant was needed here. The proof uses the new graded `Construction.build` producer to discharge the actual nested binder requests. It does not assume their output cap.

Validation:

- Strict absolute-path direct attempt 5 returned exit 0 with a zero-byte log.
- Root canonical `cap-stored-substitution-build.log` passed 1086 jobs. The only replayed warning is the historical unused `inputs` warning in `InternedFreshOrdinaryClosedCompletion`.
- Six public declarations have imported full explicit signatures and axiom reports.
- One constructive integration kernel passes. It builds an open false-guard ordinary source with a nested raw Mu and a captured original reference. It proves that source is nonhereditary and has cap depth 1. The complete endpoint then constructs the actual substitution return. The returned physical identity differs. The cap depth, full readiness, causal store, availability, growth, and history hold at that exact return. The kernel takes no successful source or substitution premise.
- Final probes use all linter, explicit/proof/universe/deep-term, full-name, and 10-million print-step settings. Their logs contain no warnings or `sorryAx`.

Attempt history is preserved. Direct attempt 1 failed before a source file existed because its working directory duplicated `lean/`; its log records the missing source. Attempt 2 is the first saved source. Attempts 2 and 4 failed on explicit unfolding and simplifier syntax. Attempt 3 passed before the full-ready conclusion was added. Attempt 5 is the final source. Kernel attempts 1 and 2 failed on explicit reduction and tuple elaboration. Attempt 3 is final.

This component proves cap transport for stored substitution with hereditary replacements. It does not prove general mixed native optional-binder preservation, recursive selected-path termination, or whole-library Haskell correspondence. Syntax indices here are the existing natural-number lexical slots. The theorem adds no claim about signed host conversions.
