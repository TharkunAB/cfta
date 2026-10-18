# Next source simulation obligation

Checked on 2026-10-18. The new normalization theorem removes only literal normalization from the remaining source obligation.

`LiteralNormalizationSimulation.Relation P a b` is exactly `Below a b` or one `P` pair preceded and followed by `Below`. `Relation.pre` and `Relation.post` retain this restriction. `directed` proves `Directed reader (Relation P)` from the genuine per-source obligation `forall a b, P a b -> LiteralLocalSimulation.Clauses reader (Relation P) a b`. It does not admit transitive chains of `P`.

The proof uses full literal inclusion before the source pair and the independently proved `below_directed` after it. Matched row children retain both ordered directions. A union epsilon step only extends the literal prefix. A Mu epsilon step uses the actual successor clause supplied for the exact literal Mu atom. The proof does not use `Directed` for the source relation or assume output observation equality. The earlier checked closure obstruction needs two source steps and does not satisfy this restricted premise. It remains a counterexample to arbitrary `Local (Closure P)` closure, not a counterexample to actual `Generated`.

The smallest faithful next target is to prove these literal clauses for the actual source generators at one fixed causal reader. The clauses must transfer every literal reference, every full literal row with mutual ordered child membership, and each actual successor of each literal Mu atom. They must produce at most one source pair surrounded by literal inclusion, or use an independently proved semantic certificate for any additional source edge. A chain of actual generator memberships is not such a certificate by itself.

The ordinary source case has a direct route. `CausalGeneratedNodeLocal.node` already derives both `Local Generated` directions with actual historical node receipts and causal Empty survival. `LiteralLocalSimulation.of_ordinary` supplies the literal clauses. Inclusion of each generated child pair into the new relation needs only the reflexive `Below` prefix and suffix. No observation equality premise is needed for that embedding.

The union case must keep its actual original reader. `FixedReaderUnionFragments.source` now derives the indexed original historical members, available raw members, literal-atom executions and full `RowCalls` at the warm parent reader. It does not require full subgroup filter or stored calls to be warm. Its exact coverage separates retained reference/Mu atoms from surviving reconstructed ordinary rows. This is a useful input to a fragment-level strict source proof. The old `LiteralSourceClauses.union` still returns clauses at a produced later reader from supplied strict member laws; it does not prove its `Law` at the original reader. Full-subgroup induction hypotheses must not be silently applied to the new smaller fragment schedules.

The used-Mu case is still the substantive semantic obligation. The new publication and selected-writer producers construct both source-generator memberships for actual body/probe outputs under arbitrary common maps. They preserve the older writer syntax. They do not prove the literal clauses for these new memberships. Reconciling the current requester, the chosen writer and the opposite result can introduce more than one source edge. The new normalization theorem does not combine those edges. A direct source relation constructor needs its own actual clause proof, or the intervening writer comparison needs an independently justified semantic law.

Finite observation depth does not resolve this obligation alone. `OpenObservations.Same` reduces depth only at ordered ordinary children. `OpenObservations.unfold` preserves the same observation depth, including depth zero reference origins. `OpenOriginSteps` gives a strictly shorter actual epsilon witness after a real front step, and `OpenPreorderSimulation.Directed.path` already uses this progress once genuine local clauses are known. Replacing that actual step by an unproved source chain can increase the new witness length and loses the required decrease. Thus neither same-depth self comparison nor a newly generated proof of membership is a valid smaller semantic induction case.

Actual own-reference filtering supplies a useful syntactic fact: `LiteralFilterParts.literal` removes a direct own-root atom except at a standalone own root. `UsedBinderOutputTags.bare` gives exact bare-root parity. These facts can help prove a guarded source rule. They do not prove it now: a literal Mu is atomic for root filtering, and its actual epsilon successors can expose further references. The generic rule must account for that case rather than declare every filtered occurrence guarded.

A chronological publication proof is another possible route, but its stronger invariant remains to be defined and proved. It must retain full row fields, child order and actual epsilon origins under arbitrary permitted replacements and later supported readers. The current causal payload invariant carries assigned root profiles only. Source syntax order, publication order and observation depth cannot be combined into a decreasing measure until each new semantic task is shown to decrease one component while preserving the earlier components.

This batch proves the restricted normalization rule. It does not prove all `Generated` clauses or general retained used-Mu alignment. No Haskell defect or infinite execution follows from these proof boundaries.

| Reviewed source | SHA-256 |
| --- | --- |
| `lean/MicroCFTA/SourceCurrentLiteralNormalizationSimulation.lean` | `877299f5680d2474a60fca3e9b0686778eab2f6d718afc4289e15a09b90b4c10` |
| `lean/MicroCFTA/SourceCurrentLiteralLocalSimulation.lean` | `da30ba8484667b18cc73087c5216c44c0c405c9d9d2a88000e6c355b0e27f3cf` |
| `lean/MicroCFTA/SourceCurrentSourceDirectedCases.lean` | `f770d8bd236b7b2b8c66cf75b3b1c108e2835afa5f8999b9dadf52923d5c0888` |
| `lean/MicroCFTA/SourceCurrentDirectedClosure.lean` | `96b94082cf4c8fb1aa7cec62023d5a9f6db59e09884d8e1016d1af5676067a54` |
| `lean/MicroCFTA/SourceCurrentOpenPreorderSimulation.lean` | `080dce05c66ea21a6971e0b07d866361b894b3aa3f7d05ea525985ef50ac32fa` |
| `lean/MicroCFTA/SourceCurrentOpenWeakSimulation.lean` | `363b1f97c4e4d376c53049a12d8a1fad8c13a4a70a1103e26dc2c7968aaa03c1` |
| `lean/MicroCFTA/SourceCurrentLiteralRootParts.lean` | `d2d0bddaf1aa4f3397505ca751915b04ebf190a528c8c27db53255c29cbea4df` |
| `lean/MicroCFTA/SourceCurrentLiteralFilterParts.lean` | `5db5739dd40775b0fe49a4e0ae44d1b3d5ae22ed8b86ab6d366bac27baf8cdbb` |
| `lean/MicroCFTA/SourceCurrentFixedReaderUnionFragments.lean` | `f6a1c3568d44d546bb17e7324bc92cbd7c2447ae01c1373bd26d03b47281f0bf` |
| `lean/MicroCFTA/SourceCurrentLiteralSourceClauses.lean` | `6c385fc36059618a0b4c97bc29ca8c7b16f5fbcbad9e6ff40fdf87f80c7c1c99` |
| `lean/MicroCFTA/SourceCurrentCausalGeneratedNodeLocal.lean` | `5fe61e23ba1de494d15fc044fdd99e769797c9b50c26f0be8e399850a49bc3f7` |
| `lean/MicroCFTA/SourceCurrentCausalGeneratedEmpty.lean` | `744a576b5218ae54d27847b7ad590de532756b4130f54861859a154631ef89cd` |
| `lean/MicroCFTA/SourceCurrentStoredLiteralRowLineage.lean` | `d04385883eb67f7c365d8c4a7492429ba8dcbe677b7a6a6be7e73d2ed54ddd1b` |
| `lean/MicroCFTA/SourceCurrentNativeOriginExposure.lean` | `20ecd0f0f4ae76264f1cc59f44aee95181c095de0e65f5dc4ee8ff749b8bf046` |
| `lean/MicroCFTA/SourceCurrentUsedBinderOutputTags.lean` | `249b06a358eac40de2451a591566f679ebb02d5be7edbd7432b9633e8b5a5d27` |
| `lean/MicroCFTA/SourceCurrentUsedBinderRootAlternatives.lean` | `47d9c3eace5b6cc328ff293db218cf13a85f5c23ae2bd1418c37cc568586b27b` |
| `lean/MicroCFTA/SourceCurrentOpenObservationLanguage.lean` | `cae50937bf346a755d94a34f19c9bacfe2836d3ae6053c99f47e3889e727b868` |
| `lean/restart-evidence/20261018-causal-union-local/closure-obstruction.lean` | `fad20997ce5f92f02cc4ec7963cb86a27a1e48aa61da5cefe8afb2ef451b3024` |
