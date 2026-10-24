# Shallow-child checkpoint: actual owner schema closure

Reviewed at 2026-10-24T09:29:07.234187+02:00. **SOURCE-ONLY SCHEMA REVIEW CLEAR.** The actual owner closes the schema caveat in the immutable prior script review a2fd552f90c1ec0f131a488f749b5f4c751ad3bb424838df0d7a7e72e7346a58. That report and all five pre-schema sources remain unchanged.

Root authored the scripts; Arity authored the frozen declarations. I independently reviewed schema, exact source delta and input identities. Root/Guard mathematical declaration and body gates remain separate. No compiler, prepared program/import, Git/network/board operation or repository write occurred. Only this report was created.

The sole verifier change replaces insertion-map key public_headers with the actual **public_heads**. Exact text comparison proves that this one replacement reproduces the complete current verifier. It remains216 lines/87 asserts. The other four programs are byte-identical to scripts-before-owner-schema-*.py. Total456 lines/115 assertions and every generic guard from the preceding review remain unchanged. No fallback, ignored field, parser heuristic or relaxed count is introduced.

## Actual frozen schema

- FROZEN is1003 bytes/SHA10e690acb6656596322e523659735c53bb03f6409c7d88ec866ad43a1989aeee. All **71 safe relative object pins / 73 physical files** match exact lengths/hashes and recursive file set. Only exact top-level pins.json/FROZEN.json are excluded. Nested controls, if present, are ordinary payload. Nested FROZEN.pins path/bytes/hash is the format already used by the verifier.
- All **seven literal STRING contracts / 47 lines** equal their files. They contain context12, definition header4, public theorem header27, one terminal condition and three one-line have headers. The source inventory is one named local childMonadList, one public definition and one theorem; no new global instance. Hard cap220 and compiler_evidence=false match the current checks.
- Insertion-map.public_heads is exactly a list of prepareChild/def and prepareChild_complete/theorem under MicroCFTA.SourcePruningEnumerationShallowChild. Entries carry the approved literal plain ` :=\n` and theorem ` := by\n` attachments. Name/kind filtering in the current verifier therefore produces the correct two expected public maps. Literal fragment/body-gate matching is retained.
- Source-index has **16 full snapshots,29 cuts and461 cut lines**. Each source has path/snapshot/bytes/hash and start/end/snapshot cut records. All full live bytes, retained snapshots and exact cut slices independently match. Two sources are external Lean4.34.1 Init/Data/List/Lemmas.lean and Basic.lean; the existing conditional path handling keeps those absolute paths instead of forcing them beneath the repository.
- Import-routes.defining_import_sources is a **LIST25** of path/bytes/hash entries. Each actual identity matches; all are project paths compatible with the unchanged import loop. The twelve routes contain82 adjacent module edges. No stale LIST35/18-source/4-contract assumptions remain.

The initial body-gate.json, nested pin fields, literal contracts, local/global counts, source-index and LIST import schemas now match the actual owner. No V1/V2 history is required for this new component. Earlier action V1/V2 and prospective56+2 histories remain protected by the preceding baseline as documented in the original review. No old failure or new successful check is invented.

I also read both complete new templates. They remain unrendered conditional inputs with actual validation/build/proof/axiom markers. Their scope distinguishes ordinary full-scs writes from Mu/retained-union diagnostic empty-scs allocation, Empty rejection from unsupported terminal/reference representation, and this child action from selected-root expansion. The descendant report remains a source-only cutoff witness with no established native bug. This is not final rendered-document clearance or a source proof.

The closed item is **actual-schema compatibility of these preparation scripts**. Root must still accept mathematical declarations before body work, and later retain actual source/public/build/Audit outcomes, rendered documents, seal and publication evidence. No such future result is claimed here.

## Exact reviewed identities

| Input | Bytes | SHA-256 |
| --- | ---: | --- |
| current verify.py | 12953 | `7498f69eb80861b46082a5b49e94db476f31f4f78c7f7946d767e0a1cb268d4f` |
| before-schema verify.py | 12955 | `4ae431f8b66deaf519420f4b19fbc15c86c3974618b288c22a0e43d049717c87` |
| owner FROZEN.json | 1003 | `10e690acb6656596322e523659735c53bb03f6409c7d88ec866ad43a1989aeee` |
| owner pins.json | 9671 | `4c41f091123caf1c14182b5c1b406cdea16e6498623ab61a41b7fb99414c16ef` |
| owner contracts.json | 3298 | `716f654263c8774d601bf562d68783c65569d601e1cb7e5a137fc44af92cf40a` |
| owner insertion-map.json | 3264 | `ad798043d3ffbf019980eac22dff8fefca0c57ef8a95e5156996ed63c094624f` |
| owner source-index.json | 12604 | `5caf760f70e975f50bccb5179b1963da3295910d386f9565c13f6c05ac50c413` |
| owner import-routes.json | 12107 | `568572847751d8a8a2b945d27671d8c26447d2a24dd15b986d608528fa05c74d` |
| conditional current-note.md | 4896 | `a7f0946ac1fe78637e2d51c84be94d23d569a426a48407bad18f2305d27741e2` |
| conditional status-prefix.txt | 2277 | `1d3b00215b7603036c1885d16e649c5651b5a406a4bbd36e118d1828823fc6b2` |

No blocking schema finding. All previous reports and frozen inputs remain unchanged.
