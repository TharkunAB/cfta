# Generated scalar shape proof-repair review

Reviewed at 2026-10-24 03:51:53 CEST. Status: **PROOF_REPAIR_CLEAR**. No executable definition, datatype, structure, imported dependency or theorem statement changed. This adds to the earlier source-model review; that original report remains unchanged. I did not author these repairs, run Lean or Lake, edit repository files or mutate Git.

I compared the complete original 255-line `shape-check-1/checked.lean` with the final installed 298-line source. I read the complete unified diff without truncation. The first larger diagnostic output was truncated; I used a separate complete diff and do not claim a manual read of all 588 old error-log lines. Read-only checks validated the full old raw log hash and inspected its distinct error headings. The changes consist of exactly **13 public constructor/field docstrings and seven theorem proof bodies**. After removing comments and empty lines, the complete prefix containing all executable definitions and data declarations is byte-identical. All 13 public and two private theorem headers are byte-identical, including every binder, premise and conclusion. The other eight proof bodies are unchanged. The complete candidate, final strict-check snapshot and installed file are byte-identical at SHA-256 `bcf77307a41f47a11e3c5c7862ba8120f575761924e9eeebd47b8fc01a977ae9`.

The added docstrings cover six Constructor alternatives, three Reified alternatives and four public structure fields. They do not change fields, constructor order, derivation clauses or source behavior. They directly address the missing-documentation linter errors without disabling a linter.

The seven proof changes preserve the existing argument:

- `generatedName_success` removes `eq_comm` from the broad Boolean/definition simp set and uses equality symmetry only for the remaining terminal goals.
- Private `namedScalar_success` exposes the definitionally equal `Except.bind`, then uses the existing success characterization and existing generated-name theorem. Its statement is unchanged.
- `constructors_success` makes the nil `Except.ok` result and the cons nested binds explicit before using the same list induction and helper.
- `constructors_first_error` exposes each actual bind, rewrites the actual first constructor result, then rewrites the same induction hypothesis. Failure still stops at the first rejected occurrence after a valid prefix.
- `derive_data_success` replaces overloaded bind/pure notation in its `change` goal with the definitionally equal explicit `Except.bind` and `.ok` constructors.
- `type_collision` and `type_hash_error` expose the earlier name bind and rewrite its existing error result. No constructor check, new premise or validation oracle is added.

The source/name/error-order review therefore applies unchanged. In particular, uppercase then trailing-hash then scope-lookup order remains literal; independent ValidName conditions remain unchanged; and `generated_names_pass` remains only the unconditional suffix-prefix compatibility theorem. Generic/NodeView build-read realization, native lexical admissibility and TH/name extraction remain boundaries.

The first strict attempt actually failed and remains retained. The final strict attempt reports exit 0, zero raw bytes, warning-as-error and all linters. Its checked-source digest equals the final installed digest. The installed target build receipt and raw identity also pass. Root's aggregate Audit receipt matches its complete 617-byte raw log: 3,676 jobs and 75,963 checked theorem dependencies, with only the replayed older unused-`inputs` warning. These are Root's executed checks; this review only read and correlated them.

The exact reviewed unified diff is 8019 bytes, SHA-256 `ef2149a1cb7e04a7b4756f18d6a2854404981f9884d11b7fcb5ba971ea096082` (labels `shape-check-1/checked.lean` and `final-installed.lean`). No changed public contract or new executable behavior is hidden by the proof repairs.

## Checked input identities

| Input | Bytes | SHA-256 |
| --- | ---: | --- |
| `/tmp/mcfta-derived-scalar-shape-20261024/shape-check-1/checked.lean` | 14859 | `ecfcec6f013cec35c683c2725153814d3c94bf1ee2d97b8353781c8988e0355e` |
| `/tmp/mcfta-derived-scalar-shape-20261024/SourceGeneratedNodeViewShape.lean` | 16951 | `bcf77307a41f47a11e3c5c7862ba8120f575761924e9eeebd47b8fc01a977ae9` |
| `/home/tritlo/Code/mcfta/lean/MicroCFTA/SourceGeneratedNodeViewShape.lean` | 16951 | `bcf77307a41f47a11e3c5c7862ba8120f575761924e9eeebd47b8fc01a977ae9` |
| `/tmp/mcfta-derived-scalar-shape-20261024/shape-check-1/report.json` | 508 | `35f07c51ed7268aa316292bdf1c4676120adad76deea881dd3f67cb1c439d866` |
| `/tmp/mcfta-derived-scalar-shape-20261024/shape-check-1/raw.log` | 29581 | `e48a78987fb097855c5396b980b69e6cac789bba692048993ea7213a3a9747ce` |
| `/tmp/mcfta-derived-scalar-shape-20261024/shape-check-2/report.json` | 504 | `5bd03cd2e5d3a75236143bd4bf6f7661a437ed601fec11b4ac0ec02339bc9f32` |
| `/tmp/mcfta-derived-scalar-shape-20261024/installed-build-1/report.json` | 323 | `efbf52bfe41de8766a59bea1c84c98b8a910e56795cbf83d6866ee76d6a6af7f` |
| `/tmp/mcfta-derived-scalar-shape-20261024/audit-1/report.json` | 300 | `2720af7af5a50843b1d7ba23aefae25b82b20600e5da02bb4ba7caff549bcb64` |
| `/tmp/mcfta-derived-scalar-shape-20261024/audit-1/raw.log` | 617 | `7601e55e65ae28bff2303ed6d529e82e1edcc0dd1ea48ceba93dab2cfcea4b94` |
