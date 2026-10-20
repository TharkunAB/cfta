# Rooted child integration through a closed original node

Checked at 2026-10-20 17:03 CEST. This is an authored constructed integration, not a separate independent review of the generic production proof.

The fixture source is `rooted-indexed-source-child-fixture.lean`, SHA-256 `15efc336951f7bb87f0c7a4e97bab3873e64f8633dcb30712b7985b2375c54e4`. It has one public theorem, `MicroCFTA.RootedIndexedSourceChildFixture.actual_closed_member`.

## Actual source and selected occurrence

The source is `union [node5(false,[leaf17,leaf17]), var0]`. The lexical input is the available Depth reference. The joint Context is derived from the empty Context and the actual available Depth input. `reached_initial` supplies the original root receipt. Actual successful builds from empty tables produce the closed original node and the open whole union.

The complete parent row has symbol 5 and guard false. Its child lookups at positions 0 and 1 both return the same closed leaf17 value. The fixture retains `0 ≠ 1`. The selected child position is exactly 1. No encoder slot or first-equal-value search is used. The returned whole union is open, while the original source node result is closed. This is the case that an open-result premise on a source node extractor would exclude.

The fixture derives `RowAt raw parentRow` from the computed whole result. It calls `build_row_origin` on the SAME original expression, inputs, empty entry heap, completed raw result, return heap, Context and row. It then calls the official `from_source_row` once, with that derived SourceRow, the initial Reached receipt and the exact child-1 lookup. No desired Origin is supplied or constructed in parallel.

## Returned receipt

The node-call certificate is extracted by cases on the returned Origin. The fixture proves the shape of actual descendant source Paths. These Paths cannot cross a binder because the original source has none. A capture stop would resolve only to the actual Depth input, which cannot have a structural row. Thus the Origin's node arm supplies the certificate.

That certificate retains the actual buildEdges/makeNode equations, distinct existential source and canonical output row indices, the SAME complete parent row, the SAME RowCall, the original child syntax at index 1, the returned value at index 1, the ordered child prefix, the exact adjacent child build and suffix, and the rich Context at the child entry. It also retains forward physical and issued-name growth, Reached at that exact child entry, and the strict original syntax bound.

The public theorem expands this entire existential. Its proof aliases a private checked witness with the same proposition. The size bound explicitly uses `instSizeOfDefault Nat` and `instSizeOfDefault Bool`, matching the generic production theorem. It is a bound on the original source child against the original supplied union syntax. It is not the default concrete Nat/Bool payload measure and not a constructed-value or recursive execution bound.

The returned existential source and canonical indices are not identified with separately computed indices. Their exact RowCall lookups and full-row equality remain in the certificate. The fixed selected child index 1 is preserved throughout.

## Validation and limits

Selected strict attempt `rooted-indexed-fixture-direct-3` completed with exit code 0 and a literal zero-byte log. Selected `rooted-indexed-fixture-public-1` completed with exit code 0. The hardened full one-head statement/proof/axiom check passed all eight print-option requirements, the standard-three-axiom allowlist, and all no-omission checks. The public log has 88631 bytes.

All four Lean jobs are preserved. Direct attempt 1 failed on unresolved source-path placeholders and an untyped existential index; it also reported one unreachable tactic. Direct attempt 2 failed on typed existential binder syntax. Direct attempt 3 and public attempt 1 passed. No job timed out or exceeded the cap. Actual cgroup limits were 4 GiB maximum and high, zero swap, with a five-minute wrapper limit. Recorded peaks were 221, 225, 212 and 227 MiB. The pinned toolchain was Lean 4.34.1. Fresh usage checks were observed before every job and are recorded separately. No canonical build was run by this fixture component.

Counts are zero new generic public heads, one constructed pair, zero auxiliary pairs, four Lean jobs and two failed elaboration attempts. No capture/binder fixture, source_cases integration, later Ready/replay, or native-history transport is claimed. This source-built node case does not establish general original binding ancestry, global renewal, termination, or Haskell refinement.

All owned files remain under this isolated directory. The input copies pin the official production sources and source-path foundations. The standalone verifier checks all portable pins, selected readbacks, strict source correspondence and effective caps. An optional `--live-root` argument checks the copied inputs against their ROOT-relative paths.
