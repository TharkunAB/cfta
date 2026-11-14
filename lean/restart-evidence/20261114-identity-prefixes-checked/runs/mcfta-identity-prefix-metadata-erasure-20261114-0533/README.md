# Identity-selected prefix metadata erasure

Created on 2026-11-14 at 05:35 CET. The Lean module is an uncompiled proof draft.

The candidate defines two pure functions. `eraseMetadata` returns the canonical `Metadata Unit` value `⟨[], [], [], ()⟩`. `erasePrefix` maps metadata in the existing `SelectedStep.Result` datatype. It adds no datatype, provider, callback, or operational worker.

The main theorem compares two calls to the same actual `runPrefixWithNarrow` backend with identity narrowing. One call receives arbitrary `Metadata Typing`. The other receives arbitrary `Metadata Unit`. Both calls use the same graph, templates, metadata-independent order, caller, full query memos, cache, six fuel arguments, and selected raw hole ID. Both stop arguments are `none`. The theorem states that their results are equal after `erasePrefix`.

## Exact projection

| Existing constructor | Erased field | Fields retained exactly |
| --- | --- | --- |
| `stopped` | None | Complete raw read and optional complete raw recursion check |
| `parked` | Metadata in successful restart rows | Checked Core, candidate, optional raw-list shape, errors, `Next`, every row Core, row order, duplicates |
| `narrowed` | Metadata in successful Right rows | Checked Core, complete preparation result, caller, full query memos, action observations, candidate, optional raw-list shape, errors, Boolean, every row Core, row order, duplicates, complete ordinary observation |

The projection preserves every `None`, empty list, error, endpoint, and result constructor. It does not turn a failed or incomplete observation into a successful observation. The `prepared`, `action`, and `ordinary` fields do not contain the result's metadata parameter. The candidate reuses those fields directly.

## Source obligations

- `SourcePruningEnumerationSelectedStep.lean:26` defines the existing result fields. Lines 43 through 96 define the actual selected prefix. The two projections retain these fields without changing their types.
- `SourcePruningEnumerationAction.lean:17` defines `prepareWithNarrow`. Metadata reaches the supplied narrowing operation only. With the identity operation, preparation is definitionally independent of metadata. The private helper `prepare_identity_metadata` proves this exact equality by `rfl`.
- `SourcePruningEnumerationRestart.lean:13` defines the actual decision. With stop `none`, it uses the supplied order and the same cache. An order that ignores metadata therefore returns the same decision. Lines 24 through 29 retain the same Core and attach metadata only to the successful raw row. The projection removes that metadata difference. A stuck decision remains the same empty raw list.
- `SourcePruningRecordTypes.lean:83` proves `recordTypes_inr`. The Right event returns `pure (false, metadata)` for every template catalog. The theorem therefore allows arbitrary templates. It does not require the empty catalog used by the earlier whole-worker proposal.
- `SourcePruningEnumerationSelectedStep.lean:125` supplies the existing structural proof template. The draft follows its actual read, check, preparation, action, encoding, and adapter cases. The parked and Right cases add the metadata maps. All other cases reduce to equality of the same retained fields.

The theorem needs only the equality instance required by `runPrefixWithNarrow`. It adds no readiness, availability, model, productivity, successful-prefix, or future-continuation premise.

## Files and checks

`candidate/lean/MicroCFTA/SourcePruningEnumerationIdentityPrefixMetadataErasure.lean` contains the two definitions, the `rfl` helper, and the main theorem proof draft. `theorem-header.lean.txt` and `preparation-helper.lean.txt` contain their exact interfaces. `candidate.patch` adds that module without changing an existing file.

`inputs/` contains the four exact source inputs. `source-pins.json` records their hashes. `prior-plan-pins.json` records the two earlier approved plan files. Those plan files remain unchanged.

GNU patch adds the candidate to an empty temporary tree with zero fuzz. The added bytes equal the candidate bytes. The inverse patch removes the file with zero fuzz. `patch-roundtrip.json` records both results. These mechanical checks do not establish Lean elaboration.

No compiler or runtime probe ran. No live source, Haskell source, Git state, or message board entry changed. Root must compile the module before making a theorem claim.

## Scope

This draft concerns the selected prefix only. It does not establish whole eager-worker erasure, sufficient recursive fuel, accepted output, finite completion, source/Haskell representation correspondence, or literal Haskell runtime behavior. It does not compare identity narrowing with configured pruning. It makes no claim for a metadata-dependent stop rule or a metadata-dependent order.
