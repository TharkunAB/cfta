# Independent review of filtered union coverage

Reviewed on 2026-10-18 at 16:04 CEST. No production source was changed. No Lean build was run for this review.

## Result and scope

No material issue was found in `SourceCurrentFilteredUnionCoverage.lean`, SHA 1bb154e21f58b71cf7b1fb72a53571f125f3fde1494c001020c0111e9051b390. The selected production evidence contains two full public pairs. This package reuses those two public pairs and one separately owned constructed pair. It adds zero public or constructed pairs.

`parts` (lines 52–158) characterizes both literal atoms and complete ordinary rows of an actual filtered parent reconstruction. `empty_iff` (lines 160–198) characterizes physical Empty by physical Empty of all retained original member reconstructions. Neither theorem assumes the corresponding parent output law.

The entry facts remain explicit: one Ready reader, availability of every original member value, an actual warm union request, actual warm parent filter and stored calls, available replacements, and actual warm filter/stored calls for every original member. These member schedules are real local premises. The theorem does not infer their warmth from the parent being warm. `GeneratedUnionPreparation.prepare` is the separate finite producer that can construct them at a later reader. It does not assert their existence at an arbitrary earlier reader.

## Bare-self exception

The exact retention condition is `raw ≠ reference own OR parent = reference own`. A bare-self source member is excluded when the complete normalized parent has other root parts. Its own direct filter would leave it unchanged. Therefore unconditional inclusion of every member output would be false. When the entire parent is bare self, the bare member is retained and the parent filter also leaves it unchanged.

The forward atom proof (lines 79–108) handles the harder parent-bare case with `LiteralFilterParts.bare_iff`. It uses exact atom containment AND absence of all ordinary rows. It does not infer that a member is bare from a single self atom. The raw member may be a union or contain opaque Mu atoms; the normal available-root characterization handles these shapes. If an original ordinary row supplies the output (lines 140–156), the source member cannot be bare self, so retention follows without an extra assumption.

## Full atom and row coverage

`LiteralUnionParts.literal` and `.row` derive exact root coverage through actual normalization. They account for flattening, identity selection, canonical readback, and ordinary edge normalization. Mu atoms remain whole literal values. The coverage law does not unfold them or claim epsilon/source ancestry.

`StoredLiteralExecutionParts.parts` splits a result row into an actual literal-atom execution or an actual original-row execution with its surviving ordered children. In the ordinary branch, the new proof carries the SAME complete source edge, SAME `RowCalls`, and SAME live test into the selected member. It does not replace the full row by its symbol or arity. Full guards and ordered child values remain in the row itself. Atom-origin rows likewise retain the same actual atom execution and its complete returned row.

The reverse directions use the existing `GeneratedUnionCases.retained_member`. Its proof combines actual literal inclusion, the exact filter retention condition, and actual warm stored executions under one map. It assumes no semantic Same relation or final parent equation.

## Physical Empty and nonvacuity

Both filtered and stored output availability are derived from actual initial availability, replacements, and literal calls. `no_parts_empty` uses normal available-root completeness to compare with actual Empty. It is used only after those availability facts are established. The proof does not infer physical Empty from epsilon agreement or finite-language emptiness. A physically nonempty Mu can have no finite accepted tree; these theorems do not alter that distinction.

The member-completion premise is existential per original occurrence. The final Empty law quantifies every actual warm member filter/output pair. Execution determinism makes those concrete outcomes coherent. The supplied actual parent and member calls are not restatements of the desired coverage or Empty conclusion. Empty member lists and bare-only lists are permitted boundary cases; the proof also retains arbitrary nonempty ordinary and mixed root parts. The source-built fixture below checks the nonempty member and Empty parent boundary.

## Source-built bare-self integration

The final fixture source `union-coverage-kernels-2.source.lean` has SHA b5e48ada0ce5ea9970bacf847f270a55b11f0eea1daf7ace0056324965182cb6. It builds its own USED Mu `mu x. f[x]` from empty. This proves physical nonempty; the fixture does not assert a finite accepted tree for that Mu.

It then builds the actual raw union of `reference depth` and `reference (uninterned 0)`. The map sends the first name to that available Mu and the second name to Empty. `GeneratedUnionPreparation.prepare` constructs the actual member filters, stored calls, parent filter/call, all intermediate states, Keeps, final availability, and final warm replays. The original raw source results are aligned by actual deterministic `buildMany`.

At that final reader, both new coverage theorems are invoked with actual available raws and actual calls. The fixture's per-member warm-call helper is a literal evaluation of these two references; it assumes no future completion. The complete parent filter removes self, and its stored return is Empty. The independent bare-self filter remains self and its stored return is the physically nonempty USED Mu. The public witness retains explicit exclusion of this bare member, both theorem conclusions, and the complete actual preparation receipt. This checks why unconditional all-member Empty equivalence would be false. It is not a Haskell defect or a language-emptiness claim.

The selected strict fixture log is literal zero bytes. Its private checked theorem and public alias have the same exact full statement. The full constructed proof/axiom group passes the same hardened checker. Attempt 1 remains in its owner component. This review selects attempt 2 and runs no Lean build.

## Selected evidence

Strict `union-coverage-direct-5` has terminal code zero and a literal zero-byte log. Canonical `union-coverage-canonical-3` has terminal zero, no warning, and completes 612 jobs. `union-coverage-public-1` has two full check/print/axiom groups. This review reran only the lightweight existing evidence checker. Both public groups pass all eight required options, complete proof printing with no omissions, and only standard-three axioms. The receipts record Lean 4.34.1 and effective four-GiB max/high with zero swap under the five-minute cap.

No initial-source rank, general changing-capture binder alignment, all Generated Empty fusion, recursive completion, or Haskell defect follows from this component. Earlier attempts remain in their owner component. This manifest pins only the final selected source/evidence and the precise source dependencies used in this review.

Version 1 was frozen as a production-only review immediately before the final fixture pins arrived. It remains unchanged and unselected. Version 2 adds only the final fixture review and evidence pins. Production proof sources remain unchanged.
