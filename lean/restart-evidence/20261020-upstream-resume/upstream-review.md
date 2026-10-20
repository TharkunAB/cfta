# Upstream source review

Reviewed on 2026-10-20 at 15:05 CEST. Compare `184bba662` with incoming `9769fe3e921d63836a0be337f19edd3c601f076e`. The local import is `7ac4534cb`. This review covers ten changed paths: 488 inserted lines and seven deleted lines.

The import adds one executable library operation, `Data.CFTA.replaceRows`. It also adds one typed-ranking regression test and documentation. The production change to `Typing.hs` is documentation only. No Haskell production source, test, or Lean source was edited for this review.

## Persistent row replacement

`cfta/src/Data/CFTA.hs:161-171` applies all replacements and deletions to the persistent row map before validation. `Just row` adds or replaces a complete row. `Nothing` deletes a state. A deletion of a missing state has no effect. `Just []` keeps the state. The initial state stays unchanged. An empty edit map returns the original automaton.

`validateFTA`, at lines 173-206, checks the initial state, then dangling children, then consistent symbol arities. These are the previous `mkFTA` checks in the previous order. `mkFTA`, at lines 144-150, still concatenates duplicate input rows before validation. To compare an update with a fresh construction, pass the edited map to `mkFTA`; do not append replacement rows to the old input list.

Rows retain transition order, duplicates, annotations, and unreachable declarations. The operation does not normalize constraints, run a solver, or reuse generator indexes. The documentation correctly requires new indexes after an edit. Untouched persistent rows can remain shared, but validation scans the complete resulting graph. No concrete runtime defect in `replaceRows` was established by this source review.

There is no committed `replaceRows` test in either test tree. `docs/updating-languages.md:55-80` reports a separate 76-batch check and benchmarks. Those are upstream reports. This review did not execute those checks, the added regression test, or any package suite.

## Source-level size-order documentation issue

`cfta-generator/src/Data/CFTA/Gen/Typing.hs:78` and `cfta-generator/README.md:120-121` state that `Binders` generators already have size-major ranks. The actual dispatch depends on the imported graph, not on the `Bound` constructor. `fromTypingRules` calls `fromConstructorAutomaton` at `Typing.hs:289-291`; the latter imports the graph at line 474. `Internal/Flat.hs:105-111` selects the finite implementation when `numNestedMu` is zero. `Internal/Automaton.hs:279-282` orders distinct finite row symbols by arity and constructor key. `Typing.hs:483-489` gives the declaration-order keys.

A `Binders` grammar can have no recursive `subterm` fields and therefore be acyclic. A candidate that respects the documented field interface is:

```haskell
data Payload = P Payload | Z
data T = A Payload | B Int
-- Binders 0, with these two rules:
rule (ANode (value (P (P Z)))) Only
rule (BNode (value (0 :: Int))) Only
```

Both root constructors have arity one. `A` precedes `B` in the declaration. Their terms have sizes four and two. The source path predicts the larger `A` term before `B` in the finite generator. `upToSize 4` should reorder them. `Internal/Recur.hs:525-545` explicitly distinguishes finite reranking from cyclic size counting.

This candidate is NOT a runtime-validated counterexample. Do not report an executable ordering failure. A fresh-toolchain check is needed before an external repair. The proposed documentation correction is to qualify the claim by actual cyclic import, rather than by `Binders` alone. The existing `Binders` constructor documentation at `Typing.hs:243-249` has the same unconditional cyclicity claim.

The first illustrative candidate used `value` for the language's own datatype. It was rejected before execution because `Typing.hs:205-207` requires `subterm` there. All archived attempts use the corrected external `Payload` and `Int` fields.

## Temporary repro status

The exact source is `upstream-review-binders.source.hs.txt`. The executable, temporary source modules, and compiler outputs remain under `/tmp/mcfta-upstream-binders-20261020`. The current `Typing.hs` was copied there and compiled explicitly against cached libraries. No package or dependency build was started. Nix substitutes and builders were disabled for attempts 2-7. All jobs ran in the project `nix-shell` through the required four-GiB, five-minute cap. Each effective receipt records max/high 4294967296 and swap zero.

Seven terminal attempts are retained:

| Attempt | Exit | Observed result |
| --- | ---: | --- |
| binders-1 | 1 | `nix-shell` rejected `--offline` before GHC. |
| binders-2 | 1 | The default GHC package environment selected an older installed API. |
| binders-3 | 1 | Legacy exposed `microcfta` packages made imports ambiguous. |
| binders-4 | 1 | A direct package flag selected text 2.1.4, but the cached library uses 2.1.3. |
| binders-5 | 1 | Exact dependency IDs compiled both modules; the Nix linker could not find GMP. |
| binders-6 | 1 | Host GCC required a non-PIE link for the cached objects. |
| binders-7 | 134 | Linking succeeded; the executable aborted with `stack smashing detected` before rank output. |

The final abort is an unresolved cached-toolchain/runtime blocker. It does not establish a production defect, an ordering result, or a cause for the abort. No job remains live. The artifact verifier checks preserved bytes and cap receipts; PASS is not a successful repro result.

## Other documentation and test scope

The added `TypingSpec.hs:434-454` regression checks finite arithmetic reranking, cardinality preservation, rank round trips, and sizes five and fourteen. It does not establish the unconditional `Binders` claim. This review did not run it. The symbolic-counting caveat at `Typing.hs:80-83` remains relevant: a finite symbolic import can count a whole term as one atom. Exact structural size queries use `Data.CFTA.Sized`.

`docs/language-levels.md:3-5` marks its document, file, checkpoint, and edit interfaces as planned. The import does not implement a portable language document or checkpoint API. `CONTEXT.md` adds domain terms; it does not add executable behavior.

## Lean coverage

`lean/MicroCFTA/FTAValidation.lean:171-184` models row validation and duplicate-row construction. `validateRows_exact` at line 200 and `mkFTA_exact` at line 229 describe those checks. This remains consistent with the copied validation code. No `replaceRows` model or batch-update proof was found. Existing immutable native node edits model a different operation.

A useful next theorem would model the edited explicit row map, prove validation soundness, preserve untouched rows, and distinguish state deletion from an empty row. It should compare with `mkFTA` on the edited map. Pointer sharing is a separate runtime property. Existing `SourceSizedQueries` rank and prefix theorems concern their modeled size-class interfaces; they do not establish full correspondence for the Haskell typed generator wrapper. The import adds no whole-library correctness or completion proof.
