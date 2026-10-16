# Checked target projection validation

Source: `lean/MicroCFTA/SourceCurrentConjunctionTargetProjection.lean`.
Frozen SHA256: `577020368ab039941637724b2541221483390598542b14da355a3e1a92c2eccb`.
Source length: 126 lines. The frozen copy has identical bytes.

Pinned toolchain: Lean 4.34.1 at `/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lake`.

The focused canonical build passed with terminal status 0 and 1256 jobs. `projection-build-2.log` records the result. Its only warning is the existing unused `inputs` warning in `InternedFreshOrdinaryClosedCompletion`. The first build records a local continuation indentation error. No old proof was changed.

Direct Lean validation passed with terminal status 0. It checked all three public theorem axiom reports and all four public signatures, including the receipt type. Four named integration kernels have their own axiom reports and full signatures. The final log therefore has seven axiom reports and eight signature checks. All axiom reports use only `propext`, `Classical.choice`, and `Quot.sound`. The final log has no errors, warnings, or `sorryAx`. The first two probe logs preserve failed evidence-only proofs of a nonempty mapped path. The final probe uses the ordinary list simplifier and has no placeholder axioms.

The kernels establish these integrations:

- `current_fields` constructs a finite projection and derives field loads at the unchanged initial operation cache. Both warm native tables remain exact.
- `required_selected` obtains the selected domain from an actual current Required receipt. It derives closed output and selected-subterm inclusion. It does not require the captured forest closed.
- `sequential` runs two actual projections in order. It threads one inventory and the actual global memo return. It retains exact operations, both query tables, and all prior unfolding entries.
- `root_union` constructs the root projection and derives exact union language. Its root domain requires the original values closed, as the source root branch reads all operands.

The public completion premises are initial checked Ready, initial inventory At, original forest availability, the selected ForestClosed domain, and initial global validity. Completion derives the actual Forest graph, stable finite worker bounds, physical Effects and Extension, final Ready and At, exact native tables/domains/operations, closed resident output, and the same graph's global receipt. It requires no native WordRanges, successful future call, future field load, model-validity callback, or old native Step.

Proper paths preserve selected-subterm inclusion. They do not have equality with selected subterms of accepted original terms because projection discards ancestor guard tests. The empty path has exact union language. Same-cache merge construction, target folding, leaf narrowing, class edits, and runtime demand/publication remain outside this module.
