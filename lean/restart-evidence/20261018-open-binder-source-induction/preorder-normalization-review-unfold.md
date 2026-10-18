# Independent review of retained-Mu finite unfolding equations

Date: 2026-10-18 13:15 CEST. Read-only review. No Lean build was added.

Reviewed source:
`lean/MicroCFTA/SourceCurrentRetainedMuFiniteUnfoldEquation.lean`, SHA-256
`7e97e3df05319f36869e6acfe6845e9a6647be92165fedadc6c5dc65e25c4be2`.

No material issue was found.

`finite` takes an actual installed record, its earlier `Writer`, initial
`Ready`, and the corrected immediate-body `BodyIH`. The publication adapter
constructs both stored calls and exact growth. The first call is literally
the repaired Mu unfold at the original reader. The open unfold law then
composes with the finite reconstruction relation at that same reader.
Physical Empty agreement applies to the two reconstructed outputs. It is
not asserted between the Mu and its unfolding.

`all_depths` constructs one actual pair of calls at depth zero. Each other
finite application has the same deterministic unfold equation and then
the same deterministic ordinary reconstruction equation. Outcome
injectivity identifies the returned values. Its lowering step is valid
because each application proves one extra observation depth. No reader
growth transports a `Same` claim.

The `node` corollary derives the actual writer-to-reader `Keeps` from the
provided Ready and the exact Writer growth and issued extension. It uses
the actual source shape and indexed strict children at depth count plus
one to derive `BodyIH`. It then invokes `finite`. It does not assume a
whole-parent output relation or an unrelated all-smaller-grammar law.

The strict source induction hypotheses remain explicit. The module does
not prove unrestricted nested-binder alignment, arbitrary-view source
alignment, general completion, or an initial-query source ancestor claim.
Writer alone is not treated as installed membership; `selected` remains
an explicit actual physical record premise.
