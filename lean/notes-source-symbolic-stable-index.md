# Stable symbolic source ranks

`SourceSymbolicStableIndex.stable_source_index` gives one fixed distinct
index and one execution bound. Every later source cardinality equals that
index's size. Every later valid decode equals that index's decoder.
Every later accepted inverse query equals that index's encoder.
The index appears before the quantifier over execution bounds.

The proof does not assume stable fuel behavior. `allocated_total_api`
proves that each inverse query eventually has one fixed answer.
`finite_stabilization` combines these individual bounds over the finite
member list of an initial complete source index. The proof selects the
final index at the resulting bound. Every later inverse agrees with it.
The inverse and decode laws then force every later decoder to use the
same term order. The proof also covers an empty accepted language.

Each rejected finite term retains its own sufficient inverse bound.
The theorem does not claim one rejection bound for all possible terms.
It also does not claim a uniform bound across different source graphs.

The member list is a proof artifact. The Haskell symbolic decoder does
not construct it. The proof gives existence of an execution bound, not
a polynomial running-time bound or a practical bound calculation.
Overlap preprocessing can still require exponential work.

The source representation premises remain explicit. `CompiledRows`
records successful constraint compilation. `ClosedOperationRows` gives
the copied-row interface for intersection, conditioning, and projection.
This interface includes the reasons that permit row removal.
`AllocatedRows` supplies a finite allocation history for each observed
row. It does not supply one shared executed host-cache history for all
rows. These interfaces do not constitute complete Haskell verification.

Validation: `lake build MicroCFTA.SourceSymbolicStableIndex` succeeds
with the pinned toolchain. Both new theorem audits report only standard
Lean axioms. The module has no added axioms or incomplete proofs.
