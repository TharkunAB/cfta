# Deep path fixture review

Reviewed on 2026-10-19 at 12:48 CEST.

The source builds one event wrapper around a two-row ordinary node. The
first child is finite. The second child is a used Mu. Source construction
derives SemanticReady, CostHeap and availability. The actual projection
selects path [0]. Its selected outer row index is 1. Its Mu operand read
index is 0. The complete physical row is retained.

The fixture calls ProjectionPathOrigins.project_read at the actual read
return. It then calls occurs with the actual event child occurrence. This
proves PathOrigin at [0,0]. The selected row has symbol rec. The event row
has symbol event. origin_node therefore excludes an epsilon Origin at the
event root. This is a distinction between root and path origins. It is not
a whole-event projection receipt or a general renewal counterexample.

Selected strict attempt 5 has a literal empty log. The single constructed
public theorem has the same expanded statement as private checked_witness.
The full probe includes all eight options and the standard three axioms.
Attempt 1 stopped before Lean because the sandbox could not connect to the
systemd user bus. Attempts 2 through 4 retain elaboration diagnostics.
The final capped attempts record max/high 4 GiB and swap zero. The mutable
peaks file is excluded. The final five-row snapshot is immutable.

No production source, previous evidence, Git state or Haskell file was
changed by this component. It owns zero production declarations and one
constructed pair. The dependency canonical receipt is reused.
