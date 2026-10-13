# Historical semantic contexts and repaired constructor replay

`InternedFreshOrdinaryContext.Context` retains normalization, available
lexical values, and the new root-profile and free-name heaps. Full repaired
execution preserves this context through expression, child, edge, callback,
and reservation steps. The result includes pending outcomes.

`InternedFreshOrdinarySemanticOrigins.closed_origins` records that context
at the actual source call that produced each complete stored Mu. It keeps
the exact Depth callback, chosen ordinary callback, missing reservation,
and fresh-body callback. Later proof steps can therefore use the original
semantic facts without assuming them for a historical cache.

`InternedFreshOrdinaryCaptureBounds.origin_ordinary_free` uses those actual
callbacks to equate the complete Mu's ordinary free names with its stored
Depth observation's ordinary free names. `closed_capture_bound` proves
that each such name has a smaller level than the chosen ordinary probe.
The theorem applies to every completed record after a closed execution,
including records made by discarded computations and records retained
when the enclosing execution reaches a pending key.

`InternedFreshOrdinaryReplay.build_replay` proves exact successful replay
from the repaired syntax, cache validity, actual completion, and later
cache growth. It returns the same complete value and leaves the later
cache unchanged. The callback theorem also returns its exact normalized
observation. These proofs need no semantic heap or body equality premise.
They reuse only the generic ordinary and canonical-request replay lemmas.
The new ordinary choice is made from the exact replayed Depth record.

These theorems do not assert that first execution always completes. Strict
bounds on a returned record's free names do not, by themselves, bound every
name observed by an intermediate discarded computation. General repaired
completion and arbitrary callback substitution remain separate obligations.
