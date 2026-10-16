# Record-indexed Scan validation

The worker retains each selected original Record at its input occurrence.
It executes the same reached gate, projection, and decision calls as the
frozen path worker. It uses the same checked state, fourth memo, and Fault.
`scan_mapPaths` proves equality for the complete outcome at the same bounds.
A failed selection retains its original path tag and exact reached state.
The proof does not assume distinct paths or coherent records.

`scan_done_stable` proves successful monotonicity for all five stage bounds.
`scan_done_unique` identifies the stopped class, ordered Record list, complete
checked state, and fourth memo. The conjunction budget stays fixed.

Direct pinned Lean checks returned exit 0 for both source modules. The
public probe returned exit 0 with no warnings. It checks ten declarations
with axioms and signatures, including seven public theorems and three
executable definitions. Eight kernel examples cover empty input, selected
failure, distinct tries with equal paths, secondary skipping, early stop,
success projection, failure projection, and equality-operation retention.
All reported axioms are standard foundations. No sorryAx occurs.

This is a bounded serial interpreter. It proves no GHC demand order,
global event replay, general outer termination, or source extraction law.
The graph and positional Retained adapters are separate work.
No older proof or Haskell source was changed. This owner ran no Lake build.
