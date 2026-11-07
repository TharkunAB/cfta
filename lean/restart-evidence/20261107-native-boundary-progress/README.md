# Native generated-boundary progress observations

These are bounded observations of current Haskell execution. They are not a Lean termination theorem or a nontermination proof. No library Haskell source changed.

The checked source tree is d5a5e2a9d7c2ec59ded139b13f3864fe3a42e6a0. The existing library built in the project Nix shell with GHC 9.14.1 and -O0. The temporary shell adds pkgs.gmp. The first attempt without that package failed to link -lgmp before it ran the fixture. No project configuration changed.

RepeatedIntersectionGrowth.hs passes. Repeated intersection with one fixed factor changes the stored graph counts from (2,3,3) to (4,6,7) to (12,19,26). The fields are ordinary nodes, all physical nodes, and edges. The fixture also checks both results through actual reduceEdgeIntersection and checks closedness and distinct native IDs.

GeneratedBoundaryEnumerationTimeout.hs constructs a closed input with four ordinary nodes and seven edges. Its default runsInterned query does not return a first run within eight seconds in this environment. Construction has a separate five-second timeout and completes before the enumeration timer starts. Every p edge in both recursive bodies carries the same two equality classes: [0]=[1] and [0,0]=[1,0]. This is a valid structural input. No transfer to a concrete Specftacular or Synthesis caller is established.

The marked draft uses termsPruneWith and a callback that returns False and the same caller state. It records at most twelve events in an external diagnostic IORef and then throws an exception. It does not modify the core before that exception. This frontend uses canonical edge order; runsInterned uses stored edge order. They use the same enumerateFully' engine, but their exact branch order is not equated here. The observed prefix selects IDs 11, 71, and 234881. The first two selections have after-expansion events. The third has no after event before its eight-second timeout. Numeric IDs are process observations, not universal input bounds.

The observations do not establish infinite fresh IDs, the complete repeated-factor recurrence in this driver, eventual divergence, or a Haskell defect. They expose a concrete case that the original-input work proof must address. A stopping repair must preserve documented diagnostic Mu-marker behavior. Ignoring IDs needs a correspondence proof. Pruning every pending branch with no finite completion can remove expected results in EqualitySpec.hs757-763.

Reproduce from the repository root, serially:

```sh
env XDG_RUNTIME_DIR=/run/user/1000 DBUS_SESSION_BUS_ADDRESS=unix:path=/run/user/1000/bus CAPPED_UNIT=mcfta-native-boundary-progress HEAVY_PEAKS=/tmp/mcfta-proof-peaks.tsv /home/tritlo/Code/heavy-management/bin/capped --mem 4G --time 380 python3 lean/restart-evidence/20261107-native-boundary-progress/check.py
```

The checker builds the local library and records each command's output. An exit of zero means that the observation process completed. It does not mean that enumeration finished. observed.json records the exact source hashes and results. Timeouts depend on the host and build settings. Both new Haskell files passed fourmolu. cabal-gild checked cfta/cfta.cabal without changes. No full test suite or CI run is claimed. The packet contains no build archive.
