# Reservation validation

Validated at 2026-10-16 18:17 CEST.

Source: `lean/MicroCFTA/SourceCurrentAllocatedFiniteOrdinaryReservations.lean`. SHA256 `60fd0c927d22dfb9db9a4a776383077c87040c7e81b299a8f998905f8a9618e2`. The source has 228 lines.

Direct pinned Lean compilation passed with exit 0 and no warnings in reservations-direct-4.log. Failed direct logs 1 through 3 remain. The canonical dependency build passed with exit 0, 1307 jobs, in shared-reservations-build-2.log. Root owned that build. Only the existing InternedFreshOrdinaryClosedCompletion unused-input warning occurred.

The imported public probe passed with exit 0 in reservations-public-1.log. It checks all 29 declared public types, constructors, functions, and theorems with full explicit signatures and axiom reports. The imported integration probe passed with exit 0 in reservations-kernels-3.log. It checks four theorems: repeated actual constructors, filtered node output, losing same-key atomic candidate, and generic warm replay with retained issued histories. Earlier failed kernel logs remain. The final probes have no errors, warnings, or sorryAx. The only foundations are propext, Classical.choice, and Quot.sound.

Commands used the pinned toolchain `/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean` and `LEAN_PATH=lean/.lake/build/lib/lean`. Direct source compilation used `-o /tmp/SourceCurrentAllocatedFiniteOrdinaryReservations.olean`. Imported probes used no output artifact. No Lake, Git, Haskell build, or network action ran from this task.
