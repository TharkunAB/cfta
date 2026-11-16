Status: UNCOMPILED. The earlier380-line candidate and its full failed diagnostics remain unchanged.

The finalizer-expression rewrite failed in both branches. The observed equation still matched the literal outer ChildDispatch tuple. This repair inserts ONLY `dsimp only at observed` after the successful singleton child/candidate cases and before the actual finalizer split. This reduces the outer literal match. It exposes the existing inner finalizer call for the unchanged none/some rewrites.

Both complete original headers330ffa3577780820f51c912601d335e850fbc8b1274d66783edb70db2d746199 and0ccee48e1aba565b25743713bdb7891904279109ce0bdeb411758764e4e9f3c4 are byte-exact. The entire finalized-child helper proof and appendable probes are byte-exact. No new logical premise, runtime fuel, checking cap, linter setting or original906/549 target is changed. All outcomes and output observers remain unchanged. No proof credit is claimed before Root's strict check.

Assembly: replace only the earlier380-line opaque append with this381-line append. Keep its original owner context and all other components once. No new import is required.
