# Actual initial identity prefix: proof repair v2

Status: UNCOMPILED. Root's first actual strict check failed. It has no proof credit. The complete instrumented source, complete16733-byte diagnostic and original source-only draft remain retained under separate pins.

Lean4.34 treats `prefix` as a reserved token. The candidate renames the local binding and both uses to `prefixRun`. It does not change the theorem name or statement.

The checking simp leaves two goals. The false case is the evaluation of `pure false` on the initial core. The true case is the evaluation of the representative get/set/bind sequence and the empty ancestry test. Both use the same original initialized core. The initial forest already contains root0. A fuel1 representative read returns that root and the identical forest. The empty recursion ancestry contains no key, so the check does not write a repeated state. No semantic mismatch was found. No replacement checked state or boundary-clear premise is needed.

The candidate adds `<;> rfl` after the existing checking simp to close those definitional reductions. This repair is still a source-only proposal. Root must check it. Remaining parse errors from the first run may have hidden later proof errors.

The ENTIRE original prefix through the complete theorem header and `:= by` is byte-identical. This includes imports, namespace, aliases, local instances, every hypothesis, all initializer receipt fields, both prefix branches and the exact selection implication. The remainder changes only the four proof lines described above. Exact forward patch replay reproduces the candidate. Exact reverse replay restores Root's pinned instrumented original.

The original actual diagnostic prints sorryAx because Lean inserted error placeholders after the failed proof. The candidate adds no sorry, admission or axiom. No checking or theorem credit is inferred from the failed axiom print.

No live source write, compiler, evaluation, Haskell, Git or board action ran. No Haskell fix arose. The earlier original draft owner remains sealed and unchanged.
