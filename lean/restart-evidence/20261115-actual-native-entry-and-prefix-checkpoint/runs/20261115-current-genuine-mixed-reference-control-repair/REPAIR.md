# Proof-only alias repair

UNCOMPILED. This packet has no theorem credit.

The original raw candidate is unchanged. Its public theorem header and the original full coupled header are byte-identical in this repair. Every source, original-pattern, actual-entry, domain, continuation, and height assumption is unchanged.

The complete diagnostics report proof failures at lines 142, 144, 146, and 147. They also report unused simp arguments at those sites. Each failing simplification compares an expanded actual enter expression with a local entered alias.

Three explicit `change` steps fold definitionally equal expressions before rewriting:

1. Fold the full lookup fact to `lookup before.native.machine.heap entered.1.key entry.identity = some universeValue`.
2. Fold the reverse compileNode goal to the same local `entered.1`.
3. Fold the actual checked-step goal to the same local `entered.1` and `universeValue`.

The existing proofs then use the same membership, readback, actual selection, and checked-step equations. The repair adds no premise and changes no actual operation or endpoint.

The final invalid-import diagnostic comes from appending the old standalone PROBES file after the raw module. The repaired PROBES file contains only the axiom print command. Append it after the raw file, or import the checked module separately before running the probe. This probe correction does not affect the theorem.

The case scope is unchanged: all closed strict descendants exclude repeated in both orders. Literal ordinary-node descendants also get exact source rightReference/swap compilation and the real checked binding-read step. The reverse compiled request retains native memo traffic. The recursive producer, all-fuel history propagation, and whole A/M family remain open.
