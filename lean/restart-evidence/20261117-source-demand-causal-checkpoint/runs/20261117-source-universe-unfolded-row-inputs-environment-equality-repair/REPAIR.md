# Pointwise replacement environment equality

Status: FROZEN, UNCOMPILED.

This packet starts from Root's latest lambda-repair packet.
The public header 514c8cf3 and probes remain byte-identical.
The sole remaining conversion is inside the private selected_mu_execute proof.
A pointwise proof identifies the replacement function with the literal unfold environment.
The proof rewrites that function equality in the expected executor goal.
It then uses the same actual unfold equation.
All other proof bytes remain unchanged from the lambda repair.
All original failed packets and logs remain unchanged.
No premise, result, budget, operation, proof limit or linter setting changes.
