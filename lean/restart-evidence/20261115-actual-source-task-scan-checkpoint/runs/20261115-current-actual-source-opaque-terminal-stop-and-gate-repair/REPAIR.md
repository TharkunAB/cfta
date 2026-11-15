# Proof-only stop, gate, and finalizer reduction repair

Status: UNCOMPILED. No proof credit.

The original213 and failed strict23558 diagnostics remain unchanged.

Seven stopped-output proofs now use explicit And constructor bullets. The inline tactic comma was parsed as an additional cases target.

The opaque gate proof unfolds the actual run, removes the known nonempty branch, and splits the actual ordinary selector. Its true branch contradicts the original dispatch equality. This avoids the unsuccessful simp rewrite across generated match definitions and removes exactly its unused simp arguments.

The successful-child branch first changes the goal to its literal finalizer match. The following actual finalizer cases therefore rewrite the same occurrence before applying completedResources. The previous case split occurred before the outer child match had reduced.

All current-resource callback and empty-rejection proofs are unchanged. The complete header4fb571d9, probes41d4134c, preamble, imports, original budgets, forecasts, endpoints, and caches remain byte-exact.
