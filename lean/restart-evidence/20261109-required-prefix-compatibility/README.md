# Required-path shape and actual output allocation compatibility

The packet checks the affected source frontier of this checkpoint.
It builds the complete Audit import target under the serial 4 GiB cap.
The frontier manifest records the exact source hashes and the DAG closure.
The Audit target checks the axiom dependencies of its imported theorems.
Each new module has its own strict source and public-declaration checker.

Reproduce under the existing heavy-management cap:

```sh
python3 lean/restart-evidence/20261109-required-prefix-compatibility/check.py
```

The check requires memory.max and memory.high of 4 GiB and no swap.
It sets LEAN_NUM_THREADS=1. It works from another current directory.
The checked.json file records the full result and the observed limits.

The source-audit.md file states the source retention and finite typing gaps.
It also records two small Haskell probes and their source inputs.
Those probes are separate observations. This compatibility checker does
not run them. They establish no public concrete-output defect.
No production Haskell behavior changes in this checkpoint.

This packet does not prove source-wide retention, source completeness,
one original-input execution bound, exact API order or complete Haskell
correspondence. Terminal endpoints can remain opaque. Partial output
preserves existing current-state models; it does not construct a model.
