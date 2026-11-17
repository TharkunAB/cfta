# Explicit width for the depth-zero target

Status: UNCOMPILED. The first full check failed. This repair adds only `(bits := bits)` to the private zero theorem result. The original result leaves its width implicit and Lean cannot infer it from the configuration. The explicit width selects the already intended caller width `bits + 2`. No binder, premise, conclusion, runtime fuel, or checking limit changes.

The shared predicate body 5e4832cf is byte-exact. The zero proof and probes are byte-exact. The original header is retained and its change is recorded in HEADER-DIFF.patch. The new header is not claimed byte-exact to the original.
