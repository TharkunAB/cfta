# Checked edit success stability

Two additive modules are frozen:

- `SourceCurrentAllocatedSharedTargetWorkerStability`
- `SourceCurrentAllocatedSharedEditWorkerStability`

The shared target module proves successful force, native step, and leaf
monotonicity. It reuses actual target-worker success stability and actual
checked native success stability. A stored slot hit retains the whole input
state. A miss retains the same completed target and store operation. Leaf
uniqueness compares two successes at the coordinatewise maximum bounds.

The edit module proves successful execution stability under all six bounds:
edit recursion, projection, reads, merge work, selection, and native steps.
It follows the actual edit-fuel recursion. Head stability uses the actual
stored reader. Row work uses the same raw symbol, full guard, child list,
and returned heap before it enters the row suffix. No constructor work is
replaced by an identity or a different allocation schedule.

The generic child and row transport helpers require only preservation of
actual successful callback returns. The public concrete node, child, row,
list, and compiled-edit endpoints discharge that condition through the
edit-fuel induction. Those endpoints contain no callback, Ready, physical
input plan, language law, or future completion premise. They preserve an
existing success. They do not assert arbitrary-state completion. Concrete
uniqueness compares two supplied successes at maximum bounds. It identifies
the complete ordered output and shared state, including equality operations,
native tables, domains, target slots, and the completed merge memo.

## Validation

Toolchain: `/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin`.

```
LEAN_PATH=lean/.lake/build/lib/lean /home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean lean/MicroCFTA/SourceCurrentAllocatedSharedTargetWorkerStability.lean
LEAN_PATH=lean/.lake/build/lib/lean /home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean lean/MicroCFTA/SourceCurrentAllocatedSharedEditWorkerStability.lean
/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lake -d lean build MicroCFTA.SourceCurrentAllocatedSharedEditWorkerStability
LEAN_PATH=lean/.lake/build/lib/lean /home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean lean/restart-evidence/20261016-current-edit-worker/stability-public.lean
```

Final direct logs are `stability-target-direct-2.log` and
`stability-edit-direct-3.log`. Both returned exit 0 without warnings.
The root built the shared target dependency first. The focused edit build
returned exit 0 with 1296 jobs in `stability-build-1.log`. Its only warning
is the existing unused-input warning in
`InternedFreshOrdinaryClosedCompletion`. Handle 86563 reached terminal exit 0.
The canonical slot was released to the class-stability task.

`stability-public-1.log` returned exit 0 without warnings. It contains
18 public axiom checks, 18 complete signatures, and five external kernels.
All axiom dependencies are within `propext`, `Classical.choice`, and
`Quot.sound`. The kernels check zero-edit failure versus positive Empty
success, ignored child-list root leaves at zero bounds, the literal raw edge
then node constructor sequence, a ready target slot followed by actual
native success under larger bounds, and cross-bound equality of operations,
native state, slots, and merge memo.

Earlier direct logs retain elaboration-only draft failures. The final source
and probes contain no `sorry`. No source changed after the final checks.
No compiled artifact is retained in this evidence directory. No owned build
process remains. No older proof, Haskell source, Audit, or project document
was edited. Host forcing and runtime publication remain separate boundaries.
