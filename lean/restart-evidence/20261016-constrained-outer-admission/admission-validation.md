# Outer admission validation

Frozen 2026-10-16 18:46 CEST. Source145 lines, SHA256 `46f6e2f43e441eb7844284e4479dd06441cd67d385b699bd0eed7f9d3b273ede`.

Direct `admission-direct-1.log` exited 0 without diagnostics. Canonical `admission-build-1.log` passed 1539 jobs (root process10123), with only the historical unused `inputs` dependency warning. Three public declarations have full signature and axiom reports in `admission-public-1.log`. Three integration declarations have full signature and axiom reports in `admission-kernels-1.log`. Both final probe logs exit 0 with no errors, warnings, or `sorryAx`.

The public API is `step bits formulas solver one initial numericPlan`, `reach bits formulas solver reached initial numericPlan`, and `ranges bits formulas solver initial numericPlan`. Budget and entry indices are inferred. `step` covers all ten current entry transitions. `reach` permits the inventory and global bundle to change along the path. `ranges` derives the frozen raw-Reach range plan at every reached parent from its own derived admission facts. No old range plan or completed enclosing call is an input.

The first integration derives the old Plan and then constructs a finite literal node call with exact whole-state stable return, actual graph, strict reads, checks, Post, availability, structural tables, positional bound, and independent language law. It supplies no completed node or lower range callback. The other integrations derive admission and the old Plan for an actual row suffix after earlier edge and descendant graphs, and for an actual indexed walk suffix after its earlier node graph. They supply no strict reads or future state invariants for those prefixes.

The source and scope review preserve the finite ordinary and empty-seen restrictions. Numeric reached-entry capacity remains explicit. The new result closes the admission conversion; it does not derive a total static allocation budget. `next-budget-review.md` gives that next proof boundary. No older proof or Haskell source was edited. No Lake process was run by this task.
