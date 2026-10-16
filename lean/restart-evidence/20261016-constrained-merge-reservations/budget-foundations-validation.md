# Merge budget foundations validation

Frozen: 2026-10-16 20:20 CEST.

The new Numbers module has 94 lines. SHA256: `600d709f38e84985d8d2046875aec68461f329da99632981f7b8f09f854886df`.
The new Code module has 182 lines. SHA256: `2f4edb52a2e14d007dd52be4186ebb678d75361dc7f06f17759e52ae30aecf6c`.

Numbers implements the requested separate constructor request recurrences. At height zero both budgets are zero. At the next height, the recursive row parameter is squared. The module proves joint and individual row/arity monotonicity and height monotonicity. It does not estimate instructions, comparisons, or host evaluations.

`Budget before after nodes edges` contains an actual `ConstructorWorkTrace.Trace` with its literal ordered observed request list. Counts inspect those requests. They are not counter differences. Reflexivity records an empty trace. Composition appends both traces at their exact common heap. Monotonicity changes only the allowed counts. `Budget.next_le` derives supply bounds from the trace.

The literal Work helpers record at most one node request for `makeNode`, and one edge request for `makeEdge`. A filtered-empty node records no request. A cache hit still records a request. The reservation count can be smaller. No availability, successful whole-query, or returned state invariant is needed for these primitive count laws.

The request Contract combines the existing physical/profile contract with a universal input-profile budget between the same actual heaps. The instruction predicate is the existing Effects certificate with that stronger contract. Structural lifting retains existing profile or physical certificates. It introduces no recursive execution law.

The map theorem accepts variable node and edge costs for each request. Each local call certificate records its own starting heap. Bind composes those budgets at the actual returned heap. The result contains the sum of the per-request costs and position-aware `Language.All₂`. Only physical preconditions and result relations grow through later effects. The proof never grows a Budget as an annotation without adding Work.

Validation:

- `merge-budget-numbers-direct-2.log`: exit 0, no warnings. Direct1 retains the rejected external Mathlib import. The final source imports the existing project module.
- `merge-budget-code-direct-1.log`: exit 0, no warnings.
- Root-owned canonical targets: `budget-numbers-build-1.log` and `budget-code-build-1.log`, 157 and 1131 jobs respectively, completed successfully. Only the historical dependency warning remains. This agent ran no Lake process.
- `budget-foundations-public-1.log`: 29 public full-signature and axiom pairs, exit 0, no warnings or `sorryAx`.
- `budget-foundations-kernels-2.log`: four imported theorem/axiom pairs, exit 0, no warnings or `sorryAx`. Kernel1 retains an unused-instance warning; an explicit omit removes it in the final source.

The integration kernels compute the nontrivial squared-row expansion at rows 2, arity 3, height 2 as node budget 85 and edge budget 26; check the zero-height and nullary cases; certify a mixed three-request map with separate costs and exact output multiplicity; construct two actual repeated edge Work steps with two requests but at most one reservation and exact warm replay; and apply a request's universal budget to its own original profile.

All direct commands use pinned Lean 4.34.1 with `LEAN_PATH=lean/.lake/build/lib/lean`. Public and kernel checks import the canonical modules. Temporary direct oleans were removed after canonical validation. No older source or evidence file changed.

The Body and mutual actual Run/Call resource producer remain separate proof components. These foundations alone prove no whole-Merge budget or finite return. Source lazy publication, concurrent losing candidates, host scheduling, cumulative Target/Shared/class/outer capacity, and runtime correspondence remain separate boundaries.
