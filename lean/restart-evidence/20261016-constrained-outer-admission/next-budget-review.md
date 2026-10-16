# Next proof: an input-derived reservation budget

Reviewed 2026-10-16 18:46 CEST. OuterAdmission now derives the old outer range plan from initial admission and numeric reached-entry plans. The next resource theorem must derive those numeric plans. It must not assume the complete root execution or a bound on the request list from that execution.

The existing count layer is exact but not yet a static reduction budget. `FiniteOrdinaryReservations.run_next` records actual Work misses (`:133`). `run_next_le` bounds them by actual Work requests (`:161`). `AtomicTrace.next_exact` counts every reservation, including a candidate that loses publication (`:60`). `QueryReservations.prefix_counts` and `.prefix_bounds` cover arbitrary finite yielded native prefixes (`:103`, `:121`). `capacity_after` still requires bounds on the actual prefix request count (`:132`). Thus it cannot by itself remove the reached-capacity premise. `ConstructionReservations.nodeCount/edgeCount` are genuinely static syntax bounds (`:47`, `:50`), and `InitialCapacity.prepared` derives capacity at the initial constructed root (`:62`). Initial capacity does not bound later target query entries.

Height alone is insufficient. A height-one node can have arbitrarily many rows. A row can have arbitrarily many children. Guards can contain arbitrarily many classes and paths. The input resource profile must therefore retain node and row occurrences or resident operand inventories, maximum row width and arity, class count, path count and path lengths, and inherited equality payload size. Repeated source positions count even when physical nodes share an identity. Query products can multiply row counts. Class edits can repeat a traversal with a newly generated forest. Target slots avoid repeated target construction within one class, but they do not avoid every leaf intersection, and a later class clears those slots.

The smallest useful next module is `SourceCurrentAllocatedFiniteOrdinaryNativeBudget.lean`. Define a finite, independently computed operand inventory for one fixed initial query source. Prove that every finite literal query prefix requests only node pairs and edge pairs from that inventory, at the exact empty domain. Then prove that a pair can start its producer at most once during that sequential query. Warm returned hits make no new producer. A suspended warm cell can start once. Busy observations cannot produce a successful body. Use the literal compiled node and checked-edge branches to bound constructor Work requests per producer. The generic WordExecution certificate permits arbitrary safe Work; it alone does not supply a constructor-count bound. Do not publish a pair-count formula until these exact producer cases have been counted.

The intended public shape is:

```lean
def queryBudget (sourceOperands : OperandInventory) : Nat × Nat

theorem node_prefix_budget
    (initial physical and operand-domain facts)
    (actual : Steps fuel
      (.code (requestNode emptyDomain left right)) before next after) :
    nodeRequests (requestsThrough fuel ... before) ≤ (queryBudget operands).1 ∧
    edgeRequests (requestsThrough fuel ... before) ≤ (queryBudget operands).2
```

Here the budget is computed before the query. The theorem quantifies over every finite prefix and needs no successful result, final Ready, completed child callback, or supplied actual-request bound. Combine it with `prefix_bounds` and initial supply plus budget fitting the two key layouts. This derives capacity at every such prefix. Prove the edge analogue at the same time. Count Empty explicitly in the node operand inventory, and retain the fixed empty-domain restriction. A key universe that silently allows arbitrary seen histories is too large and changes the current domain theorem.

Then add separate static bounds for required-path rebuilding, projections, completed merge bodies, and raw edit constructors. `makeEdge_next` and `makeNode_next` already supply the one-request primitive bounds (`Reservations.lean:200`, `:218`). Merge grouping and native row products need output row/arity envelopes in addition to NodeNarrow height. Compose these envelopes in the literal operand, target, leaf, compiled edit, class right fold, precheck, and outer schedules. Each suffix uses the worst-case envelope derived from the earlier input profile. A total root budget can be very large; it must remain a computed function of the original profile and initial warm supply counters. Extracting an existential budget from an already completed graph would not establish this result.

Keep resource families separate. Current Capacity bounds only constructor node and edge supplies. Equality interner identities, native and outer thunk handles, global memo storage, retained loser candidates, and source machine Int or Word overflow need their own statements or explicit runtime adapters. The sequential counted Work model does not bound unrelated host interleavings or repeated lazy evaluations. Finite ordinary structure and full guards remain the current scope. General recursive structures and arbitrary repeated outer reductions remain separate. No Haskell source changed; any later repair must first enter root FINDINGS.
