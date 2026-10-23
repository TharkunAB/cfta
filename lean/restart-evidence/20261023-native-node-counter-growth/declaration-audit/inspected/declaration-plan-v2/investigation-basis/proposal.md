Proposed next component: native node-counter growth on the same actual Outcome.state.
Use three public results for step, finite execute, and resume. No private helper or new definition is needed.
For step and execute, compare the input state.machine.heap.nodes.next with the same projection of the actual outcome.
For resume, compare the supplied outcome.state projection with the actual resumed outcome.state projection.
Parameters are arbitrary width, Symbol, Guard, result type, emptyGuard, conjoin, code/state or outcome/fuel.
The only type-class premises are the existing DecidableEq Symbol and DecidableEq (EdgeKey Symbol Guard).
No Valid, Good, Available, dense-cache, successful-run, readiness, callback, or desired counter bound is supplied.
All yielded, done, failed, and blocked outcomes are included; the original full state and code are used.
Use existing public node_step_machine and edge_step_machine to avoid all new lookup/demand inversions.
Both helpers include absent, busy, ready, evaluate and direct node selection without a validity premise.
Finish and advance have public definitions with exact machine projection; no finish_machine or advance_machine theorem was found.
The Work branch uses the node component of run_next, whose reservation count is a natural number.
The optionalBinder branch uses H34 maybeMu_mono on the actual heap, then splits its done/pending outcome.
Constructor pending can increase the counter before blocking. Do not treat blocked outcomes as unchanged heaps.
Pure, fail, domain entry, read, finishNode and finishEdge leave the physical heap counter unchanged.
Finite execute uses fuel induction generalized over code/state. Yielded composes step bound with the induction result.
The done, failed and blocked cases retain the one-step bound. Zero fuel returns the same state.
Resume uses the execute result only for yielded; its other three tags retain their supplied state.
Minimal import pair: H34 StoredNodeCounterGrowth and NativePrefixCoverage. Exact public routes are pinned.
Use fully qualified Native.step/execute and NestedConstruction.Outcome.state in proof simplifier lists.
Estimated source: context/docs 12–18, step 40–50, execute 25–32, resume 12–16, close 2 lines.
Whole estimate is 91–118 ordinary lines; allow target 95–130 and hard 160 only after exact declaration review.
No whole-native node-counter theorem was found in the targeted Native/Thunk scan or exact projection search.
This is operational input-to-output growth. It does not derive fixed inventory source-to-input counter order.
It does not add upper bounds, source Room, WordRanges, allocation Trace, heap validity, result semantics or successful completion.
Scan/H23 transport, generated-source resources, Mu/public pass, Haskell correspondence and convergence stay separate.
H34 is installed and its actual proof checks passed; this next component has no declarations, body or compiler evidence.
Arity authored H33/H34 declarations and their verifier tools. Root authored the H34 mathematical body.
This investigation checks live public API correspondence. It is not an independent reproof of those foundations.
