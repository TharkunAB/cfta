# Opaque fix self-application source candidate

Status: FIXTURE READY, NOT COMPILED OR RUN. No reachable-source failure or Haskell defect is established.

## Exact source case

Use the existing FirstOrder Library with singleton opaque groups:

- `fix :: forall b. (b -> b) -> b`
- `k :: forall a. a -> Int`

The query has no arguments and goal `Int`. The original program size is3 component leaves. There are no avoidance rules, argument-only groups, custom nodes, custom callbacks or early stop. Distinct source variable names a/b avoid the historical cross-component naming confound. Each use of fix still has an independent instance. The fixture evaluates no library component.

The candidate is `k (fix fix)`. A finite positive control of the SAME size is `k (k fix)`. Both go through the SAME library/query/size and stream. They do not filter or steer the worker.

For inner fix instances `(t -> t) -> t` and `(s -> s) -> s`, application forces `t -> t = (s -> s) -> s`. Arrow injectivity gives `t = s -> s` and `t = s`. Thus `s = s -> s`, impossible for finite type trees by height. Outer k adds no constraint that removes this equation: its quantified argument type can equal the inner result. This is a mathematical boundary, not evidence that the implementation emits the program. The positive control has a finite instance: choose fix's variable Int, inner k's argument type `(Int -> Int) -> Int`, and outer k's argument type Int.

## Actual source and execution chain

Synthesis.hs778-854 builds the real rawSearchSpace. Components are generalized with the actual recursive typesOf universe. Size3 splits positive source leaf budgets; it includes the nested application AST. The real application layout is at638-650 and keeps its three path classes. The outer ofType filter at654-656 ties the query Int to the program type. No ad hoc payload is introduced.

The public route is solutionsOfSize973-974 -> orderedSearchSpace775 -> reduceWithOrder718-719 -> programsIn969-970 -> Enumeration.runsBy1253-1256. The diagnostic reduced route reads the SAME reduced typed stream before erasing annotations/residuals. The raw route invokes runsBy(const0) directly on the genuine rawSearchSpace and bypasses only preprocessing. It uses the existing worker.

Enumeration.runsFrom1285-1294 initializes state297-311, then enumerateFully913-927 with no stop, no narrowing and a false oracle. The real worker is enumerateUntil'968-1014. Ordinary child traversal is enumerateEdgeWith769-781. Terminal endpoints725-753 merge UF and node domains. Mu/Union children with no terminal endpoint730-731 allocate a hole with an empty bucket; no descendant arrow traversal can be inferred from a rendered Mu marker.

## Actual rejection candidates, not a proven outcome

- assimilateUvarVal493-510 and mergeNodeIntoUVarVal516-525 reject literal Empty contents after actual intersections.
- intersectUVarValue204-218 additionally uses provablyEmpty only when the root's reachesConstrainedMu flag enables it. provablyEmpty true is rejection; false proves nothing. Its budget10000 is the existing implementation constant, not a fixture replacement.
- findExpandableUVars831-843 and nextExpandableUVar863-877 exclude classes named by suspended constraints. If every remaining expandable class is blocked, ExpansionStuck is rejected at978. This can reject a surviving proper type cycle. The exact fix/fix cache state is not known without execution.
- the repeated-key branch1003-1012 instead clears the selected recursive bucket and continues. Its key287-293 records native identity and a set of path tries. This branch is not a general occurs-check rejection.

The checked selected_clear_proper_cycle_unsatisfiable theorem152-183 protects an already present closed proper reference cycle across an actual selected clear, under Safe/Roots/correct waiting/flags and selection receipts. It does not say this candidate reaches that configuration, nor that every earlier discarded proper path is still present. It is relevant positive evidence, not an executed rejection guard for this case.

The emitter1057-1082 renders pending recursive boundaries as the supplied Mu marker. programsIn erases annotations and drops residual pairs. Therefore a matched public AST must be paired with its actual typed run/residuals and reviewed for the finite-type obstruction; a marker alone is not a native witness.

## Existing evidence searched

No exact `fix fix` or `k (fix fix)` case was found in current FINDINGS, lean/FINDINGS or source fixtures. Related retained BOUND and SKI probes report absence after exhaustion for bound self-application and `sink (s i i)` and include finite controls. The 20261115-source-occurs-fg-diagnostic records f g absent and a finite f f control accepted on its own source. These observations do not settle this different library/source/query. They remain immutable.

## What Root can conclude after running

Run one route per externally capped process. A target match reports its actual zero-based output index. Typed matches print ONE actual (term,residuals) pair together. A process timeout, crash, construction stall or observation cap gives no absence claim. Only observed list exhaustion reports absence. A public match with no matching typed observation still requires diagnostic follow-up; do not manufacture a trace.

If the candidate is emitted with the recorded same-source/same-run receipts, Root can investigate the exact original path equations, causal discarded bucket and no finite accepted completion, then record a verified defect in FINDINGS. This packet does not make that claim. If absent after exhaustion, it settles this case only. Distinguishing Empty, blocked selection, preprocessing and clear requires a Root-owned trace; the default oracle cannot see the clear branch because it bypasses callbacks.

Full scope remains one finite accepted completion of the SAME original emitted root under one assignment satisfying native domains, guards/residuals and all causal historical constraints. No OnlyU, future model, adequate-fuel, shallow legacy worker or independently chosen witness replaces that objective.
