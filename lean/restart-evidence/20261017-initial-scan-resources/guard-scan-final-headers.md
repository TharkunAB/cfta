# Final root adapter headers

## lean/MicroCFTA/SourceCurrentGateGuard.lean — primary

```lean
124: theorem primary (annotation : Guard → Prop) (unconstrained reaches : Value Symbol Guard → Bool)
125:     {values : List (Value Symbol Guard)} {paths : EqualityNormalize.Class}
126:     {before after : State Symbol Guard} {answer : Bool}
127:     (actual : EndpointStatefulGateTrace.ClassTrace unconstrained reaches values paths before answer after)
128:     (semantic : SemanticReady before) (costs : CostHeap before)
129:     (available : InternedNestedProvenance.Values before values) (guards : Heap annotation before) : Heap annotation after :=
```

## lean/MicroCFTA/SourceCurrentGateGuard.lean — secondary

```lean
210: theorem secondary (annotation : Guard → Prop) (unconstrained : Value Symbol Guard → Bool)
211:     {values : List (Value Symbol Guard)} {paths : EqualityNormalize.Class}
212:     {before after : State Symbol Guard} {answer : Bool}
213:     (actual : SourceCurrentSecondaryTrace.ClassTrace unconstrained values paths before answer after)
214:     (semantic : SemanticReady before) (costs : CostHeap before)
215:     (available : InternedNestedProvenance.Values before values) (guards : Heap annotation before) : Heap annotation after :=
```

## lean/MicroCFTA/SourceCurrentGateFrameResources.lean — forecast

```lean
32: def forecast (paths : Class) (profile : Profile) : Profile :=
```

## lean/MicroCFTA/SourceCurrentGateFrameResources.lean — forecast_ge

```lean
37: theorem forecast_ge (paths : Class) (profile : Profile) : Le profile (forecast paths profile) := by
```

## lean/MicroCFTA/SourceCurrentGateFrameResources.lean — forecast_mono

```lean
44: theorem forecast_mono (paths : Class) {first last : Profile} (increase : Le first last) :
45:     Le (forecast paths first) (forecast paths last) := by
```

## lean/MicroCFTA/SourceCurrentGateFrameResources.lean — workerFuel

```lean
51: def workerFuel (paths : Class) (profile : Profile) : Nat := classFuel paths (scalar profile)
```

## lean/MicroCFTA/SourceCurrentGateFrameResources.lean — workerFuel_mono

```lean
54: theorem workerFuel_mono (paths : Class) {first last : Profile} (increase : Le first last) :
55:     workerFuel paths first ≤ workerFuel paths last :=
```

## lean/MicroCFTA/SourceCurrentGateFrameResources.lean — primary

```lean
61: theorem primary (formulas : SourceGuards.Formulas FullSyntax.Formula)
62:     (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
63:     (unconstrained reaches : Value Symbol Guard → Bool) (values : List (Value Symbol Guard))
64:     (paths : Class) (before : Checked width) (frame : Frame formulas solver inventory before)
65:     (profile : Profile) (fits : Fits profile before) (available : Values before.native.machine.heap values) :
66:     ∃ answer heap,
67:       EndpointStatefulGateTrace.ClassTrace unconstrained reaches values paths before.native.machine.heap answer heap ∧
68:       Frame formulas solver inventory (advanceHeap before heap) ∧
69:       Fits (forecast paths profile) (advanceHeap before heap) ∧ Values heap values ∧
70:       SourceCurrentConjunctionRowsAllocation.Effects (SourceCurrentAllocatedNativeEffects.physical before)
71:         (SourceCurrentAllocatedNativeEffects.physical (advanceHeap before heap)) ∧
72:       ∀ fuel, workerFuel paths profile ≤ fuel →
73:         SourceCurrentMuEndpoint.classMeets true unconstrained reaches fuel values paths before.native.machine.heap =
74:           .done (some answer) heap := by
```

## lean/MicroCFTA/SourceCurrentGateFrameResources.lean — secondary

```lean
92: theorem secondary (formulas : SourceGuards.Formulas FullSyntax.Formula)
93:     (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
94:     (unconstrained reaches : Value Symbol Guard → Bool) (values : List (Value Symbol Guard))
95:     (paths : Class) (before : Checked width) (frame : Frame formulas solver inventory before)
96:     (profile : Profile) (fits : Fits profile before) (available : Values before.native.machine.heap values) :
97:     ∃ answer heap,
98:       SourceCurrentSecondaryTrace.ClassTrace unconstrained values paths before.native.machine.heap answer heap ∧
99:       Frame formulas solver inventory (advanceHeap before heap) ∧
100:       Fits (forecast paths profile) (advanceHeap before heap) ∧ Values heap values ∧
101:       SourceCurrentConjunctionRowsAllocation.Effects (SourceCurrentAllocatedNativeEffects.physical before)
102:         (SourceCurrentAllocatedNativeEffects.physical (advanceHeap before heap)) ∧
103:       ∀ fuel, workerFuel paths profile ≤ fuel →
104:         SourceCurrentMuEndpoint.classMeets false unconstrained reaches fuel values paths before.native.machine.heap =
105:           .done (some answer) heap := by
```

## lean/MicroCFTA/SourceCurrentSeededCallerNumeric.lean — of_receipt

```lean
32: theorem of_receipt (formulas : SourceGuards.Formulas FullSyntax.Formula)
33:     (solver : SourceGuards.Entailment FullSyntax.Formula)
34:     {inventory next : Inventory} {before : Caller width} {after : Checked width}
35:     {value : Value Symbol Guard} {memos final : Memos}
36:     (initial : Context formulas solver inventory before memos)
37:     (receipt : SourceCurrentConstrainedCapSeededNumeric.Receipt formulas solver next before.checked value after memos final) :
38:     Post formulas solver next before (advance before after before.fourth before.merge) final := by
```

## lean/MicroCFTA/SourceCurrentSeededCallerNumeric.lean — complete

```lean
49: theorem complete (formulas : SourceGuards.Formulas FullSyntax.Formula)
50:     (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
51:     (unconstrained : Value Symbol Guard → Bool) (anchor : State Symbol Guard)
52:     (anchorSemantic : SemanticReady anchor) (anchorReady : GateReady anchor)
53:     (values : List (Value Symbol Guard)) (paths : List (List Int)) (before : Caller (bits + 2))
54:     (memos : Memos) (initial : Context formulas solver inventory before memos)
55:     (frame : Frame formulas solver inventory before.checked) (profile : Profile) (fits : Fits profile before.checked)
56:     (available : Values before.checked.native.machine.heap values) (growth : Grows anchor before.checked.native.machine.heap)
57:     (supported : ∀ path ∈ paths, PathSupport unconstrained anchor path values)
58:     (proper : ∀ path ∈ paths, path ≠ []) (reserved : SeededReserved bits values.length paths profile) :
59:     ∃ result after next final,
60:       ∃ actual : SourceCurrentAllocatedSeededQuery.Seeded values paths before.checked result after,
61:       SourceCurrentAllocatedSeededMemos.SeededReads actual memos final ∧
62:       SourceCurrentConstrainedCapSeededNumeric.Receipt formulas solver next before.checked result after memos final ∧
63:       Post formulas solver next before (advance before after before.fourth before.merge) final ∧
64:       Fits (finalProfile values.length paths profile) after ∧
65:       (paths ≠ [] → SourceCurrentAllocatedSeededLanguage.Includes formulas solver values paths result) ∧
66:       (advance before after before.fourth before.merge).nodeResults = before.nodeResults ∧
67:       (advance before after before.fourth before.merge).edgeResults = before.edgeResults ∧
68:       (advance before after before.fourth before.merge).fourth = before.fourth ∧
69:       (advance before after before.fourth before.merge).merge = before.merge ∧
70:       SourceCurrentAllocatedSeededWorker.seeded
71:         (fuel values.length paths profile) (fuel values.length paths profile) (fuel values.length paths profile)
72:         values paths before.checked = .done result after ∧
73:       (∀ projection reader native, fuel values.length paths profile ≤ projection →
74:         fuel values.length paths profile ≤ reader → fuel values.length paths profile ≤ native →
75:         SourceCurrentAllocatedSeededWorker.seeded projection reader native values paths before.checked = .done result after) := by
```

## lean/MicroCFTA/SourceCurrentGeneratedQueryFrameResources.lean — Receipt

```lean
32: structure Receipt (profile : Profile)
33:     (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
34:     (inventory : Inventory) (fuel : Nat) (left right : Value Symbol Guard) (before : Checked width)
35:     (value : Value Symbol Guard) (after : Checked width) (memos : Memos) : Prop where
36:   /-- The actual return has exact intersection language and global memo laws. -/
37:   query : SourceCurrentAllocatedTargetQuery.Receipt formulas solver inventory left right before value after memos
38:   /-- The same inventory and state admit the next query. -/
39:   frame : Frame formulas solver inventory after
40:   /-- The instruction count belongs to this exact physical trace. -/
41:   trace : SourceCurrentAllocatedNativePhysicalTraceCompletion.Trace fuel
42:     (.code (requestNode IntersectionEmptyDomain.emptyDomain left right)) before (.code (.pure value)) after
43:   /-- The initial profile bounds the literal trace length. -/
44:   count : fuel ≤ instructionBound profile.nodes profile.edges profile.mass
45:   /-- The initial computed fuel returns the same complete state. -/
46:   done : execute (instructionBound profile.nodes profile.edges profile.mass + 1)
47:     (.code (requestNode IntersectionEmptyDomain.emptyDomain left right)) before = .done value after
48:   /-- The complete returned state fits the initial one-query forecast. -/
49:   fits : Fits (SourceCurrentAllocatedNativeResourceForecast.step profile) after
50:   /-- The returned payload fits the same initial mass schedule. -/
51:   mass : InternedValueMass.value value ≤
52:     massAfter (instructionBound profile.nodes profile.edges profile.mass) profile.mass
53: 
```

## lean/MicroCFTA/SourceCurrentGeneratedQueryFrameResources.lean — complete

```lean
102: theorem complete (profile : Profile)
103:     (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
104:     (inventory : Inventory) (before : Checked (bits + 2)) (frame : Frame formulas solver inventory before)
105:     (fits : Fits profile before) (room : Room bits profile)
106:     (left right : Value Symbol Guard)
107:     (leftAvailable : Available before.native.machine.heap left) (rightAvailable : Available before.native.machine.heap right)
108:     (leftClosed : left.free = []) (rightClosed : right.free = [])
109:     (memos : Memos) (valid : Valid before.native.machine.heap memos) :
110:     ∃ next fuel value after, Receipt profile formulas solver next fuel left right before value after memos := by
```
