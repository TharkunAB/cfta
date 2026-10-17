# Selected exact source headers

## lean/MicroCFTA/SourceCurrentMuEndpoint.lean — dispatch

```lean
16: def dispatch [DecidableEq (EdgeKey Symbol Guard)] (belowEnd : Bool)
17:     (unconstrained reaches : Value Symbol Guard → Bool)
18:     (recur : Path → Value Symbol Guard → State Symbol Guard → Outcome Symbol Guard (Option Bool))
19:     (path : Path) (value : Value Symbol Guard) (state : State Symbol Guard) : Outcome Symbol Guard (Option Bool) :=
```

## lean/MicroCFTA/SourceCurrentMuEndpoint.lean — nodeMeets

```lean
40: def nodeMeets [DecidableEq (EdgeKey Symbol Guard)] (belowEnd : Bool)
41:     (unconstrained reaches : Value Symbol Guard → Bool) :
42:     Nat → Path → Value Symbol Guard → State Symbol Guard → Outcome Symbol Guard (Option Bool)
43:   | 0, _, _, state => .done none state
44:   | fuel + 1, path, value, state => dispatch belowEnd unconstrained reaches (nodeMeets belowEnd unconstrained reaches fuel) path value state
45: 
```

## lean/MicroCFTA/SourceCurrentMuEndpoint.lean — primary_class

```lean
98: theorem primary_class [DecidableEq (EdgeKey Symbol Guard)]
99:     (unconstrained reaches : Value Symbol Guard → Bool) (fuel : Nat)
100:     (values : List (Value Symbol Guard)) (paths : Class) (state : State Symbol Guard) :
101:     classMeets true unconstrained reaches fuel values paths state =
102:       EndpointStatefulGate.classMeets unconstrained reaches fuel values paths state := by
```

## lean/MicroCFTA/SourceCurrentSecondaryTrace.lean — NodeTrace

```lean
33: inductive NodeTrace [DecidableEq (EdgeKey Symbol Guard)] (unconstrained : Value Symbol Guard → Bool) :
34:     Path → Value Symbol Guard → State Symbol Guard → Bool → State Symbol Guard → Prop where
```

## lean/MicroCFTA/SourceCurrentSecondaryTrace.lean — ClassTrace

```lean
83: inductive ClassTrace [DecidableEq (EdgeKey Symbol Guard)] (unconstrained : Value Symbol Guard → Bool)
84:     (values : List (Value Symbol Guard)) : Class → State Symbol Guard → Bool → State Symbol Guard → Prop where
```

## lean/MicroCFTA/SourceCurrentSecondaryTrace.lean — class_trace_unique

```lean
466: theorem class_trace_unique [DecidableEq (EdgeKey Symbol Guard)] (unconstrained : Value Symbol Guard → Bool)
467:     (values : List (Value Symbol Guard)) (paths : Class) (state : State Symbol Guard)
468:     (first second : Bool) (firstState secondState : State Symbol Guard)
469:     (left : ClassTrace unconstrained values paths state first firstState)
470:     (right : ClassTrace unconstrained values paths state second secondState) : first = second ∧ firstState = secondState := by
```

## lean/MicroCFTA/EndpointStatefulGateTrace.lean — NodeTrace

```lean
19: inductive NodeTrace [DecidableEq (EdgeKey Symbol Guard)] (unconstrained reaches : Value Symbol Guard → Bool) :
20:     Path → Value Symbol Guard → State Symbol Guard → Bool → State Symbol Guard → Prop where
```

## lean/MicroCFTA/SourceCurrentSecondaryCompletion.lean — node_complete

```lean
24: theorem node_complete [DecidableEq (EdgeKey Symbol Guard)] (unconstrained : Value Symbol Guard → Bool)
25:     (path : Path) (node : Node Symbol Guard) :
26:     Completes node.state (fun fuel => nodeMeets unconstrained fuel path node.value node.state) := by
```

## lean/MicroCFTA/SourceCurrentSecondaryCompletion.lean — class_complete

```lean
102: theorem class_complete [DecidableEq (EdgeKey Symbol Guard)] (unconstrained : Value Symbol Guard → Bool)
103:     (node : Node Symbol Guard) (values : List (Value Symbol Guard))
104:     (available : ∀ value ∈ values, Available node.state value) (paths : Class) :
105:     Completes node.state (fun fuel => classMeets unconstrained fuel values paths node.state) := by
```

## lean/MicroCFTA/SourceCurrentClassGateCompletion.lean — primary_class_complete

```lean
37: theorem primary_class_complete [DecidableEq (EdgeKey Symbol Guard)]
38:     (unconstrained reaches : Value Symbol Guard → Bool) (values : List (Value Symbol Guard))
39:     (paths : Class) (before : State Symbol Guard) (semantic : SemanticReady before)
40:     (costs : CostHeap before) (available : Values before values) :
41:     ∃ bound answer final,
42:       EndpointStatefulGateTrace.ClassTrace unconstrained reaches values paths before answer final ∧
43:       SemanticReady final ∧ CostHeap final ∧ Keeps before final ∧ Values final values ∧
44:       ∀ extra, SourceCurrentMuEndpoint.classMeets true unconstrained reaches (bound + extra)
45:         values paths before = .done (some answer) final := by
```

## lean/MicroCFTA/SourceCurrentClassGateCompletion.lean — secondary_class_complete

```lean
62: theorem secondary_class_complete [DecidableEq (EdgeKey Symbol Guard)]
63:     (unconstrained reaches : Value Symbol Guard → Bool) (values : List (Value Symbol Guard))
64:     (paths : Class) (before : State Symbol Guard) (semantic : SemanticReady before)
65:     (costs : CostHeap before) (available : Values before values) :
66:     ∃ bound answer final,
67:       SourceCurrentSecondaryTrace.ClassTrace unconstrained values paths before answer final ∧
68:       SemanticReady final ∧ CostHeap final ∧ Keeps before final ∧ Values final values ∧
69:       ∀ extra, SourceCurrentMuEndpoint.classMeets false unconstrained reaches (bound + extra)
70:         values paths before = .done (some answer) final := by
```

## lean/MicroCFTA/SourceCurrentAllocatedGateWorker.lean — primary_finite

```lean
185: theorem primary_finite (values : List (Value Symbol Guard)) (paths : Class) (before : Checked width)
186:     (semantic : SourceEqualityRequiredSemanticCache.SemanticReady before.native.machine.heap)
187:     (costs : InternedFreshOrdinaryCostHeap.Heap before.native.machine.heap)
188:     (available : Values before.native.machine.heap values) :
189:     ∃ answer after bound, ∀ fuel, bound ≤ fuel → primary fuel values paths before = .done answer after := by
```

## lean/MicroCFTA/SourceCurrentAllocatedGateWorker.lean — secondary_finite

```lean
196: theorem secondary_finite (values : List (Value Symbol Guard)) (paths : Class) (before : Checked width)
197:     (semantic : SourceEqualityRequiredSemanticCache.SemanticReady before.native.machine.heap)
198:     (costs : InternedFreshOrdinaryCostHeap.Heap before.native.machine.heap)
199:     (available : Values before.native.machine.heap values) :
200:     ∃ answer after bound, ∀ fuel, bound ≤ fuel → secondary fuel values paths before = .done answer after := by
```

## lean/MicroCFTA/SourceCurrentAllocatedGateFields.lean — primary_complete

```lean
66: theorem primary_complete [DecidableEq (EdgeKey Symbol Guard)]
67:     (unconstrained reaches : Value Symbol Guard → Bool) (values : List (Value Symbol Guard))
68:     (paths : EqualityNormalize.Class) (before : Physical) (ready : Ready before)
69:     (available : Values before.heap values) :
70:     ∃ answer heap, EndpointStatefulGateTrace.ClassTrace unconstrained reaches values paths before.heap answer heap ∧
71:       Effects before ⟨heap, before.equality⟩ ∧ Values heap values := by
```

## lean/MicroCFTA/SourceCurrentAllocatedGateFields.lean — secondary_complete

```lean
77: theorem secondary_complete [DecidableEq (EdgeKey Symbol Guard)]
78:     (unconstrained reaches : Value Symbol Guard → Bool) (values : List (Value Symbol Guard))
79:     (paths : EqualityNormalize.Class) (before : Physical) (ready : Ready before)
80:     (available : Values before.heap values) :
81:     ∃ answer heap, SourceCurrentSecondaryTrace.ClassTrace unconstrained values paths before.heap answer heap ∧
82:       Effects before ⟨heap, before.equality⟩ ∧ Values heap values := by
```

## lean/MicroCFTA/SourceCurrentAllocatedGateFields.lean — false_class_path_complete

```lean
167: theorem false_class_path_complete [DecidableEq (EdgeKey Symbol Guard)]
168:     (unconstrained : Value Symbol Guard → Bool)
169:     {paths : EqualityNormalize.Class} {values : List (Value Symbol Guard)}
170:     {before : Physical} {anchor : State Symbol Guard}
171:     (gate : SourceCurrentSecondaryTrace.ClassTrace unconstrained values paths before.heap false anchor)
172:     (ready : Ready before) (available : Values before.heap values)
173:     (path : EqualityNormalize.Path) (member : path ∈ paths) (proper : path ≠ []) :
174:     ∃ result heap, Forest (path.map Int.ofNat) values anchor result heap ∧
175:       Effects before ⟨heap, before.equality⟩ ∧ Available heap result ∧ result.free = [] := by
```

## lean/MicroCFTA/SourceCurrentSecondaryGateResources.lean — node

```lean
204: theorem node (unconstrained : Value Symbol Guard → Bool)
205:     {path : List Nat} {value : Value Symbol Guard} {before after : State Symbol Guard} {answer : Bool}
206:     (actual : NodeTrace unconstrained path value before answer after)
207:     (semantic : SemanticReady before) (costs : CostHeap before) (available : Available before value)
208:     (bound : Nat) (fits : Fits bound before) :
209:     Fits (nodeBound path.length bound) after ∧
210:       ∀ fuel, nodeFuel path.length bound ≤ fuel → nodeMeets unconstrained fuel path value before = .done (some answer) after := by
```

## lean/MicroCFTA/SourceCurrentSecondaryGateResources.lean — path

```lean
217: theorem path (unconstrained : Value Symbol Guard → Bool)
218:     {values : List (Value Symbol Guard)} {selected : List Nat} {before after : State Symbol Guard} {answer : Bool}
219:     (actual : PathTrace unconstrained values selected before answer after)
220:     (semantic : SemanticReady before) (costs : CostHeap before) (available : Values before values)
221:     (bound : Nat) (fits : Fits bound before) :
222:     Fits (pathBound selected bound) after ∧
223:       ∀ fuel, pathFuel selected bound ≤ fuel → meets unconstrained fuel values selected before = .done (some answer) after := by
```

## lean/MicroCFTA/SourceCurrentSecondaryGateResources.lean — classes

```lean
234: theorem classes (unconstrained : Value Symbol Guard → Bool)
235:     {values : List (Value Symbol Guard)} {paths : List (List Nat)} {before after : State Symbol Guard} {answer : Bool}
236:     (actual : ClassTrace unconstrained values paths before answer after)
237:     (semantic : SemanticReady before) (costs : CostHeap before) (available : Values before values)
238:     (bound : Nat) (fits : Fits bound before) :
239:     Fits (classBound paths bound) after ∧
240:       ∀ fuel, classFuel paths bound ≤ fuel → classMeets unconstrained fuel values paths before = .done (some answer) after := by
```

## lean/MicroCFTA/SourceCurrentSecondaryGateResources.lean — class_complete

```lean
261: theorem class_complete (unconstrained : Value Symbol Guard → Bool) (values : List (Value Symbol Guard))
262:     (paths : List (List Nat)) (before : State Symbol Guard) (semantic : SemanticReady before)
263:     (costs : CostHeap before) (available : Values before values) (bound : Nat) (fits : Fits bound before) :
264:     ∃ answer after, ClassTrace unconstrained values paths before answer after ∧
265:       SemanticReady after ∧ CostHeap after ∧ SourceEqualityRequiredCache.Keeps before after ∧ Values after values ∧
266:       Fits (classBound paths bound) after ∧
267:       ∀ fuel, classFuel paths bound ≤ fuel → classMeets unconstrained fuel values paths before = .done (some answer) after := by
```

## lean/MicroCFTA/SourceCurrentPrimaryGateResources.lean — rank_le_mass

```lean
79: theorem rank_le_mass (value : Value Symbol Guard) : rank value ≤ InternedValueMass.value value := by
```

## lean/MicroCFTA/SourceCurrentPrimaryGateResources.lean — unfold_fits

```lean
93: theorem unfold_fits [DecidableEq (EdgeKey Symbol Guard)] {bound : Nat}
94:     {value result : Value Symbol Guard} {before after : State Symbol Guard}
95:     (actual : InternedFreshOrdinaryStoredSubstitution.unfold value before = .done result after)
96:     (fits : Fits bound before) (available : Available before value) : Fits (g bound) after := by
```

## lean/MicroCFTA/SourceCurrentPrimaryGateResources.lean — classBound

```lean
199: def classBound : List (List Nat) → Nat → Nat
200:   | [], bound => bound
201:   | path :: rest, bound => classBound rest (pathBound path bound)
202: /-- One common class fuel covers each exact forecasted path entry. -/
203: def classFuel : List (List Nat) → Nat → Nat
204:   | [], _ => 0
205:   | path :: rest, bound => max (pathFuel path bound) (classFuel rest (pathBound path bound))
206: 
```

## lean/MicroCFTA/SourceCurrentPrimaryGateResources.lean — classFuel

```lean
203: def classFuel : List (List Nat) → Nat → Nat
204:   | [], _ => 0
205:   | path :: rest, bound => max (pathFuel path bound) (classFuel rest (pathBound path bound))
206: 
```

## lean/MicroCFTA/SourceCurrentConjunctionClassScan.lean — Scan

```lean
38: inductive Scan [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
39:     [DecidableEq (Value Symbol Guard)]
40:     (budget : Nat) (unconstrained reaches : Value Symbol Guard → Bool)
41:     (values : List (Value Symbol Guard)) :
42:     Constraints → Checked width → Memo → Option Class → Constraints → Checked width → Memo → Prop where
```

## lean/MicroCFTA/SourceCurrentConjunctionClassScan.lean — primary_effects

```lean
127: theorem primary_effects [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
128:     (unconstrained reaches : Value Symbol Guard → Bool)
129:     {values : List (Value Symbol Guard)} {paths : Class} {before : Checked width}
130:     {answer : Bool} {heap : State Symbol Guard}
131:     (actual : EndpointStatefulGateTrace.ClassTrace unconstrained reaches values paths
132:       before.native.machine.heap answer heap)
133:     (ready : Ready before) (available : Values before.native.machine.heap values) :
134:     Ready (advanceHeap before heap) ∧
135:       SourceCurrentConjunctionRowsAllocation.Effects (physical before) (physical (advanceHeap before heap)) ∧
136:       Values (advanceHeap before heap).native.machine.heap values := by
```

## lean/MicroCFTA/SourceCurrentConjunctionClassScan.lean — secondary_effects

```lean
142: theorem secondary_effects [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
143:     (unconstrained : Value Symbol Guard → Bool)
144:     {values : List (Value Symbol Guard)} {paths : Class} {before : Checked width}
145:     {answer : Bool} {heap : State Symbol Guard}
146:     (actual : SourceCurrentSecondaryTrace.ClassTrace unconstrained values paths
147:       before.native.machine.heap answer heap)
148:     (ready : Ready before) (available : Values before.native.machine.heap values) :
149:     Ready (advanceHeap before heap) ∧
150:       SourceCurrentConjunctionRowsAllocation.Effects (physical before) (physical (advanceHeap before heap)) ∧
151:       Values (advanceHeap before heap).native.machine.heap values := by
```

## lean/MicroCFTA/SourceCurrentConjunctionClassScanCompletion.lean — Ranges

```lean
26: def Ranges [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
27:     [DecidableEq (Value Symbol Guard)]
28:     (budget : Nat) (unconstrained reaches : Value Symbol Guard → Bool)
29:     (values : List (Value Symbol Guard)) : Constraints → Checked width → Memo → Prop
30:   | [], _, _ => True
31:   | paths :: classes, before, memo =>
32:       (∀ heap, EndpointStatefulGateTrace.ClassTrace unconstrained reaches values paths
33:         before.native.machine.heap false heap →
34:         Ranges budget unconstrained reaches values classes (advanceHeap before heap) memo) ∧
35:       (∀ heap, EndpointStatefulGateTrace.ClassTrace unconstrained reaches values paths
36:         before.native.machine.heap true heap →
37:         ∀ anchor, SourceCurrentSecondaryTrace.ClassTrace unconstrained values paths heap true anchor →
38:         Ranges budget unconstrained reaches values classes (advanceHeap (advanceHeap before heap) anchor) memo) ∧
39:       (∀ heap, EndpointStatefulGateTrace.ClassTrace unconstrained reaches values paths
40:         before.native.machine.heap true heap →
41:         ∀ anchor, SourceCurrentSecondaryTrace.ClassTrace unconstrained values paths heap false anchor →
42:         SourceCurrentAllocatedSeededQuery.SeededRanges values (paths.map (List.map Int.ofNat))
43:           (advanceHeap (advanceHeap before heap) anchor) ∧
44:         ∀ query middle, SourceCurrentAllocatedSeededQuery.Seeded values (paths.map (List.map Int.ofNat))
45:           (advanceHeap (advanceHeap before heap) anchor) query middle →
46:           ∀ later saved, SourceCurrentConjunctionMemo.Call budget memo query (physical middle) false later saved →
47:             Ranges budget unconstrained reaches values classes (advancePhysical middle later) saved)
48: 
```

## lean/MicroCFTA/SourceCurrentConjunctionClassScanCompletion.lean — finite

```lean
50: theorem finite [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
51:     [DecidableEq (Value Symbol Guard)]
52:     (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
53:     (budget : Nat) (unconstrained reaches : Value Symbol Guard → Bool)
54:     (values : List (Value Symbol Guard)) (classes : Constraints) (before : Checked width) (memo : Memo)
55:     (ready : Ready before) (available : Values before.native.machine.heap values)
56:     (proper : ∀ paths ∈ classes, ∀ path ∈ paths, path ≠ [])
57:     (correct : SourceCurrentEmptinessMemo.Correct formulas solver before.native.machine.heap memo)
58:     (ranges : Ranges budget unconstrained reaches values classes before memo) :
59:     ∃ outcome selected after saved,
60:       Scan budget unconstrained reaches values classes before memo outcome selected after saved ∧
61:       Ready after ∧ Effects (physical before) (physical after) ∧
62:       Values after.native.machine.heap values ∧
63:       SourceCurrentEmptinessMemo.Correct formulas solver after.native.machine.heap saved ∧
64:       SourceCurrentEmptinessMemo.Extends memo saved := by
```

## lean/MicroCFTA/SourceCurrentAllocatedSeededQuery.lean — Operand

```lean
44: inductive Operand [DecidableEq (EdgeKey Symbol Guard)] (path : List Int)
45:     (values : List (Value Symbol Guard)) (before : Checked width) :
46:     Value Symbol Guard → Checked width → Prop where
```

## lean/MicroCFTA/SourceCurrentAllocatedSeededQuery.lean — Fold

```lean
52: inductive Fold [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
53:     (values : List (Value Symbol Guard)) :
54:     List (List Int) → Checked width → Value Symbol Guard → Checked width → Prop where
```

## lean/MicroCFTA/SourceCurrentAllocatedSeededQuery.lean — Seeded

```lean
63: inductive Seeded [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
64:     (values : List (Value Symbol Guard)) :
65:     List (List Int) → Checked width → Value Symbol Guard → Checked width → Prop where
```

## lean/MicroCFTA/SourceCurrentAllocatedSeededQuery.lean — SeededRanges

```lean
83: def SeededRanges [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
84:     (values : List (Value Symbol Guard)) (paths : List (List Int)) (before : Checked width) : Prop :=
```

## lean/MicroCFTA/SourceCurrentAllocatedSeededQuery.lean — false_class_complete

```lean
251: theorem false_class_complete [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
252:     (unconstrained : Value Symbol Guard → Bool) (paths : Class) (values : List (Value Symbol Guard))
253:     {before : Checked width} {anchor : State Symbol Guard}
254:     (gate : SourceCurrentSecondaryTrace.ClassTrace unconstrained values paths before.native.machine.heap false anchor)
255:     (good : Good before) (ready : Ready (physical before)) (scopes : Scoped before.native) (idle : Idle before.native)
256:     (available : Values before.native.machine.heap values) (proper : ∀ path ∈ paths, path ≠ [])
257:     (ranges : SeededRanges values (paths.map (List.map Int.ofNat))
258:       (advancePhysical before ⟨anchor, before.operations⟩)) :
259:     ∃ query after, Seeded values (paths.map (List.map Int.ofNat))
260:         (advancePhysical before ⟨anchor, before.operations⟩) query after ∧ Good after ∧
261:       Effects (physical before) (physical after) ∧ Extension before.native.machine after.native.machine ∧
262:       Scoped after.native ∧ Idle after.native ∧ Available after.native.machine.heap query ∧ query.free = [] := by
```

## lean/MicroCFTA/SourceCurrentAllocatedSeededWorker.lean — operand

```lean
43: def operand [DecidableEq (EdgeKey Symbol Guard)] (p h : Nat) (path : List Int)
44:     (values : List (Value Symbol Guard)) (before : Checked width) : Outcome width :=
```

## lean/MicroCFTA/SourceCurrentAllocatedSeededWorker.lean — fold

```lean
63: noncomputable def fold [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
64:     (p h n : Nat) (values : List (Value Symbol Guard)) (seed : List Int) :
65:     List (List Int) → Checked width → Outcome width
66:   | [], before => operand p h seed values before
67:   | path :: paths, before =>
68:       (operand p h path values before).bind fun head middle =>
69:         (fold p h n values seed paths middle).bind fun tail later => leaf n head tail later
70: 
```

## lean/MicroCFTA/SourceCurrentAllocatedSeededWorker.lean — seeded

```lean
72: noncomputable def seeded [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
73:     (p h n : Nat) (values : List (Value Symbol Guard)) (paths : List (List Int))
74:     (before : Checked width) : Outcome width :=
```

## lean/MicroCFTA/SourceCurrentAllocatedSeededWorkerCompletion.lean — fold_complete

```lean
82: theorem fold_complete [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
83:     {values : List (Value Symbol Guard)} {seed : List Int} {paths : List (List Int)}
84:     {before after : Checked width} {result : Value Symbol Guard}
85:     (actual : Fold values (paths ++ [seed]) before result after) :
86:     StableRun (fun p h n => fold p h n values seed paths before) result after := by
```

## lean/MicroCFTA/SourceCurrentAllocatedSeededWorkerCompletion.lean — seeded_complete

```lean
106: theorem seeded_complete [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
107:     {values : List (Value Symbol Guard)} {paths : List (List Int)}
108:     {before after : Checked width} {result : Value Symbol Guard}
109:     (actual : Seeded values paths before result after) :
110:     StableRun (fun p h n => seeded p h n values paths before) result after := by
```

## lean/MicroCFTA/SourceCurrentAllocatedSeededWorkerCompletion.lean — seeded_uniform

```lean
116: theorem seeded_uniform [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
117:     {values : List (Value Symbol Guard)} {paths : List (List Int)}
118:     {before after : Checked width} {result : Value Symbol Guard}
119:     (actual : Seeded values paths before result after) :
120:     ∃ bound, ∀ fuel, bound ≤ fuel → seeded fuel fuel fuel values paths before = .done result after := by
```

## lean/MicroCFTA/SourceCurrentGeneratedQueryFrameResources.lean — Receipt

```lean
32: structure Receipt (profile : Profile)
33:     (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
34:     (inventory : Inventory) (fuel : Nat) (left right : Value Symbol Guard) (before : Checked width)
35:     (value : Value Symbol Guard) (after : Checked width) (memos : Memos) : Prop where
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

## lean/MicroCFTA/SourcePrimaryGateEffects.lean — class_effects

```lean
147: theorem class_effects (property : Guard → Prop) [DecidableEq (EdgeKey Symbol Guard)]
148:     (unconstrained reaches : Value Symbol Guard → Bool)
149:     {values : List (Value Symbol Guard)} {paths : Class} {before after : State Symbol Guard} {answer : Bool}
150:     (trace : ClassTrace unconstrained reaches values paths before answer after)
151:     (semantic : SemanticReady before) (costs : InternedFreshOrdinaryCostHeap.Heap before)
152:     (available : ∀ value ∈ values, Available before value) (fields : Heap property before) :
153:     SemanticReady after ∧ Keeps before after ∧ InternedFreshOrdinaryCostHeap.Heap after ∧ Heap property after := by
```

## lean/MicroCFTA/SourceCurrentSecondaryEffects.lean — class_effects

```lean
147: theorem class_effects (property : Guard → Prop) [DecidableEq (EdgeKey Symbol Guard)]
148:     (unconstrained : Value Symbol Guard → Bool)
149:     {values : List (Value Symbol Guard)} {paths : Class} {before after : State Symbol Guard} {answer : Bool}
150:     (trace : ClassTrace unconstrained values paths before answer after)
151:     (semantic : SemanticReady before) (costs : InternedFreshOrdinaryCostHeap.Heap before)
152:     (available : ∀ value ∈ values, Available before value) (fields : Heap property before) :
153:     SemanticReady after ∧ Keeps before after ∧ InternedFreshOrdinaryCostHeap.Heap after ∧ Heap property after := by
```

## lean/MicroCFTA/InternedFreeOccurrenceRank.lean — rank

```lean
104: def rank (value : Value Symbol Guard) : Nat := ((costs value).map Prod.snd).min?.getD 0
```

## lean/MicroCFTA/InternedFreshOrdinaryUnfoldRank.lean — unfold_decreases

```lean
20: theorem unfold_decreases [DecidableEq (EdgeKey Symbol Guard)]
21:     (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard) (state : State Symbol Guard)
22:     (context : Context state captures) (cached : InternedFreshOrdinaryDepthHeap.Heap state)
23:     (heap : InternedFreshOrdinaryCostHeap.Heap state)
24:     (available : Available state (.mu entry body depth ordinary))
25:     (opened : (Value.mu entry body depth ordinary).free ≠ [])
26:     (value : Value Symbol Guard) (after : State Symbol Guard)
27:     (done : InternedFreshOrdinaryStoredSubstitution.unfold (.mu entry body depth ordinary) state = .done value after) :
28:     rank value < rank (.mu entry body depth ordinary) := by
```

## cfta/src/Data/CFTA/Equality/Operations.hs — source gate

```haskell
255:     meetsConstrainedMu :: Bool -> [Node symbol] -> Path -> Bool
256:     meetsConstrainedMu belowEnd ns (ConsPath (ChildIndex index) rest) = maybe False (nodeMeetsConstrainedMu belowEnd rest) (ns !? index)
257:     meetsConstrainedMu _ _ EmptyPath = False
258: 
259:     nodeMeetsConstrainedMu :: Bool -> Path -> Node symbol -> Bool
260:     nodeMeetsConstrainedMu _ _ (Rec _) = True
261:     nodeMeetsConstrainedMu _ _ (InternedUnion _) = True
262:     nodeMeetsConstrainedMu _ _ n | numNestedMu n == 0 && null (freeVars n) = False
263:     nodeMeetsConstrainedMu belowEnd p n@(InternedMu _)
264:         | not (unconstrained n) = case p of
265:             EmptyPath | null (freeVars n) -> belowEnd
266:             _ -> True
267:         | null (freeVars n) = False
268:         | otherwise = nodeMeetsConstrainedMu belowEnd p (unfoldOuterRec n)
269:     nodeMeetsConstrainedMu belowEnd EmptyPath n = not (null (freeVars n)) || (belowEnd && reachesConstrainedMu n)
270:     nodeMeetsConstrainedMu belowEnd p (Node es) = any (\e -> meetsConstrainedMu belowEnd (edgeChildren e) p) es
271:     nodeMeetsConstrainedMu _ _ _ = False
```

## lean/MicroCFTA/EndpointStatefulGateTrace.lean — node_trace_of_done

```lean
106: theorem node_trace_of_done [DecidableEq (EdgeKey Symbol Guard)] (unconstrained reaches : Value Symbol Guard → Bool)
107:     (fuel : Nat) (path : Path) (value : Value Symbol Guard) (state : State Symbol Guard)
108:     (answer : Bool) (final : State Symbol Guard)
109:     (done : nodeMeets unconstrained reaches fuel path value state = .done (some answer) final) :
110:     NodeTrace unconstrained reaches path value state answer final := by
```
