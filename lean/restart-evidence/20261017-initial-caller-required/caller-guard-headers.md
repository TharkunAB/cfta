# Caller source headers

Captured at 2026-10-17T11:59:27+02:00.

## SourceCurrentConjunctionClassScan

`Scan`

```lean
38: inductive Scan [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
39:     [DecidableEq (Value Symbol Guard)]
40:     (budget : Nat) (unconstrained reaches : Value Symbol Guard → Bool)
41:     (values : List (Value Symbol Guard)) :
42:     Constraints → Checked width → Memo → Option Class → Constraints → Checked width → Memo → Prop where
```

`Ready`

```lean
110: structure Ready (state : Checked width) : Prop where
```

## SourceCurrentConjunctionClassScanCompletion

`Ranges`

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
49: /-- Initial invariants and reached word bounds derive a finite current scan and its returned states. -/
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

`finite`

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

## SourceCurrentConjunctionRequired

`required_complete`

```lean
130: theorem required_complete [DecidableEq (EdgeKey Symbol Guard)]
131:     (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
132:     (inventory : Inventory) (unconstrained reaches : Value Symbol Guard → Bool)
133:     (selected : Constraints) (values : List (Value Symbol Guard)) (before : Checked width)
134:     (ready : Ready before) (admitted : At formulas solver inventory before)
135:     (available : Values before.native.machine.heap values)
136:     (proper : ∀ path ∈ selected.flatten, path ≠ [])
137:     (primary : ∀ paths ∈ selected, EndpointStatefulGateTrace.ClassTrace unconstrained reaches values paths
138:       before.native.machine.heap false before.native.machine.heap) :
139:     ∃ results heap, Receipt formulas solver inventory selected values results before (advanceHeap before heap) := by
```

`scan_required_complete`

```lean
170: theorem scan_required_complete [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
171:     [DecidableEq (Value Symbol Guard)]
172:     (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
173:     (inventory : Inventory)
174:     {budget : Nat} {unconstrained reaches : Value Symbol Guard → Bool} {values : List (Value Symbol Guard)}
175:     {classes selected : Constraints} {before after : Checked width} {memo saved : Memo}
176:     (actual : Scan budget unconstrained reaches values classes before memo none selected after saved)
177:     (ready : Ready before) (admitted : At formulas solver inventory before)
178:     (available : Values before.native.machine.heap values)
179:     (proper : ∀ paths ∈ classes, ∀ path ∈ paths, path ≠ []) (active : ∀ paths ∈ classes, Nontrivial paths)
180:     (correct : SourceCurrentEmptinessMemo.Correct formulas solver before.native.machine.heap memo)
181:     (ranges : Ranges budget unconstrained reaches values classes before memo) :
182:     ∃ next results heap, Receipt formulas solver next selected values results after (advanceHeap after heap) ∧
183:       Effects (physical before) (physical (advanceHeap after heap)) ∧
184:       SourceCurrentEmptinessMemo.Correct formulas solver heap saved ∧ SourceCurrentEmptinessMemo.Extends memo saved := by
```

## SourceCurrentConjunctionRequiredActual

`verified`

```lean
40: theorem verified
41:     (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
42:     (inventory : Inventory)
43:     {budget : Nat} {unconstrained reaches : Value Symbol Guard → Bool} {values results : List (Value Symbol Guard)}
44:     {classes selected : Constraints} {before middle : Checked width} {fourth savedFourth : Fourth}
45:     (scan : Scan budget unconstrained reaches values classes before fourth none selected middle savedFourth)
46:     (ready : Ready before) (admitted : At formulas solver inventory before)
47:     (available : Values before.native.machine.heap values)
48:     (proper : ∀ paths ∈ classes, ∀ path ∈ paths, path ≠ [])
49:     (active : ∀ paths ∈ classes, Nontrivial paths)
50:     (correct : SourceCurrentEmptinessMemo.Correct formulas solver before.native.machine.heap fourth)
51:     (ranges : SourceCurrentConjunctionClassScanCompletion.Ranges budget unconstrained reaches values classes before fourth)
52:     {fuel readFuel : Nat} {heap : State Symbol Guard}
53:     (actual : SourceEqualityRequiredExecution.requireAll fuel readFuel (SourceEqualitySelectedRequired.paths selected)
54:       values middle.native.machine.heap = .done results heap) :
55:     ∃ next, SourceCurrentConjunctionRequired.Receipt formulas solver next selected values results
56:       middle (advanceHeap middle heap) := by
```

## SourceCurrentConjunctionRequiredClassPass

`finite`

```lean
141: theorem finite
142:     (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
143:     (inventory : Inventory) {selected : Constraints} {originals values : List (Value Symbol Guard)}
144:     {before prepared : Checked width}
145:     (required : SourceCurrentConjunctionRequired.Receipt formulas solver inventory selected originals values before prepared)
146:     (records : List SourceEqualityClassOrder.Record)
147:     (selectedEq : records.map SourceEqualityClassOrder.Record.paths = selected)
148:     (coherent : ∀ record ∈ records, SourceEqualityClassOrder.Coherent record)
149:     (active : ∀ record ∈ records, Nontrivial record.paths)
150:     (memo : Memo) (stored : SourceCurrentMemoMergeEffects.Stored before.native.machine.heap memo)
151:     (covered : ∀ ambient, SourceCurrentMemoMergeLanguage.CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
152:     (ranges : Ranges records values prepared memo) (memos : Memos) (valid : Valid prepared.native.machine.heap memos) :
153:     ∃ results after saved next final, ∃ actual : Pass records values prepared memo results after saved,
154:       PassReads formulas solver actual memos final ∧
155:       Receipt formulas solver next records selected originals values before prepared memo results after saved memos final := by
```

## SourceCurrentConstrainedCapClassPassNumeric

`fold`

```lean
54: theorem fold (depth : Nat)
55:     (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
56:     (inventory : Inventory) (records : List SourceEqualityClassOrder.Record)
57:     (coherent : ∀ record ∈ records, SourceEqualityClassOrder.Coherent record)
58:     (active : ∀ record ∈ records, EqualityNormalize.Nontrivial record.paths)
59:     (values : List (Value Symbol Guard)) (before : Checked (bits + 2)) (memo : Memo) (profile : Profile)
60:     (frame : Frame formulas solver inventory before) (fits : Fits profile before)
61:     (available : Values before.native.machine.heap values)
62:     (domains : ∀ record ∈ records, ∀ path ∈ record.paths, ForestClosed (path.map Int.ofNat) values)
63:     (physical : PhysicalStored before.native.machine.heap memo)
64:     (covered : ∀ ambient, CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
65:     (merged : MergeStored memo) (memos : Memos) (valid : Valid before.native.machine.heap memos)
66:     (caps : ∀ value ∈ values, Cap depth value)
67:     (reserved : Forecast.Reserved bits records values.length profile) :
68:     ∃ results after saved next final, ∃ actual : Fold records values before memo results after saved,
69:       FoldReads formulas solver actual memos final ∧
70:       Receipt formulas solver next records values before memo results after saved memos final ∧
71:       Frame formulas solver next after ∧ Fits (Forecast.foldProfile records values.length profile) after ∧
72:       MergeStored saved ∧ (∀ value ∈ results, Cap (foldDepth records depth) value) ∧
73:       results.length = values.length ∧
74:       Worker.fold (Forecast.foldFuel records values.length profile) (Forecast.foldFuel records values.length profile)
75:         (Forecast.foldFuel records values.length profile) (Forecast.foldFuel records values.length profile)
76:         (Forecast.foldFuel records values.length profile) (Forecast.foldFuel records values.length profile)
77:         records values before memo = .done results after saved := by
```

`pass`

```lean
127: theorem pass (depth : Nat)
128:     (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
129:     (inventory : Inventory) (records : List SourceEqualityClassOrder.Record)
130:     (coherent : ∀ record ∈ records, SourceEqualityClassOrder.Coherent record)
131:     (active : ∀ record ∈ records, EqualityNormalize.Nontrivial record.paths)
132:     (values : List (Value Symbol Guard)) (before : Checked (bits + 2)) (memo : Memo) (profile : Profile)
133:     (frame : Frame formulas solver inventory before) (fits : Fits profile before)
134:     (available : Values before.native.machine.heap values)
135:     (domains : ∀ record ∈ records, ∀ path ∈ record.paths, ForestClosed (path.map Int.ofNat) values)
136:     (physical : PhysicalStored before.native.machine.heap memo)
137:     (covered : ∀ ambient, CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
138:     (merged : MergeStored memo) (memos : Memos) (valid : Valid before.native.machine.heap memos)
139:     (caps : ∀ value ∈ values, Cap depth value)
140:     (reserved : Forecast.Reserved bits records values.length profile) :
141:     ∃ results after saved next final, ∃ actual : Pass records values before memo results after saved,
142:       PassReads formulas solver actual memos final ∧
143:       Receipt formulas solver next records values before memo results after saved memos final ∧
144:       Frame formulas solver next after ∧ Fits (Forecast.foldProfile records values.length profile) after ∧
145:       MergeStored saved ∧ (∀ value ∈ results, Cap (foldDepth records depth) value) ∧
146:       results.length = values.length ∧
147:       Worker.pass (Forecast.foldFuel records values.length profile) (Forecast.foldFuel records values.length profile)
148:         (Forecast.foldFuel records values.length profile) (Forecast.foldFuel records values.length profile)
149:         (Forecast.foldFuel records values.length profile) (Forecast.foldFuel records values.length profile)
150:         records values before memo = .done results after saved := by
```

## SourceCurrentConstrainedCapClassCallerNumeric

`complete`

```lean
38: theorem complete (depth : Nat)
39:     (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
40:     (inventory : Inventory) (records : List SourceEqualityClassOrder.Record)
41:     (coherent : ∀ record ∈ records, SourceEqualityClassOrder.Coherent record)
42:     (active : ∀ record ∈ records, EqualityNormalize.Nontrivial record.paths)
43:     (values : List (Value Symbol Guard)) (before : Caller (bits + 2)) (memos : Memos) (profile : Profile)
44:     (initial : Context formulas solver inventory before memos)
45:     (frame : Frame formulas solver inventory before.checked) (fits : Fits profile before.checked)
46:     (available : Values before.checked.native.machine.heap values)
47:     (domains : ∀ record ∈ records, ∀ path ∈ record.paths, ForestClosed (path.map Int.ofNat) values)
48:     (merged : MergeStored before.merge) (caps : ∀ value ∈ values, Cap depth value)
49:     (reserved : Reserved bits records values.length profile) :
50:     ∃ results after saved next final,
51:       ∃ actual : Pass records values before.checked before.merge results after saved,
52:       PassReads formulas solver actual memos final ∧
53:       Receipt formulas solver next records values before.checked before.merge results after saved memos final ∧
54:       Post formulas solver next before (advance before after before.fourth saved) final ∧
55:       Frame formulas solver next after ∧ Fits (foldProfile records values.length profile) after ∧
56:       MergeStored saved ∧ (∀ value ∈ results, Cap (foldDepth records depth) value) ∧
57:       results.length = values.length ∧
58:       (advance before after before.fourth saved).nodeResults = before.nodeResults ∧
59:       (advance before after before.fourth saved).edgeResults = before.edgeResults ∧
60:       (advance before after before.fourth saved).fourth = before.fourth ∧
61:       SourceCurrentAllocatedClassWorker.pass
62:         (foldFuel records values.length profile) (foldFuel records values.length profile)
63:         (foldFuel records values.length profile) (foldFuel records values.length profile)
64:         (foldFuel records values.length profile) (foldFuel records values.length profile)
65:         records values before.checked before.merge = .done results after saved ∧
66:       ∀ e p h m s n,
67:         foldFuel records values.length profile ≤ e → foldFuel records values.length profile ≤ p →
68:         foldFuel records values.length profile ≤ h → foldFuel records values.length profile ≤ m →
69:         foldFuel records values.length profile ≤ s → foldFuel records values.length profile ≤ n →
70:         SourceCurrentAllocatedClassWorker.pass e p h m s n records values before.checked before.merge =
71:           .done results after saved := by
```

## SourceCurrentConstrainedCapOpenExposure

`collect`

```lean
51: theorem collect [DecidableEq (EdgeKey Symbol Guard)] (valid : Guard → Prop) (capDepth fuel : Nat)
52:     (state : State Symbol Guard) (semantic : SemanticHeap state) (covered : Covered [] state)
53:     (seen : List Nat) (pending : List (Value Symbol Guard)) (inputs : Values state pending)
54:     (annotated : ∀ value ∈ pending, Cap valid capDepth value)
55:     (stored : MuStored valid state) (edges : List (EdgeValue Symbol Guard)) (after : State Symbol Guard)
56:     (done : MergedFreshOrdinaryExposure.collect fuel state seen pending = .done edges after) :
57:     MuStored valid after ∧ ∀ edge ∈ edges, Edge valid capDepth edge := by
```

`nodeEdges`

```lean
136: theorem nodeEdges [DecidableEq (EdgeKey Symbol Guard)] (valid : Guard → Prop) (capDepth fuel : Nat)
137:     (value : Value Symbol Guard) (state : State Symbol Guard) (semantic : SemanticHeap state)
138:     (covered : Covered [] state) (available : Available state value)
139:     (annotated : Cap valid capDepth value) (stored : MuStored valid state)
140:     (edges : List (EdgeValue Symbol Guard)) (after : State Symbol Guard)
141:     (done : MergedFreshOrdinaryExposure.nodeEdges fuel value state = .done edges after) :
142:     MuStored valid after ∧ ∀ edge ∈ edges, Edge valid capDepth edge := by
```

`head`

```lean
182: theorem head [DecidableEq (EdgeKey Symbol Guard)] (valid : Guard → Prop) (capDepth : Nat)
183:     {value result : Value Symbol Guard} {before after : State Symbol Guard}
184:     (trace : SourceEqualityRequiredHead.Head value before result after)
185:     (semantic : SourceEqualityRequiredSemanticCache.SemanticReady before)
186:     (costs : InternedFreshOrdinaryCostHeap.Heap before)
187:     (available : Available before value) (annotated : Cap valid capDepth value)
188:     (stored : MuStored valid before) : MuStored valid after ∧ Cap valid capDepth result := by
```

## SourceCurrentConstrainedCapSelectedRequired

`node`

```lean
175: theorem node [DecidableEq (EdgeKey Symbol Guard)] (valid : Guard → Prop) (capDepth : Nat)
176:     {needed : SourceEqualityNeeded.Needed} {value result : Value Symbol Guard} {before after : State Symbol Guard}
177:     (actual : RequireNode needed value before result after) (semantic : SemanticReady before) (costs : CostHeap before)
178:     (available : Available before value) (stored : GuardHeap valid before) (annotated : Cap valid capDepth value) :
179:     GuardHeap valid after ∧ Cap valid capDepth result :=
```

`children`

```lean
183: theorem children [DecidableEq (EdgeKey Symbol Guard)] (valid : Guard → Prop) (capDepth : Nat)
184:     {entries : List (Int × SourceEqualityNeeded.Needed)} {index : Nat} {values results : List (Value Symbol Guard)} {before after : State Symbol Guard}
185:     (actual : RequireChildren entries index values before results after) (semantic : SemanticReady before) (costs : CostHeap before)
186:     (available : Values before values) (stored : GuardHeap valid before) (annotated : ∀ value ∈ values, Cap valid capDepth value) :
187:     GuardHeap valid after ∧ ∀ value ∈ results, Cap valid capDepth value :=
```

`rows`

```lean
191: theorem rows [DecidableEq (EdgeKey Symbol Guard)] (valid : Guard → Prop) (capDepth : Nat)
192:     {entries : List (Int × SourceEqualityNeeded.Needed)} {edges results : List (EdgeValue Symbol Guard)} {before after : State Symbol Guard}
193:     (actual : RequireRows entries edges before results after) (semantic : SemanticReady before) (costs : CostHeap before)
194:     (resident : Edges before edges) (stored : GuardHeap valid before)
195:     (annotated : ∀ edge ∈ edges, Edge valid capDepth edge) :
196:     GuardHeap valid after ∧ ∀ edge ∈ results, Edge valid capDepth edge :=
```

`requireAll`

```lean
203: theorem requireAll [DecidableEq (EdgeKey CurrentSymbol CurrentGuard)] (valid : CurrentGuard → Prop) (capDepth : Nat) {paths : List (List Int)}
204:     {values results : List (Value CurrentSymbol CurrentGuard)} {before after : State CurrentSymbol CurrentGuard}
205:     {memos saved : EndpointMemoGateTrace.Memos}
206:     (reads : SourceCurrentRequiredQueryMemos.RequireAllReads paths values results before after memos saved)
207:     (semantic : SemanticReady before) (costs : CostHeap before) (available : Values before values)
208:     (stored : GuardHeap valid before) (annotated : ∀ value ∈ values, Cap valid capDepth value) :
209:     GuardHeap valid after ∧ (∀ value ∈ results, Cap valid capDepth value) ∧ results.length = values.length := by
```

## SourceCurrentConstrainedCapSelectedRequiredComplete

`complete`

```lean
34: theorem complete (depth : Nat)
35:     (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
36:     (inventory : Inventory) (unconstrained reaches : Value Symbol Guard → Bool)
37:     (selected : EqualityNormalize.Constraints) (values : List (Value Symbol Guard)) (before : Checked width)
38:     (frame : Frame formulas solver inventory before) (available : Values before.native.machine.heap values)
39:     (proper : ∀ path ∈ selected.flatten, path ≠ [])
40:     (primary : ∀ paths ∈ selected, EndpointStatefulGateTrace.ClassTrace unconstrained reaches values paths
41:       before.native.machine.heap false before.native.machine.heap)
42:     (caps : ∀ value ∈ values, Cap depth value) (memos : Memos) (valid : Valid before.native.machine.heap memos) :
43:     ∃ results heap final fuel readFuel,
44:       SourceCurrentConjunctionRequired.Receipt formulas solver inventory selected values results before
45:         (advanceHeap before heap) ∧
46:       SourceCurrentRequiredQueryMemos.RequireAllReads (SourceEqualitySelectedRequired.paths selected)
47:         values results before.native.machine.heap heap memos final ∧
48:       Frame formulas solver inventory (advanceHeap before heap) ∧
49:       SourceCurrentSubsumesQueryMemos.Effect before.native.machine.heap heap memos final ∧
50:       (∀ value ∈ results, Cap depth value) ∧ results.length = values.length ∧
51:       SourceEqualityRequiredExecution.requireAll fuel readFuel (SourceEqualitySelectedRequired.paths selected)
52:         values before.native.machine.heap = .done results heap := by
```

`caller`

```lean
69: theorem caller (depth : Nat)
70:     (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
71:     (inventory : Inventory) (unconstrained reaches : Value Symbol Guard → Bool)
72:     (selected : EqualityNormalize.Constraints) (values : List (Value Symbol Guard)) (before : Caller width)
73:     (memos : Memos) (initial : Context formulas solver inventory before memos)
74:     (frame : Frame formulas solver inventory before.checked)
75:     (available : Values before.checked.native.machine.heap values)
76:     (proper : ∀ path ∈ selected.flatten, path ≠ [])
77:     (primary : ∀ paths ∈ selected, EndpointStatefulGateTrace.ClassTrace unconstrained reaches values paths
78:       before.checked.native.machine.heap false before.checked.native.machine.heap)
79:     (caps : ∀ value ∈ values, Cap depth value) :
80:     ∃ results heap final fuel readFuel,
81:       SourceCurrentConjunctionRequired.Receipt formulas solver inventory selected values results before.checked
82:         (advanceHeap before.checked heap) ∧
83:       SourceCurrentRequiredQueryMemos.RequireAllReads (SourceEqualitySelectedRequired.paths selected)
84:         values results before.checked.native.machine.heap heap memos final ∧
85:       Frame formulas solver inventory (advanceHeap before.checked heap) ∧
86:       Post formulas solver inventory before (advance before (advanceHeap before.checked heap) before.fourth before.merge) final ∧
87:       (∀ value ∈ results, Cap depth value) ∧ results.length = values.length ∧
88:       (advance before (advanceHeap before.checked heap) before.fourth before.merge).nodeResults = before.nodeResults ∧
89:       (advance before (advanceHeap before.checked heap) before.fourth before.merge).edgeResults = before.edgeResults ∧
90:       (advance before (advanceHeap before.checked heap) before.fourth before.merge).fourth = before.fourth ∧
91:       (advance before (advanceHeap before.checked heap) before.fourth before.merge).merge = before.merge ∧
92:       SourceEqualityRequiredExecution.requireAll fuel readFuel (SourceEqualitySelectedRequired.paths selected)
93:         values before.checked.native.machine.heap = .done results heap := by
```

## SourceCurrentAllocatedPartialInvariant

`Context`

```lean
25: structure Context (formulas : SourceGuards.Formulas FullSyntax.Formula)
26:     (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
27:     (state : Caller width) (memos : Memos) : Prop where
```

`Post`

```lean
38: structure Post (formulas : SourceGuards.Formulas FullSyntax.Formula)
39:     (solver : SourceGuards.Entailment FullSyntax.Formula) (next : Inventory)
40:     (before after : Caller width) (final : Memos) : Prop where
```

## SourceCurrentAllocatedPartialMemoSound

`beginNode_sound`

```lean
179: theorem beginNode_sound (request : NodeRequest) (before : Caller width) (sound : Sound formulas solver before)
180:     (inherited : EqReady before.checked.operations.constraints request.inherited)
181:     (available : Available before.checked.native.machine.heap request.value) :
182:     Sound formulas solver (beginNode request before).2.2 := by
```

`beginEdge_sound`

```lean
192: theorem beginEdge_sound (request : EdgeRequest) (before : Caller width) (sound : Sound formulas solver before)
193:     (inherited : EqReady before.checked.operations.constraints request.inherited)
194:     (resident : Resident before.checked.native.machine.heap request.value) :
195:     Sound formulas solver (beginEdge request before).2.2 := by
```

`finishEdge_sound`

```lean
368: theorem finishEdge_sound (handle : Nat) (original : EdgeRequest) (result : Edge) (before : Caller width)
369:     (sound : Sound formulas solver before)
370:     (running : before.edgeResults.cells handle = some ⟨original, .evaluating⟩)
371:     (resident : Resident before.checked.native.machine.heap result) (law : EdgeLaw formulas solver original result) :
372:     Sound formulas solver (finishEdge handle result before) := by
```

## SourceCurrentAllocatedPartialWorker

`nodeCall`

```lean
62: noncomputable def nodeCall (fuel g s r e p h m c n budget : Nat) (request : NodeRequest)
63:     (before : Caller width) : Outcome Node width :=
```

`edgeCall`

```lean
99: noncomputable def edgeCall (fuel g s r e p h m c n budget : Nat) (request : EdgeRequest)
100:     (before : Caller width) : Outcome Edge width :=
```

`edgeBody`

```lean
111: noncomputable def edgeBody (_fuel g s r e p h m c n budget : Nat) (request : EdgeRequest)
112:     (before : Caller width) : Outcome Edge width :=
```

`rows`

```lean
120: noncomputable def rows (fuel g s r e p h m c n budget : Nat) (inherited : EqValue)
121:     (originals : List Edge) (before : Caller width) : Outcome (List Edge) width :=
```

## SourceCurrentAllocatedPartialWorkerRanges

`nodeCall`

```lean
38: noncomputable def nodeCall (fuel g s r e p h m c n budget : Nat) (request : NodeRequest)
39:     (before : Caller width) : Prop :=
```

`edgeBody`

```lean
65: noncomputable def edgeBody (_fuel g s r e p h m c n budget : Nat) (request : EdgeRequest)
66:     (before : Caller width) : Prop :=
```

`rows`

```lean
74: noncomputable def rows (fuel g s r e p h m c n budget : Nat) (inherited : EqValue)
75:     (originals : List Edge) (before : Caller width) : Prop :=
```

## SourceCurrentAllocatedParentWorkerActual

`ResidentRanges`

```lean
49: def ResidentRanges (budget : Nat) (request : Request) (before : Caller width) : Prop :=
```

`resident_finite`

```lean
182: theorem resident_finite
183:     (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
184:     {inventory : Inventory} {before : Caller width} {memos : Memos}
185:     (budget : Nat) (request : Request) (initial : Context formulas solver inventory before memos)
186:     (inheritedReady : SourceEqualityConstraintAllocation.Ready before.checked.operations.constraints request.inherited)
187:     (resident : Resident before.checked.native.machine.heap request.value)
188:     (ranges : ResidentRanges budget request before) :
189:     ∃ result after savedFourth saved next final,
190:       StableRun (fun g s r e p h m c n => edge g s r e p h m c n budget request.value.entry.key.symbol
191:         request.value.entry.key.constraint request.inherited request.value.children
192:         before.checked before.fourth before.merge) result after savedFourth saved ∧
193:       ∃ actual : SourceCurrentAllocatedPartialGraph.EdgeBody budget request before result
194:           (SourceCurrentAllocatedPartialState.advance before after savedFourth saved),
195:         SourceCurrentAllocatedPartialSourceReads.EdgeBodyReads formulas solver actual memos final ∧
196:         SourceCurrentAllocatedPartialEdgeCall.Receipt formulas solver next request before result
197:           (SourceCurrentAllocatedPartialState.advance before after savedFourth saved) final ∧
198:         Post formulas solver next before (SourceCurrentAllocatedPartialState.advance before after savedFourth saved) final := by
```

## SourceCurrentAllocatedLocalWorkerCompletion

`classes_complete`

```lean
52: theorem classes_complete {budget : Nat} {records : List Record} {values results : List (Value Symbol Guard)}
53:     {before after : Checked width} {fourth savedFourth : Fourth} {memo saved : Memo} {outcome : Option Class}
54:     (actual : SourceCurrentConjunctionScanClassPass.Reduction budget records values before fourth memo
55:       outcome results after savedFourth saved) :
56:     StableRun (fun g s r e p h m c n => classes g s r e p h m c n budget records values before fourth memo)
57:       results after savedFourth saved := by
```

## SourceCurrentConstrainedCapRichRequiredClassPass

`verified`

```lean
38: theorem verified
39:     (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
40:     (inventory : Inventory) (depth : Nat) (records : List SourceEqualityClassOrder.Record)
41:     {selected : EqualityNormalize.Constraints} {originals values results : List (Value Symbol Guard)}
42:     {before after : Checked width} {heap : Heap} {memo saved : Memo} {memos current final : Memos}
43:     (required : SourceCurrentConjunctionRequired.Receipt formulas solver inventory selected originals values before (advanceHeap before heap))
44:     (requiredReads : SourceCurrentRequiredQueryMemos.RequireAllReads (SourceEqualitySelectedRequired.paths selected)
45:       originals values before.native.machine.heap heap memos current)
46:     (selectedEq : records.map SourceEqualityClassOrder.Record.paths = selected)
47:     (coherent : ∀ record ∈ records, SourceEqualityClassOrder.Coherent record)
48:     (active : ∀ record ∈ records, EqualityNormalize.Nontrivial record.paths)
49:     {actual : Pass records values (advanceHeap before heap) memo results after saved}
50:     (reads : PassReads formulas solver actual current final)
51:     (ready : Ready before) (available : Values before.native.machine.heap originals) (closed : ClosedValues originals)
52:     (physicalStored : PhysicalStored before.native.machine.heap memo)
53:     (covered : ∀ ambient, CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
54:     (preparedValid : EndpointMemoGateTrace.Valid heap current)
55:     (native : NativeStored before) (merged : MergeStored memo)
56:     (bounded : ∀ value ∈ originals, Cap depth value)
57:     (supported : ∀ record ∈ records, ∀ path ∈ record.paths, ForestSupported Plain (path.map Int.ofNat) originals) :
58:     ∃ next, SourceCurrentConjunctionRequiredClassPass.Receipt formulas solver next records selected originals values
59:         before (advanceHeap before heap) memo results after saved current final ∧
60:       NativeStored after ∧ MergeStored saved ∧ All₂ (Preserves Plain) originals results ∧
61:       (∀ value ∈ results, Cap depth value) ∧ ClosedValues results := by
```
