# Required numeric final source anchors

These exact current headers use one-based source line numbers.

## SourceCurrentConstrainedCapRequiredResources.lean:21 — HeapFits

```lean
structure HeapFits (profile : Profile) (heap : State Symbol Guard) : Prop where
```

## SourceCurrentConstrainedCapRequiredResources.lean:43 — readFuel

```lean
def readFuel (profile : Profile) : Nat := SourceCurrentOpenRowReadResources.readFuel (scalar profile)
```

## SourceCurrentConstrainedCapRequiredResources.lean:50 — node_width

```lean
theorem node_width {profile : Profile} {heap : State Symbol Guard} (fits : HeapFits profile heap)
    {entry rows depth free} (available : Available heap (.node entry rows depth free)) : rows.length ≤ scalar profile := by
```

## SourceCurrentConstrainedCapRequiredResources.lean:59 — edge_width

```lean
theorem edge_width {profile : Profile} {heap : State Symbol Guard} (fits : HeapFits profile heap)
    (edge : EdgeValue Symbol Guard) (resident : InternedEdgeResidency.EdgeResident heap edge) :
    edge.children.length ≤ scalar profile := by
```

## SourceCurrentConstrainedCapRequiredResources.lean:72 — node

```lean
theorem node (profile : Profile) (count : Nat) (rows : List (EdgeValue Symbol Guard))
    (heap : State Symbol Guard) (fits : HeapFits profile heap) (resident : Edges heap rows)
    (length : rows.length ≤ count) : HeapFits (constructorProfile count profile) (run (makeNode rows) heap).2 := by
```

## SourceCurrentConstrainedCapRequiredResources.lean:79 — edge

```lean
theorem edge (profile : Profile) (count : Nat) (symbol : Symbol) (guard : Guard)
    (values : List (Value Symbol Guard)) (heap : State Symbol Guard) (fits : HeapFits profile heap)
    (available : Values heap values) (length : values.length ≤ count) :
    HeapFits (constructorProfile count profile) (run (makeEdge symbol guard values) heap).2 := by
```

## SourceCurrentConstrainedCapRequiredResources.lean:88 — head

```lean
theorem head (profile : Profile) {value result : Value Symbol Guard} {before after : State Symbol Guard}
    (actual : SourceEqualityRequiredHead.Head value before result after)
    (semantic : SemanticReady before) (costs : InternedFreshOrdinaryCostHeap.Heap before)
    (available : Available before value) (warm : SourceSecondaryGateHead.WarmHead before value)
    (fits : HeapFits profile before) :
    HeapFits (headProfile profile) after ∧
      SourceCurrentProjectionNumericReplay.HeadReady (readFuel (headProfile profile)) actual := by
```

## SourceCurrentConstrainedCapRequiredResources.lean:110 — to_checked

```lean
theorem to_checked {width : Nat} {first last : Profile} {before : Checked width}
    {heap : State CurrentSymbol CurrentGuard} (initial : CheckedFits first before)
    (increase : Le first last) (returned : HeapFits last heap) :
    CheckedFits last (SourceCurrentConjunctionClassScan.advanceHeap before heap) :=
```

## SourceCurrentRequiredNumericReplay.lean:20 — NodeReady

```lean
def NodeReady (shared : Nat) {needed : Needed} {value result : Value Symbol Guard}
    {before after : State Symbol Guard} (_actual : RequireNode needed value before result after) : Prop :=
```

## SourceCurrentRequiredNumericReplay.lean:28 — ChildrenReady

```lean
def ChildrenReady (shared : Nat) {entries : List (Int × Needed)} {index : Nat}
    {values results : List (Value Symbol Guard)} {before after : State Symbol Guard}
    (_actual : RequireChildren entries index values before results after) : Prop :=
```

## SourceCurrentRequiredNumericReplay.lean:35 — RowsReady

```lean
def RowsReady (shared : Nat) {entries : List (Int × Needed)} {edges results : List (EdgeValue Symbol Guard)}
    {before after : State Symbol Guard} (_actual : RequireRows entries edges before results after) : Prop :=
```

## SourceCurrentRequiredNumericReplay.lean:103 — NodeReady.recursive

```lean
theorem NodeReady.recursive {shared : Nat} {entries : List (Int × Needed)}
    {original exposed result : Value Symbol Guard} {before middle after : State Symbol Guard}
    (nonempty : entries ≠ []) (recursive : Recursive original)
    (head : SourceEqualityRequiredHead.Head original before exposed middle)
    (body : RequireNode (.node entries) exposed middle result after)
    (headReady : HeadReady shared head) (bodyReady : NodeReady shared body) :
    NodeReady shared (RequireNode.recursive nonempty recursive head body) := by
```

## SourceCurrentRequiredNumericReplay.lean:138 — ChildrenReady.selected

```lean
theorem ChildrenReady.selected {shared : Nat} {entries : List (Int × Needed)} {index : Nat} {needed : Needed}
    {value result : Value Symbol Guard} {values results : List (Value Symbol Guard)} {before middle after : State Symbol Guard}
    (found : SourceEqualityNeededMap.lookup (index : Int) entries = some needed)
    (first : RequireNode needed value before result middle)
    (rest : RequireChildren entries (index + 1) values middle results after)
    (firstReady : NodeReady shared first) (restReady : ChildrenReady shared rest) :
    ChildrenReady shared (RequireChildren.selected index found first rest) := by
```

## SourceCurrentConstrainedCapRequiredScanResources.lean:29 — ChildBound

```lean
def ChildBound (unconstrained : Value Symbol Guard → Bool) (anchor : State Symbol Guard)
    (entries : List (Int × Needed)) (level : Nat) : Prop :=
```

## SourceCurrentConstrainedCapRequiredScanResources.lean:46 — children

```lean
theorem children (unconstrained : Value Symbol Guard → Bool) (anchor : State Symbol Guard)
    (entries : List (Int × Needed)) (level : Nat) (child : ChildBound unconstrained anchor entries level)
    {index : Nat} {values results : List (Value Symbol Guard)} {before after : State Symbol Guard}
    (actual : RequireChildren entries index values before results after)
    (anchorSemantic : SemanticReady anchor) (semantic : SemanticReady before) (costs : CostHeap before)
    (available : Values before values) (growth : Grows anchor before)
    (support : ChildrenSupport unconstrained anchor entries index values)
    (profile : Profile) (fits : HeapFits profile before) :
    HeapFits (scan (planProfile level) values.length profile) after ∧
      ChildrenReady (readFuel (scan (planProfile level) values.length profile)) actual := by
```

## SourceCurrentConstrainedCapRequiredScanResources.lean:97 — rows

```lean
theorem rows (unconstrained : Value Symbol Guard → Bool) (anchor : State Symbol Guard)
    (entries : List (Int × Needed)) (level width : Nat) (child : ChildBound unconstrained anchor entries level)
    {edges results : List (EdgeValue Symbol Guard)} {before after : State Symbol Guard}
    (actual : RequireRows entries edges before results after)
    (anchorSemantic : SemanticReady anchor) (semantic : SemanticReady before) (costs : CostHeap before)
    (resident : Edges before edges) (growth : Grows anchor before)
    (support : RowsSupport unconstrained anchor (.node entries) edges)
    (widths : ∀ edge ∈ edges, edge.children.length ≤ width)
    (profile : Profile) (widthFits : width ≤ scalar profile) (fits : HeapFits profile before) :
    HeapFits (scan (rowStep level width) edges.length profile) after ∧
      RowsReady (readFuel (scan (rowStep level width) edges.length profile)) actual := by
```

## SourceCurrentConstrainedCapRequiredNumeric.lean:95 — node

```lean
theorem node (unconstrained : Value Symbol Guard → Bool) (anchor : State Symbol Guard)
    (anchorSemantic : SemanticReady anchor) (level : Nat) (needed : Needed)
    (valid : SourceEqualityNeeded.Valid needed)
    (nonnegative : SourceEqualityNeededNonnegative.Nonnegative needed)
    {value result : Value Symbol Guard} {before after : State Symbol Guard}
    (actual : RequireNode needed value before result after) (semantic : SemanticReady before)
    (costs : CostHeap before) (available : Available before value) (growth : Grows anchor before)
    (support : NodeSupport unconstrained anchor needed value) (profile : Profile)
    (fits : HeapFits profile before) (small : sizeOf needed ≤ level) :
    HeapFits (planProfile level profile) after ∧ Replay.NodeReady (readFuel (planProfile level profile)) actual := by
```

## SourceCurrentConstrainedCapRequiredNumeric.lean:149 — at_size

```lean
theorem at_size (unconstrained : Value Symbol Guard → Bool) (anchor : State Symbol Guard)
    (anchorSemantic : SemanticReady anchor) (needed : Needed)
    (valid : SourceEqualityNeeded.Valid needed)
    (nonnegative : SourceEqualityNeededNonnegative.Nonnegative needed)
    {value result : Value Symbol Guard} {before after : State Symbol Guard}
    (actual : RequireNode needed value before result after) (semantic : SemanticReady before)
    (costs : CostHeap before) (available : Available before value) (growth : Grows anchor before)
    (support : NodeSupport unconstrained anchor needed value) (profile : Profile) (fits : HeapFits profile before) :
    HeapFits (planProfile (sizeOf needed) profile) after ∧
      Replay.NodeReady (readFuel (planProfile (sizeOf needed) profile)) actual :=
```

## SourceCurrentConstrainedCapRequiredNumeric.lean:164 — children

```lean
theorem children (unconstrained : Value Symbol Guard → Bool) (anchor : State Symbol Guard)
    (anchorSemantic : SemanticReady anchor) (level : Nat) (entries : List (Int × Needed))
    (valid : SourceEqualityNeeded.Valid (.node entries))
    (nonnegative : SourceEqualityNeededNonnegative.Nonnegative (.node entries))
    {values results : List (Value Symbol Guard)} {before after : State Symbol Guard}
    (actual : RequireChildren entries 0 values before results after)
    (semantic : SemanticReady before) (costs : CostHeap before) (available : Values before values)
    (growth : Grows anchor before)
    (support : SourceCurrentRequiredSupport.ForestSupport unconstrained anchor (.node entries) values)
    (profile : Profile) (fits : HeapFits profile before) (small : sizeOf (Needed.node entries) ≤ level) :
    HeapFits (scan (planProfile level) values.length profile) after ∧
      Replay.ChildrenReady (readFuel (scan (planProfile level) values.length profile)) actual := by
```

## SourceCurrentConstrainedCapRequiredInitialNumeric.lean:33 — forecast

```lean
noncomputable def forecast (paths : List (List Int)) (count : Nat) (profile : Profile) : Profile :=
```

## SourceCurrentConstrainedCapRequiredInitialNumeric.lean:38 — forecast_ge

```lean
theorem forecast_ge (paths : List (List Int)) (count : Nat) (profile : Profile) : Le profile (forecast paths count profile) :=
```

## SourceCurrentConstrainedCapRequiredInitialNumeric.lean:43 — workerFuel

```lean
noncomputable def workerFuel (paths : List (List Int)) : Nat :=
```

## SourceCurrentConstrainedCapRequiredInitialNumeric.lean:47 — readerFuel

```lean
noncomputable def readerFuel (paths : List (List Int)) (count : Nat) (profile : Profile) : Nat :=
```

## SourceCurrentConstrainedCapRequiredInitialNumeric.lean:53 — at_requireAll

```lean
theorem at_requireAll (unconstrained : Value Symbol Guard → Bool) (anchor : State Symbol Guard)
    (anchorSemantic : SemanticReady anchor) (oldFuel oldRead : Nat) (paths : List (List Int))
    (indices : ∀ path ∈ paths, ∀ index ∈ path, 0 ≤ index)
    (values results : List (Value Symbol Guard)) (before after : State Symbol Guard)
    (done : SourceEqualityRequiredExecution.requireAll oldFuel oldRead paths values before = .done results after)
    (semantic : SemanticReady before) (costs : InternedFreshOrdinaryCostHeap.Heap before)
    (available : Values before values) (growth : Grows anchor before)
    (support : SourceCurrentRequiredSupport.ForestSupport unconstrained anchor (SourceEqualityNeeded.build paths) values)
    (profile : Profile) (fits : SourceCurrentConstrainedCapRequiredResources.HeapFits profile before) :
    SourceCurrentConstrainedCapRequiredResources.HeapFits (forecast paths values.length profile) after ∧
      ∀ worker reader, workerFuel paths ≤ worker → readerFuel paths values.length profile ≤ reader →
        SourceEqualityRequiredExecution.requireAll worker reader paths values before = .done results after := by
```

## SourceCurrentConstrainedCapRequiredInitialNumeric.lean:84 — complete

```lean
theorem complete (depth : Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (unconstrained reaches : Value Symbol Guard → Bool)
    (selected : EqualityNormalize.Constraints) (values : List (Value Symbol Guard)) (before : Checked width)
    (frame : Frame formulas solver inventory before) (profile : Profile) (fits : Fits profile before)
    (available : Values before.native.machine.heap values)
    (proper : ∀ path ∈ selected.flatten, path ≠ [])
    (primary : ∀ paths ∈ selected, EndpointStatefulGateTrace.ClassTrace unconstrained reaches values paths
      before.native.machine.heap false before.native.machine.heap)
    (caps : ∀ value ∈ values, Cap depth value) (memos : Memos) (valid : Valid before.native.machine.heap memos) :
    ∃ results heap final,
      SourceCurrentConjunctionRequired.Receipt formulas solver inventory selected values results before (advanceHeap before heap) ∧
      SourceCurrentRequiredQueryMemos.RequireAllReads (SourceEqualitySelectedRequired.paths selected)
        values results before.native.machine.heap heap memos final ∧
      Frame formulas solver inventory (advanceHeap before heap) ∧
      SourceCurrentSubsumesQueryMemos.Effect before.native.machine.heap heap memos final ∧
      (∀ value ∈ results, Cap depth value) ∧ results.length = values.length ∧
      Fits (forecast (SourceEqualitySelectedRequired.paths selected) values.length profile) (advanceHeap before heap) ∧
      SourceEqualityRequiredExecution.requireAll (workerFuel (SourceEqualitySelectedRequired.paths selected))
        (readerFuel (SourceEqualitySelectedRequired.paths selected) values.length profile)
        (SourceEqualitySelectedRequired.paths selected) values before.native.machine.heap = .done results heap ∧
      (∀ worker reader, workerFuel (SourceEqualitySelectedRequired.paths selected) ≤ worker →
        readerFuel (SourceEqualitySelectedRequired.paths selected) values.length profile ≤ reader →
        SourceEqualityRequiredExecution.requireAll worker reader (SourceEqualitySelectedRequired.paths selected)
          values before.native.machine.heap = .done results heap) := by
```

## SourceCurrentConstrainedCapRequiredInitialNumeric.lean:123 — caller

```lean
theorem caller (depth : Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (unconstrained reaches : Value Symbol Guard → Bool)
    (selected : EqualityNormalize.Constraints) (values : List (Value Symbol Guard)) (before : Caller width)
    (memos : Memos) (initial : Context formulas solver inventory before memos)
    (frame : Frame formulas solver inventory before.checked) (profile : Profile) (fits : Fits profile before.checked)
    (available : Values before.checked.native.machine.heap values)
    (proper : ∀ path ∈ selected.flatten, path ≠ [])
    (primary : ∀ paths ∈ selected, EndpointStatefulGateTrace.ClassTrace unconstrained reaches values paths
      before.checked.native.machine.heap false before.checked.native.machine.heap)
    (caps : ∀ value ∈ values, Cap depth value) :
    ∃ results heap final,
      SourceCurrentConjunctionRequired.Receipt formulas solver inventory selected values results before.checked
        (advanceHeap before.checked heap) ∧
      SourceCurrentRequiredQueryMemos.RequireAllReads (SourceEqualitySelectedRequired.paths selected)
        values results before.checked.native.machine.heap heap memos final ∧
      Frame formulas solver inventory (advanceHeap before.checked heap) ∧
      Post formulas solver inventory before (advance before (advanceHeap before.checked heap) before.fourth before.merge) final ∧
      (∀ value ∈ results, Cap depth value) ∧ results.length = values.length ∧
      Fits (forecast (SourceEqualitySelectedRequired.paths selected) values.length profile) (advanceHeap before.checked heap) ∧
      (advance before (advanceHeap before.checked heap) before.fourth before.merge).nodeResults = before.nodeResults ∧
      (advance before (advanceHeap before.checked heap) before.fourth before.merge).edgeResults = before.edgeResults ∧
      (advance before (advanceHeap before.checked heap) before.fourth before.merge).fourth = before.fourth ∧
      (advance before (advanceHeap before.checked heap) before.fourth before.merge).merge = before.merge ∧
      SourceEqualityRequiredExecution.requireAll (workerFuel (SourceEqualitySelectedRequired.paths selected))
        (readerFuel (SourceEqualitySelectedRequired.paths selected) values.length profile)
        (SourceEqualitySelectedRequired.paths selected) values before.checked.native.machine.heap = .done results heap ∧
      (∀ worker reader, workerFuel (SourceEqualitySelectedRequired.paths selected) ≤ worker →
        readerFuel (SourceEqualitySelectedRequired.paths selected) values.length profile ≤ reader →
        SourceEqualityRequiredExecution.requireAll worker reader (SourceEqualitySelectedRequired.paths selected)
          values before.checked.native.machine.heap = .done results heap) := by
```

## SourceCurrentRequiredWorkerNumeric.lean:21 — workFuel

```lean
noncomputable def workFuel (needed : Needed) : Nat := 2 * sizeOf needed + 1
```

## SourceCurrentConstrainedCapRequiredForecast.lean:65 — planProfile

```lean
def planProfile : Nat → Profile → Profile
  | 0, profile => stageProfile profile
  | level + 1, profile =>
      let start := stageProfile profile
```

## SourceCurrentConstrainedCapRequiredForecast.lean:106 — plan_mono

```lean
theorem plan_mono (level : Nat)
    {first last : Profile} (increase : Le first last) :
    Le (planProfile level first) (planProfile level last) := by
```

## SourceCurrentSecondaryProjectionSupport.lean:115 — Support

```lean
def Support [DecidableEq (EdgeKey Symbol Guard)] (unconstrained : Value Symbol Guard → Bool)
    (anchor : State Symbol Guard) (path : Path) (value : Value Symbol Guard) : Prop :=
```

## SourceCurrentSecondaryProjectionSupport.lean:120 — support_warm_head

```lean
theorem support_warm_head [DecidableEq (EdgeKey Symbol Guard)]
    {unconstrained : Value Symbol Guard → Bool} {anchor : State Symbol Guard} {path : Path} {value : Value Symbol Guard}
    (support : Support unconstrained anchor path value) (semantic : SemanticReady anchor)
    (caller : State Symbol Guard) (growth : Grows anchor caller) : SourceSecondaryGateHead.WarmHead caller value := by
```

## SourceCurrentRequiredTipSupport.lean:94 — selected_domain

```lean
theorem selected_domain [DecidableEq (EdgeKey Symbol Guard)]
    {unconstrained reaches : Value Symbol Guard → Bool}
    {values : List (Value Symbol Guard)} {selected : Constraints} {state : State Symbol Guard}
    (semantic : SemanticReady state) (available : Values state values)
    (primary : ∀ paths ∈ selected,
      EndpointStatefulGateTrace.ClassTrace unconstrained reaches values paths state false state) :
    ForestTips unconstrained state (build (SourceEqualitySelectedRequired.paths selected)) values := by
```

## SourceCurrentRequiredTipSupport.lean:124 — head_rows

```lean
theorem head_rows [DecidableEq (EdgeKey Symbol Guard)]
    {unconstrained : Value Symbol Guard → Bool} {anchor caller after : State Symbol Guard}
    {needed : Needed} {original exposed : Value Symbol Guard}
    (tips : NodeTips unconstrained anchor needed original)
    (anchorSemantic : SemanticReady anchor) (semantic : SemanticReady caller)
    (available : Available caller original) (growth : Grows anchor caller)
    (actual : SourceEqualityRequiredHead.Head original caller exposed after) :
    ∀ edge ∈ InternedEdgeResidency.nodeEdges exposed,
      ForestTips unconstrained anchor needed edge.children := by
```

## SourceCurrentConstrainedCapSelectedRequiredComplete.lean:34 — complete

```lean
theorem complete (depth : Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (unconstrained reaches : Value Symbol Guard → Bool)
    (selected : EqualityNormalize.Constraints) (values : List (Value Symbol Guard)) (before : Checked width)
    (frame : Frame formulas solver inventory before) (available : Values before.native.machine.heap values)
    (proper : ∀ path ∈ selected.flatten, path ≠ [])
    (primary : ∀ paths ∈ selected, EndpointStatefulGateTrace.ClassTrace unconstrained reaches values paths
      before.native.machine.heap false before.native.machine.heap)
    (caps : ∀ value ∈ values, Cap depth value) (memos : Memos) (valid : Valid before.native.machine.heap memos) :
    ∃ results heap final fuel readFuel,
      SourceCurrentConjunctionRequired.Receipt formulas solver inventory selected values results before
        (advanceHeap before heap) ∧
      SourceCurrentRequiredQueryMemos.RequireAllReads (SourceEqualitySelectedRequired.paths selected)
        values results before.native.machine.heap heap memos final ∧
      Frame formulas solver inventory (advanceHeap before heap) ∧
      SourceCurrentSubsumesQueryMemos.Effect before.native.machine.heap heap memos final ∧
      (∀ value ∈ results, Cap depth value) ∧ results.length = values.length ∧
      SourceEqualityRequiredExecution.requireAll fuel readFuel (SourceEqualitySelectedRequired.paths selected)
        values before.native.machine.heap = .done results heap := by
```

## SourceCurrentConstrainedCapSelectedRequiredComplete.lean:69 — caller

```lean
theorem caller (depth : Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (unconstrained reaches : Value Symbol Guard → Bool)
    (selected : EqualityNormalize.Constraints) (values : List (Value Symbol Guard)) (before : Caller width)
    (memos : Memos) (initial : Context formulas solver inventory before memos)
    (frame : Frame formulas solver inventory before.checked)
    (available : Values before.checked.native.machine.heap values)
    (proper : ∀ path ∈ selected.flatten, path ≠ [])
    (primary : ∀ paths ∈ selected, EndpointStatefulGateTrace.ClassTrace unconstrained reaches values paths
      before.checked.native.machine.heap false before.checked.native.machine.heap)
    (caps : ∀ value ∈ values, Cap depth value) :
    ∃ results heap final fuel readFuel,
      SourceCurrentConjunctionRequired.Receipt formulas solver inventory selected values results before.checked
        (advanceHeap before.checked heap) ∧
      SourceCurrentRequiredQueryMemos.RequireAllReads (SourceEqualitySelectedRequired.paths selected)
        values results before.checked.native.machine.heap heap memos final ∧
      Frame formulas solver inventory (advanceHeap before.checked heap) ∧
      Post formulas solver inventory before (advance before (advanceHeap before.checked heap) before.fourth before.merge) final ∧
      (∀ value ∈ results, Cap depth value) ∧ results.length = values.length ∧
      (advance before (advanceHeap before.checked heap) before.fourth before.merge).nodeResults = before.nodeResults ∧
      (advance before (advanceHeap before.checked heap) before.fourth before.merge).edgeResults = before.edgeResults ∧
      (advance before (advanceHeap before.checked heap) before.fourth before.merge).fourth = before.fourth ∧
      (advance before (advanceHeap before.checked heap) before.fourth before.merge).merge = before.merge ∧
      SourceEqualityRequiredExecution.requireAll fuel readFuel (SourceEqualitySelectedRequired.paths selected)
        values before.checked.native.machine.heap = .done results heap := by
```

## SourceCurrentRequiredQueryMemos.lean:285 — RequireAllReads

```lean
def RequireAllReads [DecidableEq (EdgeKey Symbol Guard)]
    (paths : List (List Int)) (values results : List (Value Symbol Guard)) (before after : State Symbol Guard)
    (memos saved : Memos) : Prop :=
```

## SourceEqualityRequiredWorker.lean:76 — require

```lean
def require [DecidableEq (EdgeKey Symbol Guard)] : Nat → Nat → Needed → Value Symbol Guard → State Symbol Guard →
    Result Symbol Guard (Value Symbol Guard)
  | 0, _, _, _, state => .exhausted .worker state
  | fuel + 1, readFuel, .node entries, value, state =>
      if entries.isEmpty then .done value state else
      match value with
      | .empty => .done .empty state
      | .reference name => .unresolved name state
      | .node _ edges _ _ => (rows (require fuel readFuel) entries edges state).bind fun rebuilt after => work (makeNode rebuilt) after
      | value@(.mu ..) | value@(.union ..) =>
          (head readFuel value state).bind fun exposed after => require fuel readFuel (.node entries) exposed after

/-- Empty source requirements return before inspecting an unresolved reference. -/
theorem identity [DecidableEq (EdgeKey Symbol Guard)] (fuel readFuel : Nat)
    (value : Value Symbol Guard) (state : State Symbol Guard) :
    require (fuel + 1) readFuel (.node []) value state = .done value state := rfl
```

## SourceEqualityRequiredGraph.lean:70 — RequireChildren.length

```lean
theorem RequireChildren.length [DecidableEq (EdgeKey Symbol Guard)]
    {entries : List (Int × Needed)} {index : Nat} {values results : List (Value Symbol Guard)}
    {before after : State Symbol Guard} (trace : RequireChildren entries index values before results after) :
    results.length = values.length := by
```

## SourceCurrentConstrainedCapGeneratedQueryResources.lean:33 — Fits

```lean
structure Fits (profile : Profile) (state : Checked width) : Prop where
```

## SourceCurrentConstrainedCapGeneratedQueryResources.lean:62 — Frame

```lean
structure Frame (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory) (state : Checked width) : Prop where
```

## Operations.hs:279 — requireAll

```haskell
requireAll ::
    forall symbol.
    (Hashable symbol, Typeable symbol) =>
    Set Path -> [Node symbol] -> [Node symbol]
requireAll paths = requireList (foldr insertNeeded (Needed IntMap.empty) paths)
  where
    insertNeeded EmptyPath needed = needed
    insertNeeded (ConsPath (ChildIndex index) rest) (Needed children) =
        Needed $ IntMap.alter (Just . insertNeeded rest . fromMaybe (Needed IntMap.empty)) index children

    requireList :: Needed -> [Node symbol] -> [Node symbol]
    requireList (Needed children) ns = IntMap.foldrWithKey (\index needed -> adjustAt (ChildIndex index) (requireNode needed)) ns children

    requireNode :: Needed -> Node symbol -> Node symbol
    requireNode (Needed children) n | IntMap.null children = n
    requireNode _ EmptyNode = EmptyNode
    requireNode needed n@(Mu _) = requireNode needed (Node $ nodeEdges n)
    requireNode needed n@(InternedUnion _) = requireNode needed (Node $ nodeEdges n)
    requireNode needed@(Needed children) (Node es) =
        Node
            [ setChildren e (requireList needed (edgeChildren e))
            | e <- es
            , compareLength (edgeChildren e) (fst (IntMap.findMax children)) == GT
            ]
    requireNode _ (Rec _) = error "requireAll: unexpected Rec"
```
