# Required source and numeric contract anchors

These are exact current source headers. Line numbers are one-based.

## SourceEqualityNeeded.lean:17 — Needed

```lean
inductive Needed where
```

## SourceEqualityNeeded.lean:31 — build

```lean
def build (paths : List Path) : Needed := paths.foldr insert empty
```

## SourceEqualityNeeded.lean:108 — demands_build

```lean
theorem demands_build (paths : List Path) (query : Path) :
    demands (build paths) query = true ↔
      query = [] ∨ ∃ path ∈ paths, query.IsPrefix path := by
```

## SourceEqualityRequiredWorker.lean:52 — children

```lean
def children (recur : Needed → Value Symbol Guard → State Symbol Guard → Result Symbol Guard (Value Symbol Guard))
    (entries : List (Int × Needed)) : Nat → List (Value Symbol Guard) → State Symbol Guard →
      Result Symbol Guard (List (Value Symbol Guard))
  | _, [], state => .done [] state
  | index, value :: rest, state =>
      match SourceEqualityNeededMap.lookup (index : Int) entries with
      | none => (children recur entries (index + 1) rest state).bind fun results after => .done (value :: results) after
      | some needed => (recur needed value state).bind fun result middle =>
          (children recur entries (index + 1) rest middle).bind fun results after => .done (result :: results) after

/-- Reject a missing required position before child work or edge reconstruction. -/
def rows [DecidableEq (EdgeKey Symbol Guard)]
    (recur : Needed → Value Symbol Guard → State Symbol Guard → Result Symbol Guard (Value Symbol Guard))
    (entries : List (Int × Needed)) : List (EdgeValue Symbol Guard) → State Symbol Guard →
      Result Symbol Guard (List (EdgeValue Symbol Guard))
  | [], state => .done [] state
  | edge :: rest, state =>
      if fits (.node entries) edge.children.length then
        (children recur entries 0 edge.children state).bind fun values middle =>
          (work (makeEdge edge.entry.key.symbol edge.entry.key.constraint values) middle).bind fun result afterEdge =>
            (rows recur entries rest afterEdge).bind fun results after => .done (result :: results) after
      else rows recur entries rest state

/-- Follow source branch priority with a separate bound for repeated recursive calls. -/
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

## SourceEqualityRequiredWorker.lean:63 — rows

```lean
def rows [DecidableEq (EdgeKey Symbol Guard)]
    (recur : Needed → Value Symbol Guard → State Symbol Guard → Result Symbol Guard (Value Symbol Guard))
    (entries : List (Int × Needed)) : List (EdgeValue Symbol Guard) → State Symbol Guard →
      Result Symbol Guard (List (EdgeValue Symbol Guard))
  | [], state => .done [] state
  | edge :: rest, state =>
      if fits (.node entries) edge.children.length then
        (children recur entries 0 edge.children state).bind fun values middle =>
          (work (makeEdge edge.entry.key.symbol edge.entry.key.constraint values) middle).bind fun result afterEdge =>
            (rows recur entries rest afterEdge).bind fun results after => .done (result :: results) after
      else rows recur entries rest state

/-- Follow source branch priority with a separate bound for repeated recursive calls. -/
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

## SourceEqualityRequiredWorker.lean:89 — identity

```lean
theorem identity [DecidableEq (EdgeKey Symbol Guard)] (fuel readFuel : Nat)
    (value : Value Symbol Guard) (state : State Symbol Guard) :
    require (fuel + 1) readFuel (.node []) value state = .done value state := rfl
```

## SourceEqualityRequiredWorker.lean:94 — unresolved

```lean
theorem unresolved [DecidableEq (EdgeKey Symbol Guard)] (fuel readFuel : Nat)
    (entries : List (Int × Needed)) (nonempty : entries ≠ []) (name : InternedBinderProtocol.Reference)
    (state : State Symbol Guard) :
    require (fuel + 1) readFuel (.node entries) (.reference name) state = .unresolved name state := by
```

## SourceEqualityRequiredGraph.lean:22 — Recursive

```lean
def Recursive : Value Symbol Guard → Prop
  | .mu .. | .union .. => True
  | _ => False

mutual
  /-- One physical required-node request, with exact source branch priority. -/
  inductive RequireNode [DecidableEq (EdgeKey Symbol Guard)] :
      Needed → Value Symbol Guard → State Symbol Guard → Value Symbol Guard → State Symbol Guard → Prop where
```

## SourceEqualityRequiredGraph.lean:70 — RequireChildren.length

```lean
theorem RequireChildren.length [DecidableEq (EdgeKey Symbol Guard)]
    {entries : List (Int × Needed)} {index : Nat} {values results : List (Value Symbol Guard)}
    {before after : State Symbol Guard} (trace : RequireChildren entries index values before results after) :
    results.length = values.length := by
```

## SourceEqualityRequiredHead.lean:16 — Head

```lean
inductive Head [DecidableEq (EdgeKey Symbol Guard)] :
    Value Symbol Guard → State Symbol Guard → Value Symbol Guard → State Symbol Guard → Prop where
```

## SourceEqualityRequiredHead.lean:35 — Head.unique

```lean
theorem Head.unique [DecidableEq (EdgeKey Symbol Guard)]
    {value first second : Value Symbol Guard} {before afterFirst afterSecond : State Symbol Guard}
    (left : Head value before first afterFirst) (right : Head value before second afterSecond) :
    first = second ∧ afterFirst = afterSecond := by
```

## SourceCurrentRequiredSupport.lean:88 — NodeSupport

```lean
def NodeSupport [DecidableEq (EdgeKey Symbol Guard)]
    (unconstrained : Value Symbol Guard → Bool) (anchor : State Symbol Guard)
    (needed : Needed) (value : Value Symbol Guard) : Prop :=
```

## SourceCurrentRequiredSupport.lean:94 — ForestSupport

```lean
def ForestSupport [DecidableEq (EdgeKey Symbol Guard)]
    (unconstrained : Value Symbol Guard → Bool) (anchor : State Symbol Guard)
    (needed : Needed) (values : List (Value Symbol Guard)) : Prop :=
```

## SourceCurrentRequiredSupport.lean:108 — empty_support

```lean
theorem empty_support [DecidableEq (EdgeKey Symbol Guard)]
    (unconstrained : Value Symbol Guard → Bool) (anchor : State Symbol Guard) (value : Value Symbol Guard) :
    NodeSupport unconstrained anchor (.node []) value := by
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

## SourceCurrentRequiredTipSupport.lean:109 — ordinary_rows

```lean
theorem ordinary_rows [DecidableEq (EdgeKey Symbol Guard)]
    {unconstrained : Value Symbol Guard → Bool} {anchor caller : State Symbol Guard}
    {needed : Needed} {entry : Cache.Interned InternedBinderProtocol.NodeKey}
    {edges : List (EdgeValue Symbol Guard)} {depth : Nat} {free : List InternedBinderProtocol.Reference}
    (tips : NodeTips unconstrained anchor needed (.node entry edges depth free))
    (anchorSemantic : SemanticReady anchor) (semantic : SemanticReady caller)
    (available : Available caller (.node entry edges depth free)) :
    ∀ edge ∈ edges, ForestTips unconstrained anchor needed edge.children := by
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

## SourceSecondaryGateHead.lean:23 — WarmHead

```lean
inductive WarmHead [DecidableEq (EdgeKey Symbol Guard)] (state : State Symbol Guard) :
    Value Symbol Guard → Prop where
```

## SourceSecondaryGateHead.lean:142 — warm_nodeEdges_complete

```lean
theorem warm_nodeEdges_complete [DecidableEq (EdgeKey Symbol Guard)]
    {state : State Symbol Guard} {value : Value Symbol Guard} (support : WarmHead state value)
    (semantic : SemanticReady state) (available : Available state value) :
    ∃ fuel edges after, nodeEdges fuel value state = .done edges after ∧ Keeps state after ∧
      SemanticReady after ∧ Edges after edges := by
```

## SourceCurrentRequiredComplete.lean:133 — node_complete

```lean
theorem node_complete [DecidableEq (EdgeKey Symbol Guard)]
    (unconstrained : Value Symbol Guard → Bool) (anchor : State Symbol Guard) (anchorSemantic : SemanticReady anchor)
    (needed : Needed) (valid : SourceEqualityNeeded.Valid needed)
    (nonnegative : SourceEqualityNeededNonnegative.Nonnegative needed)
    (value : Value Symbol Guard) (before : State Symbol Guard) (semantic : SemanticReady before)
    (available : Available before value) (growth : Grows anchor before)
    (support : NodeSupport unconstrained anchor needed value) :
    ∃ result after, RequireNode needed value before result after ∧ Keeps before after ∧
      SemanticReady after ∧ Available after result := by
```

## SourceCurrentRequiredComplete.lean:199 — requireAll_complete

```lean
theorem requireAll_complete [DecidableEq (EdgeKey Symbol Guard)]
    (unconstrained : Value Symbol Guard → Bool) (anchor : State Symbol Guard) (anchorSemantic : SemanticReady anchor)
    (paths : List (List Int)) (indices : ∀ path ∈ paths, ∀ index ∈ path, 0 ≤ index)
    (values : List (Value Symbol Guard)) (before : State Symbol Guard) (semantic : SemanticReady before)
    (available : Values before values) (growth : Grows anchor before)
    (support : ForestSupport unconstrained anchor (build paths) values) :
    ∃ results after, Keeps before after ∧ SemanticReady after ∧ Values after results ∧
      SourceEqualityRequiredWorkerComplete.StableRun
        (fun fuel readFuel => SourceEqualityRequiredExecution.requireAll fuel readFuel paths values before) results after := by
```

## SourceCurrentConstrainedCapSelectedRequired.lean:175 — node

```lean
theorem node [DecidableEq (EdgeKey Symbol Guard)] (valid : Guard → Prop) (capDepth : Nat)
    {needed : SourceEqualityNeeded.Needed} {value result : Value Symbol Guard} {before after : State Symbol Guard}
    (actual : RequireNode needed value before result after) (semantic : SemanticReady before) (costs : CostHeap before)
    (available : Available before value) (stored : GuardHeap valid before) (annotated : Cap valid capDepth value) :
    GuardHeap valid after ∧ Cap valid capDepth result :=
```

## SourceCurrentConstrainedCapSelectedRequired.lean:183 — children

```lean
theorem children [DecidableEq (EdgeKey Symbol Guard)] (valid : Guard → Prop) (capDepth : Nat)
    {entries : List (Int × SourceEqualityNeeded.Needed)} {index : Nat} {values results : List (Value Symbol Guard)} {before after : State Symbol Guard}
    (actual : RequireChildren entries index values before results after) (semantic : SemanticReady before) (costs : CostHeap before)
    (available : Values before values) (stored : GuardHeap valid before) (annotated : ∀ value ∈ values, Cap valid capDepth value) :
    GuardHeap valid after ∧ ∀ value ∈ results, Cap valid capDepth value :=
```

## SourceCurrentConstrainedCapSelectedRequired.lean:191 — rows

```lean
theorem rows [DecidableEq (EdgeKey Symbol Guard)] (valid : Guard → Prop) (capDepth : Nat)
    {entries : List (Int × SourceEqualityNeeded.Needed)} {edges results : List (EdgeValue Symbol Guard)} {before after : State Symbol Guard}
    (actual : RequireRows entries edges before results after) (semantic : SemanticReady before) (costs : CostHeap before)
    (resident : Edges before edges) (stored : GuardHeap valid before)
    (annotated : ∀ edge ∈ edges, Edge valid capDepth edge) :
    GuardHeap valid after ∧ ∀ edge ∈ results, Edge valid capDepth edge :=
```

## SourceCurrentConstrainedCapSelectedRequired.lean:203 — requireAll

```lean
theorem requireAll [DecidableEq (EdgeKey CurrentSymbol CurrentGuard)] (valid : CurrentGuard → Prop) (capDepth : Nat) {paths : List (List Int)}
    {values results : List (Value CurrentSymbol CurrentGuard)} {before after : State CurrentSymbol CurrentGuard}
    {memos saved : EndpointMemoGateTrace.Memos}
    (reads : SourceCurrentRequiredQueryMemos.RequireAllReads paths values results before after memos saved)
    (semantic : SemanticReady before) (costs : CostHeap before) (available : Values before values)
    (stored : GuardHeap valid before) (annotated : ∀ value ∈ values, Cap valid capDepth value) :
    GuardHeap valid after ∧ (∀ value ∈ results, Cap valid capDepth value) ∧ results.length = values.length := by
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

## SourceCurrentRequiredWorkerNumeric.lean:21 — workFuel

```lean
noncomputable def workFuel (needed : Needed) : Nat := 2 * sizeOf needed + 1
```

## SourceCurrentRequiredWorkerNumeric.lean:130 — node

```lean
theorem node (needed : Needed) {value result : Value Symbol Guard} {before after : State Symbol Guard}
    (actual : RequireNode needed value before result after) (semantic : SemanticReady before)
    (costs : CostHeap before) (available : Available before value) :
    ∃ headBound, ∀ worker reader, workFuel needed ≤ worker → headBound ≤ reader →
      require worker reader needed value before = .done result after := by
```

## SourceCurrentRequiredWorkerNumeric.lean:183 — children

```lean
theorem children (entries : List (Int × Needed)) {index : Nat}
    {values results : List (Value Symbol Guard)} {before after : State Symbol Guard}
    (actual : RequireChildren entries index values before results after) (semantic : SemanticReady before)
    (costs : CostHeap before) (available : Values before values) :
    ∃ headBound, ∀ worker reader, workFuel (.node entries) ≤ worker → headBound ≤ reader →
      SourceEqualityRequiredWorker.children (require worker reader) entries index values before = .done results after := by
```

## SourceCurrentRequiredWorkerNumeric.lean:198 — requireAll

```lean
theorem requireAll (oldFuel oldRead : Nat) (paths : List (List Int))
    (values results : List (Value Symbol Guard)) (before after : State Symbol Guard)
    (done : SourceEqualityRequiredExecution.requireAll oldFuel oldRead paths values before = .done results after)
    (semantic : SemanticReady before) (costs : CostHeap before) (available : Values before values) :
    ∃ headBound, ∀ worker reader, workFuel (SourceEqualityNeeded.build paths) ≤ worker → headBound ≤ reader →
      SourceEqualityRequiredExecution.requireAll worker reader paths values before = .done results after := by
```

## SourceCurrentConstrainedCapSelectedRequiredWorker.lean:30 — complete

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
    ∃ results heap final readFuel,
      SourceCurrentConjunctionRequired.Receipt formulas solver inventory selected values results before
        (advanceHeap before heap) ∧
      SourceCurrentRequiredQueryMemos.RequireAllReads (SourceEqualitySelectedRequired.paths selected)
        values results before.native.machine.heap heap memos final ∧
      Frame formulas solver inventory (advanceHeap before heap) ∧
      SourceCurrentSubsumesQueryMemos.Effect before.native.machine.heap heap memos final ∧
      (∀ value ∈ results, Cap depth value) ∧ results.length = values.length ∧
      (∀ worker reader,
        SourceCurrentRequiredWorkerNumeric.workFuel (SourceEqualityNeeded.build (SourceEqualitySelectedRequired.paths selected)) ≤ worker →
        readFuel ≤ reader → SourceEqualityRequiredExecution.requireAll worker reader (SourceEqualitySelectedRequired.paths selected)
          values before.native.machine.heap = .done results heap) := by
```

## SourceCurrentConstrainedCapSelectedRequiredWorker.lean:60 — caller

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
    ∃ results heap final readFuel,
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
      (∀ worker reader,
        SourceCurrentRequiredWorkerNumeric.workFuel (SourceEqualityNeeded.build (SourceEqualitySelectedRequired.paths selected)) ≤ worker →
        readFuel ≤ reader → SourceEqualityRequiredExecution.requireAll worker reader (SourceEqualitySelectedRequired.paths selected)
          values before.checked.native.machine.heap = .done results heap) := by
```

## SourceCurrentOpenRowReadResources.lean:27 — readFuel

```lean
def readFuel (bound : Nat) : Nat := bound + SourceCurrentProjectionUnionResources.readFuel bound + 1
```

## SourceCurrentOpenRowReadResources.lean:29 — readWidth

```lean
def readWidth (bound : Nat) : Nat := bound + SourceCurrentProjectionUnionResources.readWidth bound
```

## SourceCurrentOpenRowReadResources.lean:31 — readGrowth

```lean
def readGrowth (bound : Nat) : Nat := bound + SourceCurrentProjectionUnionResources.readFuel bound + readWidth bound
```

## SourceCurrentOpenRowReadResources.lean:33 — headGrowth

```lean
def headGrowth (bound : Nat) : Nat := primitiveGrowth (readWidth bound) (readGrowth bound)
```

## SourceCurrentOpenRowReadResources.lean:230 — complete

```lean
theorem complete (value : Value Symbol Guard) (heap : State Symbol Guard) (bound : Nat)
    (semantic : SemanticReady heap) (available : Available heap value) (warm : WarmHead heap value)
    (fits : Fits bound heap) :
    ∃ rows after, nodeEdges (readFuel bound) value heap = .done rows after ∧
      SourceEqualityProjectionRead.Read value heap rows after ∧
      Keeps heap after ∧ SemanticReady after ∧ Fits (readGrowth bound) after ∧
      rows.length ≤ readWidth bound ∧ Edges after rows ∧
      ∀ extra, nodeEdges (readFuel bound + extra) value heap = .done rows after := by
```

## SourceCurrentOpenRowReadResources.lean:250 — read

```lean
theorem read {value : Value Symbol Guard} {before after : State Symbol Guard}
    {rows : List (EdgeValue Symbol Guard)} (actual : SourceEqualityProjectionRead.Read value before rows after)
    (bound : Nat) (semantic : SemanticReady before) (costs : CostHeap before)
    (available : Available before value) (warm : WarmHead before value) (fits : Fits bound before) :
    Effect before after ∧ Fits (readGrowth bound) after ∧ rows.length ≤ readWidth bound ∧
      Edges after rows ∧ SourceCurrentProjectionNumericReplay.ReadReady (readFuel bound) actual ∧
      ∀ extra, nodeEdges (readFuel bound + extra) value before = .done rows after := by
```

## SourceCurrentOpenRowReadResources.lean:275 — head

```lean
theorem head {value result : Value Symbol Guard} {before after : State Symbol Guard}
    (actual : SourceEqualityRequiredHead.Head value before result after)
    (bound : Nat) (semantic : SemanticReady before) (costs : CostHeap before)
    (available : Available before value) (warm : WarmHead before value) (fits : Fits bound before) :
    Effect before after ∧ Fits (headGrowth bound) after ∧ Available after result ∧
      SourceEqualityRequiredCache.Ordinary result ∧
      SourceCurrentProjectionNumericReplay.HeadReady (readFuel (headGrowth bound)) actual := by
```

## SourceCurrentConstrainedCapRequiredForecast.lean:23 — headProfile

```lean
def headProfile (profile : Profile) : Profile :=
```

## SourceCurrentConstrainedCapRequiredForecast.lean:43 — stageProfile

```lean
def stageProfile (profile : Profile) : Profile :=
```

## SourceCurrentConstrainedCapRequiredForecast.lean:65 — planProfile

```lean
def planProfile : Nat → Profile → Profile
  | 0, profile => stageProfile profile
  | level + 1, profile =>
      let start := stageProfile profile
```

## SourceCurrentConstrainedCapRequiredForecast.lean:74 — rowStep

```lean
def rowStep (level width : Nat) (profile : Profile) : Profile :=
```

## SourceCurrentConstrainedCapRequiredForecast.lean:88 — plan_ge

```lean
theorem plan_ge (level : Nat) (profile : Profile) :
    Le profile (planProfile level profile) := by
```

## SourceCurrentConstrainedCapRequiredForecast.lean:106 — plan_mono

```lean
theorem plan_mono (level : Nat)
    {first last : Profile} (increase : Le first last) :
    Le (planProfile level first) (planProfile level last) := by
```

## InternedValueMassHeap.lean:17 — Stored

```lean
structure Stored (bound : Nat) (state : State Symbol Guard) : Prop where
```

## InternedValueMassHeap.lean:39 — initialBound

```lean
def initialBound (source : State Symbol Guard) : Nat :=
```

## InternedValueMassHeap.lean:54 — initial

```lean
theorem initial (source : State Symbol Guard) (facts : Facts source) : Stored (initialBound source) source := by
```

## InternedValueMassHeap.lean:74 — available

```lean
theorem available (source : State Symbol Guard) (stored : Stored bound source)
    (value : Value Symbol Guard) (known : Available source value) : InternedValueMass.value value ≤ bound := by
```

## InternedValueMassHeap.lean:82 — resident

```lean
theorem resident (source : State Symbol Guard) (stored : Stored bound source)
    (edge : EdgeValue Symbol Guard) (known : EdgeResident source edge) : InternedValueMass.edge edge ≤ bound :=
```

## SourceCurrentMemoMergeResourceControl.lean:25 — Fits

```lean
abbrev Fits (bound : Nat) (heap : State Symbol Guard) : Prop :=
```

## SourceCurrentMemoMergeResourceControl.lean:34 — initialBound

```lean
def initialBound (nodes edges mass : Nat) : Nat := max (max nodes edges) mass
```

## SourceCurrentMemoMergeResourceControl.lean:46 — primitiveGrowth

```lean
def primitiveGrowth (width bound : Nat) : Nat := max (bound + 1) (inflate width bound)
```

## SourceCurrentMemoMergeResourceControl.lean:92 — edge

```lean
theorem edge (symbol : Symbol) (guard : Guard) (values : List (Value Symbol Guard))
    (heap : State Symbol Guard) (bound width : Nat) (fits : Fits bound heap)
    (available : Values heap values) (length : values.length ≤ width) :
    Fits (primitiveGrowth width bound) (run (makeEdge symbol guard values) heap).2 ∧
      InternedValueMass.edge (run (makeEdge symbol guard values) heap).1 ≤ primitiveGrowth width bound ∧
      (run (makeEdge symbol guard values) heap).2.nodes.next = heap.nodes.next ∧
      (run (makeEdge symbol guard values) heap).2.edges.next ≤ heap.edges.next + 1 := by
```

## SourceCurrentMemoMergeResourceControl.lean:116 — node

```lean
theorem node (rows : List (EdgeValue Symbol Guard)) (heap : State Symbol Guard) (bound width : Nat)
    (fits : Fits bound heap) (resident : Edges heap rows) (length : rows.length ≤ width) :
    Fits (primitiveGrowth width bound) (run (makeNode rows) heap).2 ∧
      InternedValueMass.value (run (makeNode rows) heap).1 ≤ primitiveGrowth width bound ∧
      (run (makeNode rows) heap).2.nodes.next ≤ heap.nodes.next + 1 ∧
      (run (makeNode rows) heap).2.edges.next = heap.edges.next := by
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
