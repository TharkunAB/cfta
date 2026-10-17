# Exact reader and comparison header excerpts

These excerpts retain declaration headers and one-based source anchors. Proof bodies and recursive equations are omitted. The source hashes in the survey manifest pin the complete definitions and proofs.

`lean/MicroCFTA/MergedFreshOrdinaryColdTermination.lean:22`

```lean
def measure (limit : Nat) (state : State Symbol Guard) (seen : List Nat) (pending : List (Value Symbol Guard)) :
    Fin (limit + 1) → Nat
```

`lean/MicroCFTA/MergedFreshOrdinaryColdTermination.lean:31`

```lean
theorem ordinary_step (limit : Nat) (state : State Symbol Guard) (coherent : Coherent state)
    (seen laterSeen : List Nat) (pending laterPending : List (Value Symbol Guard))
    (visited : ∀ identity ∈ seen, identity ∈ laterSeen) (smaller : workWeight laterPending < workWeight pending) :
    HeightOrder.VectorBelow (limit + 1) (measure limit state laterSeen laterPending) (measure limit state seen pending)
```

`lean/MicroCFTA/MergedFreshOrdinaryColdTermination.lean:49`

```lean
theorem mu_step (limit : Nat) (before after : State Symbol Guard)
    (beforeCoherent : Coherent before) (afterCoherent : Coherent after) (bounded : Bounded before limit)
    (seen : List Nat) (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (present : before.nodeRecords entry.key = some (.mu entry body depth ordinary)) (unseen : entry.identity ∉ seen)
    (lower : InternedStoredPlanBinderDepthProgress.Lower before (InternedStoredPlanBinderDepth.valueDepth body) after)
    (pending laterPending : List (Value Symbol Guard)) :
    HeightOrder.VectorBelow (limit + 1) (measure limit after (entry.identity :: seen) laterPending)
      (measure limit before seen pending)
```

`lean/MicroCFTA/MergedFreshOrdinaryColdTermination.lean:71`

```lean
theorem collect_complete [DecidableEq (EdgeKey Symbol Guard)] (limit : Nat) (state : State Symbol Guard)
    (semantic : SemanticHeap state) (covered : Covered [] state) (heap : InternedOpenDepthReadback.Heap state)
    (bounded : Bounded state limit) (seen : List Nat) (pending : List (Value Symbol Guard))
    (inputs : Values state pending) (closed : ClosedValues pending) :
    ∃ fuel edges after, collect fuel state seen pending = .done edges after ∧
      InternedOpenDepthReadback.Heap after ∧ Bounded after limit
```

`lean/MicroCFTA/MergedFreshOrdinaryColdTermination.lean:160`

```lean
theorem nodeEdges_complete_bounded [DecidableEq (EdgeKey Symbol Guard)] (limit : Nat)
    (value : Value Symbol Guard) (state : State Symbol Guard) (semantic : SemanticHeap state)
    (covered : Covered [] state) (heap : InternedOpenDepthReadback.Heap state) (bounded : Bounded state limit)
    (available : Available state value) (closed : value.free = []) :
    ∃ fuel edges after, nodeEdges fuel value state = .done edges after ∧
      InternedOpenDepthReadback.Heap after ∧ Bounded after limit
```

`lean/MicroCFTA/MergedFreshOrdinaryColdTermination.lean:201`

```lean
theorem nodeEdges_complete [DecidableEq (EdgeKey Symbol Guard)] (value : Value Symbol Guard)
    (state : State Symbol Guard) (semantic : SemanticHeap state) (covered : Covered [] state)
    (heap : InternedOpenDepthReadback.Heap state) (available : Available state value) (closed : value.free = []) :
    ∃ fuel edges after, nodeEdges fuel value state = .done edges after ∧ InternedOpenDepthReadback.Heap after
```

`lean/MicroCFTA/MergedFreshOrdinaryColdTermination.lean:211`

```lean
theorem read_closed [DecidableEq (EdgeKey Symbol Guard)] (value : Value Symbol Guard)
    (state : State Symbol Guard) (semantic : SemanticHeap state) (covered : Covered [] state)
    (heap : InternedOpenDepthReadback.Heap state) (available : Available state value) (closed : value.free = []) :
    ∃ fuel edges after, nodeEdges fuel value state = .done edges after ∧
      SemanticHeap after ∧ Covered [] after ∧ InternedOpenDepthReadback.Heap after ∧
      Grows state after ∧ Extends state.nodes.issued after.nodes.issued ∧
      InternedNestedProvenance.Edges after edges ∧ MergedColdReaderClosedInputs.ClosedEdges edges ∧
      ∀ extra, nodeEdges (fuel + extra) value state = .done edges after
```

`lean/MicroCFTA/InternedMuDepthInventory.lean:20`

```lean
def rankAt (state : State Symbol Guard) (identity : Nat) : Option Nat
```

`lean/MicroCFTA/InternedMuDepthInventory.lean:68`

```lean
def Bounded (state : State Symbol Guard) (limit : Nat) : Prop
```

`lean/MicroCFTA/InternedMuDepthInventory.lean:72`

```lean
theorem initial_bounded (state : State Symbol Guard) (facts : InternedNestedFacts.Facts state) :
    Bounded state (maximumDepth (nodeInventory state) + 1)
```

`lean/MicroCFTA/InternedMuDepthInventory.lean:83`

```lean
theorem bounded_after (before after : State Symbol Guard) (limit rank : Nat)
    (bounded : Bounded before limit) (inside : rank < limit) (lower : Lower before rank after) : Bounded after limit
```

`lean/MicroCFTA/InternedMuDepthInventory.lean:91`

```lean
def unseenAt (state : State Symbol Guard) (seen : List Nat) (rank identity : Nat) : Bool
```

`lean/MicroCFTA/InternedMuDepthInventory.lean:95`

```lean
def count (state : State Symbol Guard) (seen : List Nat) (rank : Nat) : Nat
```

`lean/MicroCFTA/InternedMuDepthInventory.lean:182`

```lean
theorem count_after_le (before after : State Symbol Guard) (beforeCoherent : Coherent before)
    (afterCoherent : Coherent after) (seen : List Nat) (identity bound rank : Nat)
    (lower : Lower before bound after) (above : bound ≤ rank) :
    count after (identity :: seen) rank ≤ count before seen rank
```

`lean/MicroCFTA/InternedMuDepthInventory.lean:197`

```lean
theorem count_after_lt (before after : State Symbol Guard) (beforeCoherent : Coherent before)
    (afterCoherent : Coherent after) (seen : List Nat) (entry : Interned NodeKey)
    (body depth ordinary : Value Symbol Guard)
    (present : before.nodeRecords entry.key = some (.mu entry body depth ordinary))
    (unseen : entry.identity ∉ seen) (lower : Lower before (valueDepth body) after) :
    count after (entry.identity :: seen) (valueDepth body) < count before seen (valueDepth body)
```

`lean/MicroCFTA/MergedColdReaderTermination.lean:19`

```lean
def weight : Value Symbol Guard → Nat
```

`lean/MicroCFTA/MergedColdReaderTermination.lean:24`

```lean
def workWeight : List (Value Symbol Guard) → Nat
```

`lean/MicroCFTA/MergedColdReaderTermination.lean:40`

```lean
def Covered (state : State Symbol Guard) (seen remaining : List Nat) : Prop
```

`lean/MicroCFTA/MergedColdReaderTermination.lean:45`

```lean
theorem initially_covered (state : State Symbol Guard) (facts : Facts state) :
    Covered state [] (List.range state.nodes.next)
```

`lean/MicroCFTA/MergedColdReaderTermination.lean:72`

```lean
theorem collect_complete [DecidableEq (EdgeKey Symbol Guard)]
    (state : State Symbol Guard) (facts : Facts state) (prepared : Prepared state)
    (seen remaining : List Nat) (covered : Covered state seen remaining)
    (pending : List (Value Symbol Guard)) (inputs : Values state pending) :
    ∃ fuel, Finished (collect fuel state seen pending)
```

`lean/MicroCFTA/MergedColdReaderTermination.lean:129`

```lean
theorem nodeEdges_complete [DecidableEq (EdgeKey Symbol Guard)] (value : Value Symbol Guard)
    (state : State Symbol Guard) (facts : Facts state) (prepared : Prepared state)
    (available : Available state value) :
    ∃ fuel, Finished (MergedSourceExposure.nodeEdges fuel value state)
```

`lean/MicroCFTA/HeightOrder.lean:14`

```lean
def Below : Nat → (Nat → Nat) → (Nat → Nat) → Prop
```

`lean/MicroCFTA/HeightOrder.lean:19`

```lean
theorem below_wellFounded (bound : Nat) : WellFounded (Below bound)
```

`lean/MicroCFTA/HeightOrder.lean:71`

```lean
def VectorBelow (bound : Nat) (left right : Fin bound → Nat) : Prop
```

`lean/MicroCFTA/HeightOrder.lean:75`

```lean
theorem vector_wellFounded (bound : Nat) : WellFounded (VectorBelow bound)
```

`lean/MicroCFTA/InternedStoredPlanBinderDepth.lean:43`

```lean
def valueDepth (value : Value Symbol Guard) : Nat
```

`lean/MicroCFTA/InternedStoredPlanBinderDepth.lean:66`

```lean
def bodyDepth : Value Symbol Guard → Nat
```

`lean/MicroCFTA/InternedStoredPlanBinderDepth.lean:72`

```lean
theorem encode_depth (context : List (Value Symbol Guard)) (locals : List Reference) (value : Value Symbol Guard) :
    syntaxDepth (encode context locals value) = valueDepth value
```

`lean/MicroCFTA/InternedStoredPlanBinderDepth.lean:111`

```lean
theorem closed_zero (value : Value Symbol Guard) (closed : value.free = []) : valueDepth value = 0
```

`lean/MicroCFTA/InternedStoredPlanBinderDepthProgress.lean:21`

```lean
def Lower (initial : State Symbol Guard) (bound : Nat) (state : State Symbol Guard) : Prop
```

`lean/MicroCFTA/InternedStoredPlanBinderDepthProgress.lean:261`

```lean
theorem unfold_new_lower [DecidableEq (EdgeKey Symbol Guard)] (value : Value Symbol Guard) (state : State Symbol Guard)
    (context : Context state []) (cached : InternedFreshOrdinaryDepthHeap.Heap state)
    (heap : InternedOpenDepthReadback.Heap state) (available : Available state value) (closed : value.free = []) :
    Lower state (bodyDepth value) (InternedFreshOrdinaryStoredSubstitution.unfold value state).state
```

`lean/MicroCFTA/InternedStoredPlanBinderDepthProgress.lean:280`

```lean
theorem unfold_decreases [DecidableEq (EdgeKey Symbol Guard)] (value : Value Symbol Guard) (state : State Symbol Guard)
    (context : Context state []) (cached : InternedFreshOrdinaryDepthHeap.Heap state)
    (heap : InternedOpenDepthReadback.Heap state) (available : Available state value) (closed : value.free = [])
    (key : NodeKey) (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (new : state.nodeRecords key = none)
    (present : (InternedFreshOrdinaryStoredSubstitution.unfold value state).state.nodeRecords key =
      some (.mu entry body depth ordinary)) : bodyDepth (.mu entry body depth ordinary) < bodyDepth value
```

`lean/MicroCFTA/MergedFreshOrdinaryExposure.lean:18`

```lean
def collect [DecidableEq (EdgeKey Symbol Guard)] : Nat → State Symbol Guard →
    List Nat → List (Value Symbol Guard) → Result Symbol Guard
```

`lean/MicroCFTA/MergedFreshOrdinaryExposure.lean:37`

```lean
def nodeEdges [DecidableEq (EdgeKey Symbol Guard)] (fuel : Nat) (value : Value Symbol Guard)
    (state : State Symbol Guard) : Result Symbol Guard
```

`lean/MicroCFTA/MergedFreshOrdinaryExposure.lean:124`

```lean
def read [DecidableEq (EdgeKey Symbol Guard)] (fuel : Nat) (value : Value Symbol Guard)
    (state : State Symbol Guard) : MergedSourceComparison.Result Symbol Guard (List (EdgeValue Symbol Guard))
```

`lean/MicroCFTA/SourceCurrentAllocatedProjectionResources.lean:41`

```lean
theorem execute_bound [DecidableEq (EdgeKey Symbol Guard)] (value : Value Symbol Guard) (environment : Environment Symbol Guard)
    (before : State Symbol Guard) (bound : Nat) (stored : Stored bound before)
    (available : Available before value) (replacements : Replacements before environment) :
    Stored (ceiling bound) (InternedFreshOrdinaryStoredSubstitution.execute value environment before).state ∧
      (InternedFreshOrdinaryStoredSubstitution.execute value environment before).state.nodes.next ≤ before.nodes.next + charge bound ∧
      (InternedFreshOrdinaryStoredSubstitution.execute value environment before).state.edges.next ≤ before.edges.next + charge bound ∧
      ∀ result after, InternedFreshOrdinaryStoredSubstitution.execute value environment before = .done result after →
        InternedValueMass.value result ≤ ceiling bound
```

`lean/MicroCFTA/SourceCurrentAllocatedProjectionResources.lean:61`

```lean
theorem unfold_bound [DecidableEq (EdgeKey Symbol Guard)] (value : Value Symbol Guard) (before : State Symbol Guard) (bound : Nat)
    (stored : Stored bound before) (available : Available before value) :
    Stored (ceiling bound) (InternedFreshOrdinaryStoredSubstitution.unfold value before).state ∧
      (InternedFreshOrdinaryStoredSubstitution.unfold value before).state.nodes.next ≤ before.nodes.next + charge bound ∧
      (InternedFreshOrdinaryStoredSubstitution.unfold value before).state.edges.next ≤ before.edges.next + charge bound ∧
      ∀ result after, InternedFreshOrdinaryStoredSubstitution.unfold value before = .done result after →
        InternedValueMass.value result ≤ ceiling bound
```

`lean/MicroCFTA/SourceCurrentAllocatedProjectionResources.lean:96`

```lean
theorem collect_bound [DecidableEq (EdgeKey Symbol Guard)] (fuel : Nat) (before : State Symbol Guard)
    (semantic : SemanticHeap before) (covered : Covered [] before)
    (seen : List Nat) (pending : List (Value Symbol Guard))
    (inputs : Values before pending) (closed : ClosedValues pending)
    (bound : Nat) (stored : Stored bound before) (rows : List (EdgeValue Symbol Guard))
    (after : State Symbol Guard) (done : collect fuel before seen pending = .done rows after) :
    Stored (massAfter fuel bound) after ∧
      after.nodes.next ≤ before.nodes.next + credit fuel bound ∧
      after.edges.next ≤ before.edges.next + credit fuel bound ∧
      rows.length ≤ fuel * massAfter fuel bound
```

`lean/MicroCFTA/SourceCurrentAllocatedProjectionResources.lean:241`

```lean
theorem read_bound [DecidableEq (EdgeKey Symbol Guard)] (fuel : Nat)
    (value : Value Symbol Guard) (before : State Symbol Guard)
    (semantic : SemanticHeap before) (covered : Covered [] before)
    (available : Available before value) (closed : value.free = [])
    (bound : Nat) (stored : Stored bound before) (rows : List (EdgeValue Symbol Guard))
    (after : State Symbol Guard) (done : nodeEdges fuel value before = .done rows after) :
    Stored (massAfter (fuel + 1) bound) after ∧
      after.nodes.next ≤ before.nodes.next + credit (fuel + 1) bound ∧
      after.edges.next ≤ before.edges.next + credit (fuel + 1) bound ∧
      rows.length ≤ (fuel + 1) * massAfter (fuel + 1) bound ∧ Edges after rows
```

`lean/MicroCFTA/SourceCurrentAllocatedRecursiveMassTrace.lean:33`

```lean
def ceiling (bound : Nat) : Nat
```

`lean/MicroCFTA/SourceCurrentAllocatedRecursiveMassTrace.lean:42`

```lean
def charge (bound : Nat) : Nat
```

`lean/MicroCFTA/SourceCurrentAllocatedRecursiveMassTrace.lean:107`

```lean
def massAfter : Nat → Nat → Nat
```

`lean/MicroCFTA/SourceCurrentAllocatedRecursiveMassTrace.lean:112`

```lean
def credit : Nat → Nat → Nat
```

`lean/MicroCFTA/SourceCurrentAllocatedRecursiveMassTrace.lean:123`

```lean
theorem massAfter_add (first last bound : Nat) :
    massAfter (first + last) bound = massAfter last (massAfter first bound)
```

`lean/MicroCFTA/SourceCurrentAllocatedRecursiveMassTrace.lean:130`

```lean
theorem credit_add (first last bound : Nat) :
    credit (first + last) bound = credit first bound + credit last (massAfter first bound)
```

`lean/MicroCFTA/SourceCurrentAllocatedRecursiveMassMonotone.lean:35`

```lean
theorem ceiling_mono {first last : Nat} (enough : first ≤ last) : ceiling first ≤ ceiling last
```

`lean/MicroCFTA/SourceCurrentAllocatedRecursiveMassMonotone.lean:44`

```lean
theorem charge_mono {first last : Nat} (enough : first ≤ last) : charge first ≤ charge last
```

`lean/MicroCFTA/SourceCurrentAllocatedRecursiveMassMonotone.lean:63`

```lean
theorem massAfter_mono {firstCount lastCount firstBound lastBound : Nat}
    (counts : firstCount ≤ lastCount) (bounds : firstBound ≤ lastBound) :
    massAfter firstCount firstBound ≤ massAfter lastCount lastBound
```

`lean/MicroCFTA/SourceCurrentAllocatedRecursiveMassMonotone.lean:83`

```lean
theorem credit_mono {firstCount lastCount firstBound lastBound : Nat}
    (counts : firstCount ≤ lastCount) (bounds : firstBound ≤ lastBound) :
    credit firstCount firstBound ≤ credit lastCount lastBound
```

`lean/MicroCFTA/SourceMergedComparisonMass.lean:27`

```lean
structure Resources (bound : Nat) (before after : State Symbol Guard) : Prop
```

`lean/MicroCFTA/SourceMergedComparisonMass.lean:84`

```lean
def readBound (fuel bound : Nat) : Nat
```

`lean/MicroCFTA/SourceMergedComparisonMass.lean:87`

```lean
def readWidth (fuel bound : Nat) : Nat
```

`lean/MicroCFTA/SourceMergedComparisonMass.lean:126`

```lean
def comparisonBound : Nat → Nat → Nat
```

`lean/MicroCFTA/SourceMergedComparisonMass.lean:278`

```lean
theorem check_resources [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (clear : Guard → Bool) (fuel : Nat)
    (above : List (Nat × Nat)) (wide narrow : Value Symbol Guard) (origin before : State Symbol Guard)
    (bound : Nat) (known : Resources bound origin before) (semantic : SemanticReady before)
    (wideInput : Available before wide) (narrowInput : Available before narrow)
    (wideClosed : wide.free = []) (narrowClosed : narrow.free = [])
    (answer : Bool) (after : State Symbol Guard) (done : check clear fuel above wide narrow before = .done answer after) :
    Resources (comparisonBound fuel bound) origin after
```

`lean/MicroCFTA/SourceMergedComparisonMass.lean:318`

```lean
theorem check_bound [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (clear : Guard → Bool) (fuel : Nat) (above : List (Nat × Nat))
    (wide narrow : Value Symbol Guard) (before : State Symbol Guard) (bound : Nat)
    (semantic : SemanticReady before) (stored : Stored bound before)
    (wideInput : Available before wide) (narrowInput : Available before narrow)
    (wideClosed : wide.free = []) (narrowClosed : narrow.free = [])
    (answer : Bool) (after : State Symbol Guard) (done : check clear fuel above wide narrow before = .done answer after) :
    Resources (comparisonBound fuel bound) before after
```

`lean/MicroCFTA/SourceMergedSelectionMass.lean:24`

```lean
def selectionBound (fuel count bound : Nat) : Nat
```

`lean/MicroCFTA/SourceMergedSelectionMass.lean:111`

```lean
theorem select_bound (clear : Guard → Bool) (fuel : Nat) (inputs : List (Value Symbol Guard))
    (before : State Symbol Guard) (bound : Nat) (semantic : SemanticReady before) (stored : Stored bound before)
    (available : Values before inputs) (closed : ClosedValues inputs)
    (result : List (Value Symbol Guard)) (after : State Symbol Guard)
    (done : select clear fuel inputs before = .done result after) :
    Resources (selectionBound fuel inputs.length bound) before after
```

`lean/MicroCFTA/SourceMergedSelectionMass.lean:131`

```lean
theorem select_complete (clear : Guard → Bool) (inputs : List (Value Symbol Guard))
    (before : State Symbol Guard) (bound : Nat) (semantic : SemanticReady before) (stored : Stored bound before)
    (available : Values before inputs) (closed : ClosedValues inputs) :
    ∃ fuel result after, select clear fuel inputs before = .done result after ∧
      Resources (selectionBound fuel inputs.length bound) before after
```

`lean/MicroCFTA/SourceMergedComparisonCompletion.lean:27`

```lean
theorem check_eventually [DecidableEq Symbol] (limit : Nat) (clear : Guard → Bool)
    (state : State Symbol Guard) (semantic : SemanticReady state) (bounded : Bounded state limit)
    (above : List (Nat × Nat)) (wide narrow : Value Symbol Guard)
    (wideInput : Available state wide) (narrowInput : Available state narrow) (wideClosed : wide.free = []) (narrowClosed : narrow.free = []) :
    EventuallyDone (fun fuel => check clear fuel above wide narrow state)
```

`lean/MicroCFTA/SourceMergedComparisonCompletion.lean:93`

```lean
theorem check_complete [DecidableEq Symbol] (clear : Guard → Bool)
    (state : State Symbol Guard) (semantic : SemanticReady state) (above : List (Nat × Nat)) (wide narrow : Value Symbol Guard)
    (wideInput : Available state wide) (narrowInput : Available state narrow) (wideClosed : wide.free = []) (narrowClosed : narrow.free = []) :
    ∃ bound accepted after, (∀ fuel, bound ≤ fuel → check clear fuel above wide narrow state = .done accepted after) ∧ Effect state after
```

`lean/MicroCFTA/SourceMergedSelectionCompletion.lean:23`

```lean
theorem any_eventually (clear : Guard → Bool) (narrow : Value Symbol Guard) (wides : List (Value Symbol Guard))
    (before : State Symbol Guard) (semantic : SemanticReady before) (narrowInput : Available before narrow) (wideInputs : Values before wides)
    (narrowClosed : narrow.free = []) (wideClosed : ClosedValues wides) :
    EventuallyDone (fun fuel => anyAccepts clear fuel narrow wides before)
```

`lean/MicroCFTA/SourceMergedSelectionCompletion.lean:46`

```lean
theorem retain_eventually (clear : Guard → Bool) (recursive inputs : List (Value Symbol Guard))
    (before : State Symbol Guard) (semantic : SemanticReady before) (recInputs : Values before recursive) (recClosed : ClosedValues recursive)
    (available : Values before inputs) (closed : ClosedValues inputs) : EventuallyDone (fun fuel => retain clear fuel recursive inputs before)
```

`lean/MicroCFTA/SourceMergedSelectionCompletion.lean:73`

```lean
theorem select_eventually (clear : Guard → Bool) (inputs : List (Value Symbol Guard))
    (before : State Symbol Guard) (semantic : SemanticReady before) (available : Values before inputs) (closed : ClosedValues inputs) :
    EventuallyDone (fun fuel => select clear fuel inputs before)
```

`lean/MicroCFTA/InternedFreshMuUnfoldBudget.lean:18`

```lean
def Settled [DecidableEq (EdgeKey Symbol Guard)] (state : State Symbol Guard) (value : Value Symbol Guard) : Prop
```

`lean/MicroCFTA/InternedFreshMuUnfoldBudget.lean:44`

```lean
def count [DecidableEq (EdgeKey Symbol Guard)] (state : State Symbol Guard) (degree : Nat) : Nat
```

`lean/MicroCFTA/InternedFreshMuUnfoldBudget.lean:48`

```lean
def Progress [DecidableEq (EdgeKey Symbol Guard)] (limit : Nat) (before after : State Symbol Guard) : Prop
```

`lean/MicroCFTA/InternedFreshMuUnfoldBudget.lean:144`

```lean
theorem unfold_progress [DecidableEq (EdgeKey Symbol Guard)] (limit : Nat) (value : Value Symbol Guard)
    (before : State Symbol Guard) (semantic : SourceRecursiveIntersectionSemanticHeap.SemanticHeap before)
    (covered : Covered [] before) (heap : InternedOpenDepthReadback.Heap before) (bounded : Bounded before limit)
    (available : Available before value) (closed : value.free = []) (result : Value Symbol Guard) (after : State Symbol Guard)
    (done : InternedFreshOrdinaryStoredSubstitution.unfold value before = .done result after) :
    Progress limit before after
```

`lean/MicroCFTA/SourceEqualityProjectionPathDomain.lean:22`

```lean
def NodeClosed (path : List Int) (value : Value Symbol Guard) : Prop
```

`lean/MicroCFTA/SourceEqualityProjectionPathDomain.lean:36`

```lean
def ForestClosed (path : List Int) (values : List (Value Symbol Guard)) : Prop
```

`lean/MicroCFTA/SourceEqualityProjectionPathComplete.lean:50`

```lean
theorem node_complete [DecidableEq (EdgeKey Symbol Guard)] (path : List Int)
    (value : Value Symbol Guard) (before : State Symbol Guard) (semantic : SemanticReady before)
    (available : Available before value) (domain : NodeClosed path value) :
    ∃ result after, Project path value before result after ∧ Keeps before after ∧
      SemanticReady after ∧ Available after result ∧ result.free = []
```

`lean/MicroCFTA/SourceEqualityProjectionPathComplete.lean:84`

```lean
theorem forest_complete [DecidableEq (EdgeKey Symbol Guard)] (path : List Int)
    (values : List (Value Symbol Guard)) (before : State Symbol Guard) (semantic : SemanticReady before)
    (available : Values before values) (domain : ForestClosed path values) :
    ∃ result after, Forest path values before result after ∧ Keeps before after ∧
      SemanticReady after ∧ Available after result ∧ result.free = []
```

`lean/MicroCFTA/SourceCurrentMemoMergeMass.lean:22`

```lean
theorem entry_bound {heap : State Symbol Guard} {memo : Memo Symbol Guard}
    (physical : SourceCurrentMemoMergeEffects.Stored heap memo)
    (stored : InternedValueMassHeap.Stored bound heap)
    {key : InternedBinderProtocol.NodeRef} {entry : Entry Symbol Guard}
    (found : memo key = some entry) :
    InternedValueMass.value entry.original ≤ bound ∧ InternedValueMass.value entry.result ≤ bound
```

`lean/MicroCFTA/SourceCurrentMemoMergeMass.lean:33`

```lean
theorem hit_bound {heap : State Symbol Guard} {memo : Memo Symbol Guard}
    (physical : SourceCurrentMemoMergeEffects.Stored heap memo)
    (stored : InternedValueMassHeap.Stored bound heap)
    {input : Value Symbol Guard} {entry : Entry Symbol Guard}
    (found : memo input.referenceOf = some entry) :
    Available heap entry.result ∧ InternedValueMass.value entry.result ≤ bound
```

`lean/MicroCFTA/SourceCurrentMemoMergeMass.lean:42`

```lean
theorem winner_bound {heap : State Symbol Guard} {memo : Memo Symbol Guard}
    (physical : SourceCurrentMemoMergeEffects.Stored heap memo)
    (stored : InternedValueMassHeap.Stored bound heap)
    (input candidate : Value Symbol Guard) (available : Available heap candidate) :
    Available heap (winner memo input candidate).result ∧
      InternedValueMass.value (winner memo input candidate).result ≤ bound
```

`lean/MicroCFTA/SourceCurrentMemoMergeMass.lean:58`

```lean
theorem call_bound {clear : Guard → Bool} {top : Guard} {input output : Value Symbol Guard}
    {before after : State Symbol Guard} {memo saved : Memo Symbol Guard}
    (actual : Call clear top input before memo output after saved)
    (physical : SourceCurrentMemoMergeEffects.Stored after saved)
    (stored : InternedValueMassHeap.Stored bound after) :
    Available after output ∧ InternedValueMass.value output ≤ bound
```
