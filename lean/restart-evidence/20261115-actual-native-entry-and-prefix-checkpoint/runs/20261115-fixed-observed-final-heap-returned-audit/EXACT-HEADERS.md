# Exact existing API headers

These declarations already exist. This audit adds no theorem.

## lean/MicroCFTA/SourceCurrentAllocatedNativeContextCache.lean:84

```lean
def Returned (law : Request → Answer → Prop) (state : FlatMemoThunk.State Key Request Answer) : Prop
```

## lean/MicroCFTA/SourceCurrentAllocatedNativeContextCache.lean:87

```lean
theorem returned_empty (law : Request → Answer → Prop) :
    Returned law (FlatMemoThunk.empty : FlatMemoThunk.State Key Request Answer)
```

## lean/MicroCFTA/SourceCurrentAllocatedNativeContextCache.lean:92

```lean
theorem returned_lookup [DecidableEq Key] (law : Request → Answer → Prop)
    (key : Key) (request : Request) (state : FlatMemoThunk.State Key Request Answer) (valid : Returned law state) :
    Returned law (FlatMemoThunk.lookupOrInsert key request state).2
```

## lean/MicroCFTA/SourceCurrentAllocatedNativeContextCache.lean:118

```lean
theorem returned_demand (law : Request → Answer → Prop) (handle : Nat)
    (state : FlatMemoThunk.State Key Request Answer) (valid : Returned law state) :
    Returned law (FlatMemoThunk.demand handle state).2
```

## lean/MicroCFTA/SourceCurrentAllocatedNativeContextCache.lean:130

```lean
theorem returned_finish (law : Request → Answer → Prop) (handle : Nat) (request : Request) (result : Answer)
    (state : FlatMemoThunk.State Key Request Answer) (valid : Returned law state)
    (running : state.cells handle = some ⟨request, .evaluating⟩) (localLaw : law request result) :
    Returned law (FlatMemoThunk.finish handle result state)
```

## lean/MicroCFTA/SourceCurrentAllocatedNativeReturnedProperties.lean:22

```lean
theorem node_ready_property
    (law : NodeRequest Symbol Guard → Value Symbol Guard → Prop)
    (state : Native width Symbol Guard)
    (physical : SourceCurrentAllocatedNativePhysicalCache.Valid state)
    (returned : Returned law state.nodes)
    (request original : NodeRequest Symbol Guard) (ready : NodeReady state.machine request)
    (key : IntersectionFlatMemoKeyDomain.Triple width) (checked : NodeKey width request key)
    (handle : Nat) (published : state.nodes.table key = some handle) (value : Value Symbol Guard)
    (stored : state.nodes.cells handle = some ⟨original, .returned value⟩) :
    original = request ∧ lookupNode width request state = (.memoized handle, state) ∧
      demandNode handle state = (.ready value, state) ∧ Available state.machine.heap value ∧
      law request value
```

## lean/MicroCFTA/SourceCurrentAllocatedNativeReturnedProperties.lean:62

```lean
theorem finishNode_property
    (law : NodeRequest Symbol Guard → Value Symbol Guard → Prop)
    (state : Native width Symbol Guard)
    (physical : SourceCurrentAllocatedNativePhysicalCache.Valid state)
    (returned : Returned law state.nodes)
    (handle : Nat) (request : NodeRequest Symbol Guard) (value : Value Symbol Guard)
    (running : state.nodes.cells handle = some ⟨request, .evaluating⟩)
    (available : Available state.machine.heap value) (localLaw : law request value) :
    SourceCurrentAllocatedNativePhysicalCache.Valid (finishNode handle value state) ∧
      Returned law (finishNode handle value state).nodes ∧
      (finishNode handle value state).nodes.cells handle = some ⟨request, .returned value⟩ ∧
      (finishNode handle value state).machine = state.machine ∧
      (finishNode handle value state).edges = state.edges
```

## lean/MicroCFTA/SourceCurrentAllocatedNativeSemanticTraceReadback.lean:137

```lean
theorem effects [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {fuel : Nat} {control rest : Control A} {before after : Checked width}
    (trace : Trace fuel control before rest after) (valid : Good before) (fields : Fields control before) :
    Good after ∧ Extension before.native.machine after.native.machine ∧
      SourceEqualityRequiredCache.Keeps before.native.machine.heap after.native.machine.heap ∧
      SourceEqualityConstraintMemoAllocation.Grows before.operations after.operations ∧ Fields rest after
```

## lean/MicroCFTA/SourceCurrentAllocatedNativePhysicalCompletion.lean:129

```lean
theorem step_invariants [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (control : Control Output) (state : CheckedState width) (valid : Good state)
    (inputs : SourceCurrentAllocatedNativePhysicalExecution.Inputs control state) (fields : Fields control state) :
    Good (step control state).state ∧
      Extension state.native.machine (step control state).state.native.machine ∧
      SourceEqualityRequiredCache.Keeps state.native.machine.heap (step control state).state.native.machine.heap ∧
      SourceEqualityConstraintMemoAllocation.Grows state.operations (step control state).state.operations ∧
      OutcomeFields (step control state)
```

## lean/MicroCFTA/SourceCurrentAllocatedNativePhysicalCompletion.lean:152

```lean
theorem execute_invariants [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (fuel : Nat) (control : Control Output) (state : CheckedState width) (valid : Good state)
    (inputs : SourceCurrentAllocatedNativePhysicalExecution.InputsThrough fuel control state) (fields : Fields control state) :
    Good (SourceEqualityNativeDemand.execute fuel control state).state ∧
      Extension state.native.machine (SourceEqualityNativeDemand.execute fuel control state).state.native.machine ∧
      SourceEqualityRequiredCache.Keeps state.native.machine.heap (SourceEqualityNativeDemand.execute fuel control state).state.native.machine.heap ∧
      SourceEqualityConstraintMemoAllocation.Grows state.operations (SourceEqualityNativeDemand.execute fuel control state).state.operations ∧
      OutcomeFields (SourceEqualityNativeDemand.execute fuel control state)
```

## lean/MicroCFTA/SourceCurrentNativeRequestSourceScope.lean:30

```lean
theorem node_prefix (bits : Nat) (before : Checked (bits + 2))
    (good : Good before) (semantic : SourceEqualityRequiredSemanticCache.SemanticReady before.native.machine.heap)
    (left right : Node) (leftAvailable : Available before.native.machine.heap left)
    (rightAvailable : Available before.native.machine.heap right)
    (leftClosed : left.free = []) (rightClosed : right.free = [])
    (nodes : before.native.machine.heap.nodes.next < 2 ^ bits)
    (edges : before.native.machine.heap.edges.next ≤ 2 ^ (bits + 2))
    (room : before.native.machine.domains.next +
      2 ^ (before.native.machine.heap.nodes.next + before.native.machine.heap.nodes.next * before.native.machine.heap.nodes.next) <
        2 ^ (bits + 1))
    {count : Nat} (queried : NodeRequest Symbol Guard) (next : Node → Code Symbol Guard Node)
    {after : Checked (bits + 2)}
    (actual : Steps count (.code (requestNode emptyDomain left right)) before
      (.code (.node queried next)) after) :
    NodeScope before.native.machine.heap queried ∧
      queried.domain.key ∈ SourceRecursiveIntersectionSourceInventory.domains before.native.machine.heap
```

## lean/MicroCFTA/SourceCurrentAllocatedNativePhysicalCache.lean:173

```lean
theorem node_request_exact
    (state : Native width Symbol Guard) (valid : Valid state)
    (request : NodeRequest Symbol Guard) (ready : NodeReady state.machine request)
    (key : IntersectionFlatMemoKeyDomain.Triple width) (checked : NodeKey width request key)
    (handle : Nat) (published : state.nodes.table key = some handle)
    (cell : FlatMemoThunk.Cell (NodeRequest Symbol Guard) (Value Symbol Guard))
    (stored : state.nodes.cells handle = some cell) : cell.request = request
```

## lean/MicroCFTA/SourceSynthesisUniverseMixedDescendantFreshness.lean:35

```lean
theorem closed_identity_injective (heap : State Symbol Guard) (facts : Facts heap)
    (left right : Value Symbol Guard) (leftAvailable : Available heap left)
    (rightAvailable : Available heap right) (leftClosed : left.free = []) (rightClosed : right.free = [])
    (name : Nat) (leftIdentity : identity left = some name) (rightIdentity : identity right = some name) :
    left = right
```

## lean/MicroCFTA/SourceSynthesisUniverseMixedEntryReplay.lean:22

```lean
theorem mixed_entry_replay_after_extension
    (before after : Machine Symbol Guard) (valid : Cache.Valid before.domains)
    (left right : Value Symbol Guard) (first second : Nat)
    (growth : Extension
      ⟨before.heap, (SourceRecursiveIntersectionEnvironment.enter before.domains
        IntersectionEmptyDomain.emptyKey left right first second).2⟩ after) :
    SourceRecursiveIntersectionEnvironment.enter after.domains IntersectionEmptyDomain.emptyKey
        left right first second =
      ((SourceRecursiveIntersectionEnvironment.enter before.domains IntersectionEmptyDomain.emptyKey
        left right first second).1, after.domains)
```
