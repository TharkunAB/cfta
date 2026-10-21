# Existing public API excerpts

These are copied existing types. This file adds no declaration or proof.

## SourceCurrentEdgeCallNumeric.lean:60–84

```lean
structure Receipt (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (profile : Profile) (budget : Nat) (request : EdgeRequest) (before : Caller width)
    (memos : Memos) (result : Edge) (after : Caller width) (final : Memos) : Prop where
  /-- The actual first-writer graph retains its selected owner. -/
  actual : Graph.EdgeCall budget request before result after
  /-- Strict reads use the same actual graph and global bundle. -/
  reads : Graph.EdgeCallReads formulas solver actual memos final
  /-- The old complete receipt retains the candidate's inherited-conditioned law. -/
  semantic : SourceCurrentAllocatedPartialEdgeCall.Receipt formulas solver inventory request before result after final
  /-- The query Frame uses the same returned inventory. -/
  frame : Frame formulas solver inventory after.checked
  /-- The initial branch forecast bounds the actual returned state. -/
  fits : Fits (finalProfile budget request before profile) after.checked
  /-- The full caller postcondition retains all physical memo families. -/
  post : Post formulas solver inventory before after final
  /-- Outer fuel is arbitrary and every lower fuel can increase independently. -/
  run : ∀ f g s r e p h m c n,
    fuel budget request before profile ≤ g → fuel budget request before profile ≤ s →
    fuel budget request before profile ≤ r → fuel budget request before profile ≤ e →
    fuel budget request before profile ≤ p → fuel budget request before profile ≤ h →
    fuel budget request before profile ≤ m → fuel budget request before profile ≤ c →
    fuel budget request before profile ≤ n →
    SourceCurrentAllocatedPartialWorker.edgeCall f g s r e p h m c n budget request before = .done result after

```

## SourceCurrentEdgeCallNumeric.lean:175–220

```lean
theorem finite_or_busy
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (budget : Nat) (request : EdgeRequest) (before : Caller (bits + 2)) (memos : Memos)
    (initial : Context formulas solver inventory before memos)
    (frame : Frame formulas solver inventory before.checked) (profile : Profile) (fits : Fits profile before.checked)
    (inherited : EqReady before.checked.operations.constraints request.inherited)
    (resident : Resident before.checked.native.machine.heap request.value)
    (reserved : Reserved bits budget request before profile) :
    (∃ handle running, beginEdge request before = (handle, .busy, running) ∧
      ∀ f g s r e p h m c n, SourceCurrentAllocatedPartialWorker.edgeCall f g s r e p h m c n budget request before =
        .failed (.edgeMemo handle .busy) running) ∨
      ∃ result after next final, Receipt formulas solver next profile budget request before memos result after final := by
  generalize started : beginEdge request before = observed
  obtain ⟨handle, observation, running⟩ := observed
  cases observation with
  | ready result =>
      exact Or.inr ⟨result, running, inventory, memos,
        (ready formulas solver inventory budget request before memos initial frame profile fits inherited resident started).2⟩
  | evaluate original =>
      obtain ⟨result, after, next, final, receipt, _⟩ := evaluated formulas solver inventory budget request before memos
        initial frame profile fits inherited resident reserved started
      exact Or.inr ⟨result, after, next, final, receipt⟩
  | busy =>
      exact Or.inl ⟨handle, running, rfl,
        fun f g s r e p h m c n => SourceCurrentAllocatedPartialWorker.edgeCall_busy
          f g s r e p h m c n budget request before running handle started⟩
  | absent =>
      exact False.elim (not_absent request before initial.sound.valid inherited (by rw [started]))

/-- Excluding only the queried initial busy observation constructs the complete numeric call. -/
theorem complete
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (budget : Nat) (request : EdgeRequest) (before : Caller (bits + 2)) (memos : Memos)
    (initial : Context formulas solver inventory before memos)
    (frame : Frame formulas solver inventory before.checked) (profile : Profile) (fits : Fits profile before.checked)
    (inherited : EqReady before.checked.operations.constraints request.inherited)
    (resident : Resident before.checked.native.machine.heap request.value)
    (reserved : Reserved bits budget request before profile)
    (notBusy : (beginEdge request before).2.1 ≠ .busy) :
    ∃ result after next final, Receipt formulas solver next profile budget request before memos result after final := by
  rcases finite_or_busy formulas solver inventory budget request before memos initial frame profile fits
      inherited resident reserved with busy | completed
  · obtain ⟨handle, running, started, _⟩ := busy
    exact False.elim (notBusy (by rw [started]))
  · exact completed

```

## SourceCurrentOuterInitialActual.lean:432–449

```lean
theorem node_call (fuel : Nat) :
  ∀ {g s r e p h m c n budget : Nat} {request : NodeRequest} {before after : Caller (bits+2)} {result : Node}
    {inventory : Inventory} {memos : Memos} (seed : Seed),
    Context formulas solver inventory before memos → Frame formulas solver inventory before.checked →
    Fits seed.2 before.checked → Carrier (fun guard => guard ∈ seed.1) before.checked.native.machine.heap →
    EqReady before.checked.operations.constraints request.inherited → Available before.checked.native.machine.heap request.value →
    Room bits (Schedule.node fuel budget seed).2 →
    nodeCall fuel g s r e p h m c n budget request before = .done result after →
    ∃ next final, ∃ actual : NodeCall budget request before result after,
      NodeCallReads formulas solver actual memos final ∧
      Post formulas solver next before after final ∧
      Frame formulas solver next after.checked ∧ Fits (Schedule.node fuel budget seed).2 after.checked ∧
      Carrier (fun guard => guard ∈ (Schedule.node fuel budget seed).1) after.checked.native.machine.heap ∧
      Available after.checked.native.machine.heap result ∧ NodeLaw formulas solver request result := by
  intro g s r e p h m c n budget request before after result inventory memos seed initial frame fits known inherited available room done
  simpa only [Returned, and_assoc] using
    ((all_actual formulas solver (bits := bits) fuel).1 seed initial frame fits known inherited available room done)

```

## SourceCurrentOuterInitialActual.lean:489–506

```lean
theorem descendants (fuel : Nat) :
  ∀ {g s r e p h m c n budget : Nat} {inherited : EqValue} {value result : Edge} {before after : Caller (bits+2)}
    {inventory : Inventory} {memos : Memos} (seed : Seed),
    Context formulas solver inventory before memos → Frame formulas solver inventory before.checked →
    Fits seed.2 before.checked → Carrier (fun guard => guard ∈ seed.1) before.checked.native.machine.heap →
    EqReady before.checked.operations.constraints inherited → Resident before.checked.native.machine.heap value →
    Room bits (Schedule.descendants fuel budget seed).2 →
    SourceCurrentAllocatedPartialWorker.descendants fuel g s r e p h m c n budget inherited value before = .done result after →
    ∃ next final, ∃ actual : Descendants budget inherited value before result after,
      DescendantsReads formulas solver actual memos final ∧
      Post formulas solver next before after final ∧
      Frame formulas solver next after.checked ∧ Fits (Schedule.descendants fuel budget seed).2 after.checked ∧
      Carrier (fun guard => guard ∈ (Schedule.descendants fuel budget seed).1) after.checked.native.machine.heap ∧
      Resident after.checked.native.machine.heap result ∧ EdgeLaw formulas solver ⟨inherited,value⟩ result := by
  intro g s r e p h m c n budget inherited value result before after inventory memos seed initial frame fits known inheritedReady resident room done
  simpa only [Returned, and_assoc] using
    ((all_actual formulas solver (bits := bits) fuel).2.2.2.1 seed initial frame fits known inheritedReady resident room done)

```

## SourceCurrentConstrainedCapGeneratedQueryResources.lean:33–74

```lean
structure Fits (profile : Profile) (state : Checked width) : Prop where
  /-- The current node supply fits the forecast. -/
  nodes : state.native.machine.heap.nodes.next ≤ profile.nodes
  /-- The current edge supply fits the forecast. -/
  edges : state.native.machine.heap.edges.next ≤ profile.edges
  /-- The current domain supply fits the forecast. -/
  domains : state.native.machine.domains.next ≤ profile.domains
  /-- Every successful stored payload fits the causal mass bound. -/
  stored : Stored profile.mass state.native.machine.heap

/-- Initial numeric room bounds the actual query entry. -/
theorem Fits.room {profile : Profile} {state : Checked width} (fits : Fits profile state)
    (room : Room bits profile) :
    state.native.machine.heap.nodes.next < 2 ^ bits ∧
      state.native.machine.heap.edges.next ≤ 2 ^ (bits + 2) ∧
      state.native.machine.domains.next +
        2 ^ (state.native.machine.heap.nodes.next + state.native.machine.heap.nodes.next * state.native.machine.heap.nodes.next) <
        2 ^ (bits + 1) := by
  exact Room.mono room (show Le
    ⟨state.native.machine.heap.nodes.next, state.native.machine.heap.edges.next, state.native.machine.domains.next, profile.mass⟩
    profile from ⟨fits.nodes, fits.edges, fits.domains, Nat.le_refl _⟩)

/-- Larger numeric forecasts retain the same actual state. -/
theorem Fits.mono {first last : Profile} {state : Checked width} (fits : Fits first state) (larger : Le first last) :
    Fits last state :=
  ⟨Nat.le_trans fits.nodes larger.1, Nat.le_trans fits.edges larger.2.1,
    Nat.le_trans fits.domains larger.2.2.1, fits.stored.mono larger.2.2.2⟩

/-- One current inventory retains all laws needed by the next generated query. -/
structure Frame (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory) (state : Checked width) : Prop where
  /-- The same state retains all physical query invariants. -/
  ready : Ready state
  /-- Populated native cells retain current inventory admission. -/
  admitted : At formulas solver inventory state
  /-- The current heap retains its semantic and guard observations. -/
  context : Context Plain inventory.source state.native.machine
  /-- Completed native cells retain both joint laws. -/
  joint : SourceCurrentConstrainedCapCheckedJointCache.Stored Plain inventory.source state.native
  /-- Every allocated native cell retains its captured source witnesses. -/
  origins : SourceCurrentConstrainedCapCheckedJointOrigins.Stored inventory.source state.native

```

## SourceCurrentAllocatedPartialInvariant.lean:25–47

```lean
structure Context (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (state : Caller width) (memos : Memos) : Prop where
  ready : SourceCurrentConjunctionClassScan.Ready state.checked
  admitted : At formulas solver inventory state.checked
  sound : SourceCurrentAllocatedPartialMemoSound.Sound formulas solver state
  stored : SourceCurrentMemoMergeEffects.Stored state.checked.native.machine.heap state.merge
  covered : ∀ ambient, SourceCurrentMemoMergeLanguage.CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient state.merge
  correct : SourceCurrentEmptinessMemo.Correct formulas solver state.checked.native.machine.heap state.fourth
  globals : EndpointMemoGateTrace.Valid state.checked.native.machine.heap memos
  probes : InternedFreshOrdinaryProbeHeap.Heap state.checked.native.machine.heap

/-- A returned caller retains its actual current context and completed table history. -/
structure Post (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (next : Inventory)
    (before after : Caller width) (final : Memos) : Prop where
  context : Context formulas solver next after final
  effects : SourceCurrentConjunctionRowsAllocation.Effects (physical before.checked) (physical after.checked)
  retained : Cache.Extends before.merge after.merge
  fourthRetained : SourceCurrentEmptinessMemo.Extends before.fourth after.fourth

variable {formulas : SourceGuards.Formulas FullSyntax.Formula} {solver : SourceGuards.Entailment FullSyntax.Formula}
  {inventory next : Inventory} {before middle after : Caller width} {memos final : Memos}
```

## SourceCurrentConstrainedCapOperandFrame.lean:33–37

```lean
    {solver : SourceGuards.Entailment FullSyntax.Formula} {inventory : Inventory} {state : Checked width}
    (frame : Frame formulas solver inventory state) : SourceCurrentConstrainedCapCurrentNative.At Plain state :=
  SourceCurrentConstrainedCapCurrentNative.rebase Plain inventory.source state inventory.facts frame.ready.good
    frame.context frame.joint frame.origins

```

## SourceCurrentParentNumeric.lean:53–83

```lean
/-- One actual parent return retains strict reads, language, caller history, and numeric replay. -/
structure Receipt (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (profile : Profile) (budget : Nat) (symbol : Symbol) (original : Guard) (loaded : Allocated)
    (inherited : EqValue) (values : List (Value Symbol Guard)) (before : Caller width) (memos : Memos)
    (result : EdgeValue Symbol Guard) (after : Checked width) (savedFourth : Fourth) (saved : Memo) (final : Memos) : Prop where
  /-- The live field was loaded from the original initial operations. -/
  field : contradictory original = false →
    SourceEqualityConstraintFieldLookup.load original before.checked.operations.constraints = .ok (some loaded)
  /-- The source graph retains raw rejection or the exact local and constructor order. -/
  actual : Graph.Edge budget symbol original loaded inherited values before.checked before.fourth before.merge
    result after savedFourth saved
  /-- Global memo reads belong to that same actual graph. -/
  reads : Graph.Reads formulas solver actual memos final
  /-- The complete old receipt retains physical stores and guarded language. -/
  semantic : Graph.Receipt formulas solver inventory symbol original loaded inherited values before.checked result after
    before.fourth savedFourth before.merge saved final
  /-- The full Frame shares the caller Post inventory. -/
  frame : Frame formulas solver inventory after
  /-- The initial local schedule and original child count bound construction. -/
  fits : Fits (SourceCurrentParentForecast.finalProfile budget values.length original loaded inherited before.checked profile) after
  /-- Both outer tables and the complete caller retain their current laws. -/
  post : Post formulas solver inventory before (advance before after savedFourth saved) final
  /-- All nine independently larger fuels retain the same full parent return. -/
  run : ∀ g s r e p h m c n,
    fuel budget values.length original loaded inherited before.checked profile ≤ g →
    fuel budget values.length original loaded inherited before.checked profile ≤ s →
    fuel budget values.length original loaded inherited before.checked profile ≤ r →
    fuel budget values.length original loaded inherited before.checked profile ≤ e →
    fuel budget values.length original loaded inherited before.checked profile ≤ p →
    fuel budget values.length original loaded inherited before.checked profile ≤ h →
    fuel budget values.length original loaded inherited before.checked profile ≤ m →
```

## SourceCurrentNativeCurrentStores.lean:24–36

```lean
theorem step [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {left right result : Node} {before after : Checked width}
    (actual : SourceCurrentAllocatedTargetQuery.Step left right before result after)
    (good : SourceCurrentAllocatedNativePhysicalCompletion.Good before)
    (semantic : SourceEqualityRequiredSemanticCache.SemanticReady before.native.machine.heap)
    (current : SourceCurrentConstrainedCapCurrentNative.At Plain before)
    (supported : Support before.native.machine.heap before.native)
    (causal : SourceCurrentNativeMuPublication.History empty before.native.machine.heap)
    (leftAvailable : Available before.native.machine.heap left) (rightAvailable : Available before.native.machine.heap right)
    (leftClosed : left.free = []) (rightClosed : right.free = []) :
    SourceCurrentConstrainedCapCurrentNative.At Plain after ∧
      Support after.native.machine.heap after.native ∧
      Nonempty (SourceCurrentNativeMuPublication.History empty after.native.machine.heap) := by
```
