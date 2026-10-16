import MicroCFTA.SourceCurrentAllocatedPartialState
import MicroCFTA.SourceEqualityPartialKeyTransport

/-!
# Warm result-cell laws for the current checked caller

Every phase retains its actual inherited value and resident input.
Only returned cells require a resident result and an immutable language
law. Publication and demand require no result law for a new request.
-/
namespace MicroCFTA.SourceCurrentAllocatedPartialMemoSound
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open SourceCurrentAllocatedPartialState
open SourceCurrentAllocatedNativeEffects (physical)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Edge" => EdgeValue Symbol Guard
local notation "Heap" => InternedConstructorTemplates.State Symbol Guard
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "EqCache" => Cache.State SourceEqualityPartialConstraintKey.Key
local notation "EqReady" => SourceEqualityConstraintAllocation.Ready
local notation "MergeMemo" => SourceCurrentMemoMergeGraph.Memo Symbol Guard
local notation "Fourth" => SourceCurrentEmptinessMemo.Memo
local notation "Resident" => InternedEdgeResidency.EdgeResident

/-- A node result narrows its input and retains each inherited-satisfying term. -/
def NodeLaw (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (request : NodeRequest) (result : Node) : Prop :=
  ∀ ambient term,
    (InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient result term →
      InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient request.value term) ∧
    (SourceEqualityPrecheck.Sat term request.inherited.payload →
      (InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient result term ↔
        InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient request.value term))

/-- A reduced-edge result has the same independent inherited-conditioned law. -/
def EdgeLaw (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (request : EdgeRequest) (result : Edge) : Prop :=
  ∀ ambient term,
    (InternedGuardedLanguage.edgeMeaning (SourceEqualityPCSGuard.holds formulas solver) ambient result term →
      InternedGuardedLanguage.edgeMeaning (SourceEqualityPCSGuard.holds formulas solver) ambient request.value term) ∧
    (SourceEqualityPrecheck.Sat term request.inherited.payload →
      (InternedGuardedLanguage.edgeMeaning (SourceEqualityPCSGuard.holds formulas solver) ambient result term ↔
        InternedGuardedLanguage.edgeMeaning (SourceEqualityPCSGuard.holds formulas solver) ambient request.value term))

/-- Every node phase retains its request; a returned phase also retains the proved result. -/
structure NodeGood (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (checked : Checked width) (cell : FlatMemoThunk.Cell NodeRequest Node) : Prop where
  inherited : EqReady checked.operations.constraints cell.request.inherited
  input : Available checked.native.machine.heap cell.request.value
  returned : ∀ result, cell.status = .returned result →
    Available checked.native.machine.heap result ∧ NodeLaw formulas solver cell.request result

/-- Every edge phase retains its request; a returned phase also retains the proved result. -/
structure EdgeGood (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (checked : Checked width) (cell : FlatMemoThunk.Cell EdgeRequest Edge) : Prop where
  inherited : EqReady checked.operations.constraints cell.request.inherited
  input : Resident checked.native.machine.heap cell.request.value
  returned : ∀ result, cell.status = .returned result →
    Resident checked.native.machine.heap result ∧ EdgeLaw formulas solver cell.request result

/-- Legitimate warm caller cells have exact key links and phase-appropriate source facts. -/
structure Sound (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (state : Caller width) : Prop where
  valid : SourceCurrentAllocatedPartialState.Valid state
  nodes : ∀ handle cell, state.nodeResults.cells handle = some cell → NodeGood formulas solver state.checked cell
  edges : ∀ handle cell, state.edgeResults.cells handle = some cell → EdgeGood formulas solver state.checked cell

variable (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)

/-- Equal current physical keys transport a proved node law to a later candidate. -/
theorem NodeLaw.of_key (cache : EqCache) (heap : Heap) (original candidate : NodeRequest)
    (result : Node) (valid : Cache.Valid cache) (coherent : InternedRecordCoherence.Coherent heap)
    (originalReady : EqReady cache original.inherited) (candidateReady : EqReady cache candidate.inherited)
    (originalAvailable : Available heap original.value) (candidateAvailable : Available heap candidate.value)
    (same : original.key = candidate.key) (law : NodeLaw formulas solver original result) :
    NodeLaw formulas solver candidate result := by
  have inherited : original.inherited.identity = candidate.inherited.identity := congrArg Prod.fst same
  have refs : original.value.referenceOf = candidate.value.referenceOf := congrArg Prod.snd same
  have values := SourceEqualityPartialKeyTransport.available_reference_eq heap coherent _ _
    originalAvailable candidateAvailable refs
  intro ambient term
  have satisfied := SourceEqualityPartialKeyTransport.sat_of_identity cache valid _ _ candidate.inherited.identity
    originalReady.2 candidateReady.2 (by simpa only [SourceEqualityConstraintAllocation.Stored, ← inherited] using originalReady.1) candidateReady.1 term
  simpa only [← values] using ⟨(law ambient term).1, fun accepted => (law ambient term).2 (satisfied.mpr accepted)⟩

/-- Equal current inherited and edge identities transport a proved edge law. -/
theorem EdgeLaw.of_key (cache : EqCache) (heap : Heap) (original candidate : EdgeRequest)
    (result : Edge) (valid : Cache.Valid cache) (coherent : InternedRecordCoherence.Coherent heap)
    (originalReady : EqReady cache original.inherited) (candidateReady : EqReady cache candidate.inherited)
    (originalResident : Resident heap original.value) (candidateResident : Resident heap candidate.value)
    (same : original.key = candidate.key) (law : EdgeLaw formulas solver original result) :
    EdgeLaw formulas solver candidate result := by
  have inherited : original.inherited.identity = candidate.inherited.identity := congrArg Prod.fst same
  have identities : original.value.entry.identity = candidate.value.entry.identity := congrArg Prod.snd same
  have values := InternedEdgeResidency.edge_identity_unique heap coherent _ _ originalResident candidateResident identities
  intro ambient term
  have satisfied := SourceEqualityPartialKeyTransport.sat_of_identity cache valid _ _ candidate.inherited.identity
    originalReady.2 candidateReady.2 (by simpa only [SourceEqualityConstraintAllocation.Stored, ← inherited] using originalReady.1) candidateReady.1 term
  simpa only [← values] using ⟨(law ambient term).1, fun accepted => (law ambient term).2 (satisfied.mpr accepted)⟩

/-- Empty result families need no supplied input or returned-result laws. -/
theorem initial_sound (checked : Checked width) (merge : MergeMemo) (fourth : Fourth) :
    Sound formulas solver (initial checked merge fourth) := by
  refine ⟨initial_valid checked merge fourth, ?_, ?_⟩ <;> intros <;> contradiction

/-- Actual physical effects retain a node cell's requests and immutable result law. -/
theorem NodeGood.grows {before after : Checked width} {cell : FlatMemoThunk.Cell NodeRequest Node}
    (good : NodeGood formulas solver before cell)
    (effects : SourceCurrentConjunctionRowsAllocation.Effects (physical before) (physical after)) :
    NodeGood formulas solver after cell :=
  ⟨good.inherited.grows effects.grows.constraint_growth, effects.keeps.available _ good.input,
    fun result returned => ⟨effects.keeps.available _ (good.returned result returned).1, (good.returned result returned).2⟩⟩

/-- Actual physical effects retain an edge cell's requests and immutable result law. -/
theorem EdgeGood.grows {before after : Checked width} {cell : FlatMemoThunk.Cell EdgeRequest Edge}
    (good : EdgeGood formulas solver before cell)
    (effects : SourceCurrentConjunctionRowsAllocation.Effects (physical before) (physical after)) :
    EdgeGood formulas solver after cell :=
  ⟨good.inherited.grows effects.grows.constraint_growth,
    InternedEdgeResidency.edge_grows _ _ effects.keeps.growth _ good.input,
    fun result returned => ⟨InternedEdgeResidency.edge_grows _ _ effects.keeps.growth _ (good.returned result returned).1,
      (good.returned result returned).2⟩⟩

/-- Current checked advancement retains every legitimate warm caller cell. -/
theorem Sound.advance {before : Caller width} (sound : Sound formulas solver before)
    (checked : Checked width) (fourth : Fourth) (merge : MergeMemo)
    (effects : SourceCurrentConjunctionRowsAllocation.Effects (physical before.checked) (physical checked)) :
    Sound formulas solver (advance before checked fourth merge) :=
  ⟨sound.valid.advance before checked fourth merge effects.grows.constraint_growth,
    fun handle cell stored => (sound.nodes handle cell stored).grows formulas solver effects,
    fun handle cell stored => (sound.edges handle cell stored).grows formulas solver effects⟩

private theorem node_valid {before : Caller width} (sound : Sound formulas solver before) :
    FlatMemoThunk.Valid (NodeLinked before.checked.operations.constraints) (NodeGood formulas solver before.checked) before.nodeResults :=
  ⟨sound.valid.nodes.bounded, sound.valid.nodes.linked, sound.nodes⟩

private theorem edge_valid {before : Caller width} (sound : Sound formulas solver before) :
    FlatMemoThunk.Valid (EdgeLinked before.checked.operations.constraints) (EdgeGood formulas solver before.checked) before.edgeResults :=
  ⟨sound.valid.edges.bounded, sound.valid.edges.linked, sound.edges⟩

private theorem node_demand (checked : Checked width) (handle : Nat)
    (memo : FlatMemoThunk.State NodeKey NodeRequest Node)
    (valid : FlatMemoThunk.Valid (NodeLinked checked.operations.constraints) (NodeGood formulas solver checked) memo) :
    FlatMemoThunk.Valid (NodeLinked checked.operations.constraints) (NodeGood formulas solver checked)
      (FlatMemoThunk.demand handle memo).2 := by
  cases found : memo.cells handle with
  | none => simpa only [FlatMemoThunk.demand, found] using valid
  | some cell =>
      cases phase : cell.status with
      | evaluating | returned value => simpa only [FlatMemoThunk.demand, found, phase] using valid
      | suspended =>
          have old := valid.checked handle cell found
          have next : NodeGood formulas solver checked { cell with status := .evaluating } :=
            ⟨old.inherited, old.input, fun result impossible => by cases impossible⟩
          simpa only [FlatMemoThunk.demand, found, phase] using
            FlatMemoThunk.setStatus_valid handle .evaluating memo _ _ valid cell found next

private theorem edge_demand (checked : Checked width) (handle : Nat)
    (memo : FlatMemoThunk.State EdgeKey EdgeRequest Edge)
    (valid : FlatMemoThunk.Valid (EdgeLinked checked.operations.constraints) (EdgeGood formulas solver checked) memo) :
    FlatMemoThunk.Valid (EdgeLinked checked.operations.constraints) (EdgeGood formulas solver checked)
      (FlatMemoThunk.demand handle memo).2 := by
  cases found : memo.cells handle with
  | none => simpa only [FlatMemoThunk.demand, found] using valid
  | some cell =>
      cases phase : cell.status with
      | evaluating | returned value => simpa only [FlatMemoThunk.demand, found, phase] using valid
      | suspended =>
          have old := valid.checked handle cell found
          have next : EdgeGood formulas solver checked { cell with status := .evaluating } :=
            ⟨old.inherited, old.input, fun result impossible => by cases impossible⟩
          simpa only [FlatMemoThunk.demand, found, phase] using
            FlatMemoThunk.setStatus_valid handle .evaluating memo _ _ valid cell found next

/-- Node publication and demand require only the candidate's actual inherited and input facts. -/
theorem beginNode_sound (request : NodeRequest) (before : Caller width) (sound : Sound formulas solver before)
    (inherited : EqReady before.checked.operations.constraints request.inherited)
    (available : Available before.checked.native.machine.heap request.value) :
    Sound formulas solver (beginNode request before).2.2 := by
  have fresh : NodeGood formulas solver before.checked ⟨request, .suspended⟩ :=
    ⟨inherited, available, fun result impossible => by cases impossible⟩
  have published := FlatMemoThunk.lookup_valid request.key request before.nodeResults _ _ (node_valid formulas solver sound)
    ⟨inherited.1, rfl⟩ fresh
  have demanded := node_demand formulas solver before.checked
    (FlatMemoThunk.lookupOrInsert request.key request before.nodeResults).1 _ published
  exact ⟨beginNode_valid request before sound.valid inherited.1, demanded.checked, sound.edges⟩

/-- Edge publication and demand require only the candidate's actual inherited and input facts. -/
theorem beginEdge_sound (request : EdgeRequest) (before : Caller width) (sound : Sound formulas solver before)
    (inherited : EqReady before.checked.operations.constraints request.inherited)
    (resident : Resident before.checked.native.machine.heap request.value) :
    Sound formulas solver (beginEdge request before).2.2 := by
  have fresh : EdgeGood formulas solver before.checked ⟨request, .suspended⟩ :=
    ⟨inherited, resident, fun result impossible => by cases impossible⟩
  have published := FlatMemoThunk.lookup_valid request.key request before.edgeResults _ _ (edge_valid formulas solver sound)
    ⟨inherited.1, rfl⟩ fresh
  have demanded := edge_demand formulas solver before.checked
    (FlatMemoThunk.lookupOrInsert request.key request before.edgeResults).1 _ published
  exact ⟨beginEdge_valid request before sound.valid inherited.1, sound.nodes, demanded.checked⟩

private theorem demand_table (handle : Nat) (memo : FlatMemoThunk.State Key Request Result) :
    (FlatMemoThunk.demand handle memo).2.table = memo.table := by
  cases found : memo.cells handle with
  | none => simp only [FlatMemoThunk.demand, found]
  | some cell => cases phase : cell.status <;> simp [FlatMemoThunk.demand, found, phase, FlatMemoThunk.setStatus]

private theorem lookup_demand_ready [DecidableEq Key] (key : Key) (request : Request)
    (memo : FlatMemoThunk.State Key Request Result) (result : Result)
    (ready : (FlatMemoThunk.demand (FlatMemoThunk.lookupOrInsert key request memo).1
      (FlatMemoThunk.lookupOrInsert key request memo).2).1 = .ready result) :
    ∃ original, memo.table key = some (FlatMemoThunk.lookupOrInsert key request memo).1 ∧
      memo.cells (FlatMemoThunk.lookupOrInsert key request memo).1 = some ⟨original, .returned result⟩ := by
  cases found : memo.table key with
  | none => simp [FlatMemoThunk.lookupOrInsert, found, FlatMemoThunk.demand, put] at ready
  | some handle =>
      have observed : (FlatMemoThunk.demand handle memo).1 = .ready result := by
        simpa only [FlatMemoThunk.lookupOrInsert, found] using ready
      obtain ⟨original, returned, _⟩ := FlatMemoThunk.demand_ready_original handle memo result
        (FlatMemoThunk.demand handle memo).2 (Prod.ext observed rfl)
      exact ⟨original, by simp only [FlatMemoThunk.lookupOrInsert, found],
        by simpa only [FlatMemoThunk.lookupOrInsert, found] using returned⟩

/-- A missing node key publishes this request and starts its exact fresh cell. -/
theorem beginNode_fresh (request : NodeRequest) (before : Caller width)
    (missing : before.nodeResults.table request.key = none) :
    beginNode request before = (before.nodeResults.next, .evaluate request,
      { before with nodeResults := (FlatMemoThunk.setStatus before.nodeResults.next .evaluating
          (FlatMemoThunk.lookupOrInsert request.key request before.nodeResults).2) }) ∧
      (beginNode request before).2.2.nodeResults.cells before.nodeResults.next = some ⟨request, .evaluating⟩ := by
  simp [beginNode, FlatMemoThunk.lookupOrInsert, missing, FlatMemoThunk.demand, FlatMemoThunk.setStatus, put]

/-- A missing edge key publishes this request before its exact fresh evaluation. -/
theorem beginEdge_fresh (request : EdgeRequest) (before : Caller width)
    (missing : before.edgeResults.table request.key = none) :
    beginEdge request before = (before.edgeResults.next, .evaluate request,
      { before with edgeResults := (FlatMemoThunk.setStatus before.edgeResults.next .evaluating
          (FlatMemoThunk.lookupOrInsert request.key request before.edgeResults).2) }) ∧
      (beginEdge request before).2.2.edgeResults.cells before.edgeResults.next = some ⟨request, .evaluating⟩ := by
  simp [beginEdge, FlatMemoThunk.lookupOrInsert, missing, FlatMemoThunk.demand, FlatMemoThunk.setStatus, put]

/-- An actual node start exposes its original running owner and matching physical key. -/
theorem beginNode_evaluate_sound (request : NodeRequest) (before : Caller width)
    (sound : Sound formulas solver before)
    (inherited : EqReady before.checked.operations.constraints request.inherited)
    (available : Available before.checked.native.machine.heap request.value)
    (handle : Nat) (original : NodeRequest) (running : Caller width)
    (started : beginNode request before = (handle, .evaluate original, running)) :
    Sound formulas solver running ∧ running.nodeResults.cells handle = some ⟨original, .evaluating⟩ ∧
      NodeGood formulas solver running.checked ⟨original, .evaluating⟩ ∧ original.key = request.key := by
  have next := beginNode_sound formulas solver request before sound inherited available
  rw [started] at next
  have observed := congrArg (fun result => result.2.1) started
  have evaluated := FlatMemoThunk.demand_evaluate
    (FlatMemoThunk.lookupOrInsert request.key request before.nodeResults).1
    (FlatMemoThunk.lookupOrInsert request.key request before.nodeResults).2
    (FlatMemoThunk.demand (FlatMemoThunk.lookupOrInsert request.key request before.nodeResults).1
      (FlatMemoThunk.lookupOrInsert request.key request before.nodeResults).2).2 original (Prod.ext observed rfl)
  have present : (beginNode request before).2.2.nodeResults.cells (beginNode request before).1 =
      some ⟨original, .evaluating⟩ := evaluated.2
  have published : (beginNode request before).2.2.nodeResults.table request.key = some (beginNode request before).1 := by
    change (FlatMemoThunk.demand _ _).2.table _ = _
    rw [demand_table]
    exact FlatMemoThunk.lookup_stored _ _ _
  rw [started] at present published
  obtain ⟨cell, stored, linked⟩ := next.valid.nodes.linked request.key handle published
  have cells := Option.some.inj (stored.symm.trans present)
  subst cell
  exact ⟨next, present, next.nodes handle _ present, linked.2⟩

/-- An actual edge start exposes its original running owner without a result-law premise. -/
theorem beginEdge_evaluate_sound (request : EdgeRequest) (before : Caller width)
    (sound : Sound formulas solver before)
    (inherited : EqReady before.checked.operations.constraints request.inherited)
    (resident : Resident before.checked.native.machine.heap request.value)
    (handle : Nat) (original : EdgeRequest) (running : Caller width)
    (started : beginEdge request before = (handle, .evaluate original, running)) :
    Sound formulas solver running ∧ running.edgeResults.cells handle = some ⟨original, .evaluating⟩ ∧
      EdgeGood formulas solver running.checked ⟨original, .evaluating⟩ ∧ original.key = request.key := by
  have next := beginEdge_sound formulas solver request before sound inherited resident
  rw [started] at next
  have observed := congrArg (fun result => result.2.1) started
  have evaluated := FlatMemoThunk.demand_evaluate
    (FlatMemoThunk.lookupOrInsert request.key request before.edgeResults).1
    (FlatMemoThunk.lookupOrInsert request.key request before.edgeResults).2
    (FlatMemoThunk.demand (FlatMemoThunk.lookupOrInsert request.key request before.edgeResults).1
      (FlatMemoThunk.lookupOrInsert request.key request before.edgeResults).2).2 original (Prod.ext observed rfl)
  have present : (beginEdge request before).2.2.edgeResults.cells (beginEdge request before).1 =
      some ⟨original, .evaluating⟩ := evaluated.2
  have published : (beginEdge request before).2.2.edgeResults.table request.key = some (beginEdge request before).1 := by
    change (FlatMemoThunk.demand _ _).2.table _ = _
    rw [demand_table]
    exact FlatMemoThunk.lookup_stored _ _ _
  rw [started] at present published
  obtain ⟨cell, stored, linked⟩ := next.valid.edges.linked request.key handle published
  have cells := Option.some.inj (stored.symm.trans present)
  subst cell
  exact ⟨next, present, next.edges handle _ present, linked.2⟩

/-- An actual node hit retains the entire state and reuses only a proved owner law. -/
theorem beginNode_ready_sound (request : NodeRequest) (before : Caller width)
    (sound : Sound formulas solver before)
    (valid : Cache.Valid before.checked.operations.constraints)
    (coherent : InternedRecordCoherence.Coherent before.checked.native.machine.heap)
    (inherited : EqReady before.checked.operations.constraints request.inherited)
    (available : Available before.checked.native.machine.heap request.value)
    (handle : Nat) (result : Node) (after : Caller width)
    (ready : beginNode request before = (handle, .ready result, after)) :
    after = before ∧ Available before.checked.native.machine.heap result ∧ NodeLaw formulas solver request result := by
  obtain ⟨original, published, returned⟩ := lookup_demand_ready request.key request before.nodeResults result
    (congrArg (fun result => result.2.1) ready)
  have handles : (FlatMemoThunk.lookupOrInsert request.key request before.nodeResults).1 = handle := congrArg Prod.fst ready
  rw [handles] at published returned
  have unchanged := congrArg (fun result => result.2.2)
    (ready.symm.trans (beginNode_ready request original before handle result published returned))
  have good := sound.nodes handle _ returned
  obtain ⟨cell, stored, linked⟩ := sound.valid.nodes.linked request.key handle published
  have cells := Option.some.inj (stored.symm.trans returned)
  subst cell
  exact ⟨unchanged, (good.returned result rfl).1,
    NodeLaw.of_key formulas solver _ _ original request result valid coherent good.inherited inherited good.input available
      linked.2 (good.returned result rfl).2⟩

/-- An actual edge hit retains the entire state and transports the owner's law through its key. -/
theorem beginEdge_ready_sound (request : EdgeRequest) (before : Caller width)
    (sound : Sound formulas solver before)
    (valid : Cache.Valid before.checked.operations.constraints)
    (coherent : InternedRecordCoherence.Coherent before.checked.native.machine.heap)
    (inherited : EqReady before.checked.operations.constraints request.inherited)
    (resident : Resident before.checked.native.machine.heap request.value)
    (handle : Nat) (result : Edge) (after : Caller width)
    (ready : beginEdge request before = (handle, .ready result, after)) :
    after = before ∧ Resident before.checked.native.machine.heap result ∧ EdgeLaw formulas solver request result := by
  obtain ⟨original, published, returned⟩ := lookup_demand_ready request.key request before.edgeResults result
    (congrArg (fun result => result.2.1) ready)
  have handles : (FlatMemoThunk.lookupOrInsert request.key request before.edgeResults).1 = handle := congrArg Prod.fst ready
  rw [handles] at published returned
  have unchanged := congrArg (fun result => result.2.2)
    (ready.symm.trans (beginEdge_ready request original before handle result published returned))
  have good := sound.edges handle _ returned
  obtain ⟨cell, stored, linked⟩ := sound.valid.edges.linked request.key handle published
  have cells := Option.some.inj (stored.symm.trans returned)
  subst cell
  exact ⟨unchanged, (good.returned result rfl).1,
    EdgeLaw.of_key formulas solver _ _ original request result valid coherent good.inherited inherited good.input resident
      linked.2 (good.returned result rfl).2⟩

/-- An actual proved node body can complete only its exact retained running request. -/
theorem finishNode_sound (handle : Nat) (original : NodeRequest) (result : Node) (before : Caller width)
    (sound : Sound formulas solver before)
    (running : before.nodeResults.cells handle = some ⟨original, .evaluating⟩)
    (available : Available before.checked.native.machine.heap result) (law : NodeLaw formulas solver original result) :
    Sound formulas solver (finishNode handle result before) := by
  have originalGood := sound.nodes handle _ running
  have next : NodeGood formulas solver before.checked ⟨original, .returned result⟩ := by
    refine ⟨originalGood.inherited, originalGood.input, ?_⟩
    intro value same
    cases same
    exact ⟨available, law⟩
  have changed := FlatMemoThunk.setStatus_valid handle (.returned result) before.nodeResults _ _
    (node_valid formulas solver sound) _ running next
  refine ⟨finishNode_valid handle result before sound.valid, ?_, sound.edges⟩
  simpa only [finishNode, FlatMemoThunk.finish, running] using changed.checked

/-- An actual proved edge body can complete only its exact retained running request. -/
theorem finishEdge_sound (handle : Nat) (original : EdgeRequest) (result : Edge) (before : Caller width)
    (sound : Sound formulas solver before)
    (running : before.edgeResults.cells handle = some ⟨original, .evaluating⟩)
    (resident : Resident before.checked.native.machine.heap result) (law : EdgeLaw formulas solver original result) :
    Sound formulas solver (finishEdge handle result before) := by
  have originalGood := sound.edges handle _ running
  have next : EdgeGood formulas solver before.checked ⟨original, .returned result⟩ := by
    refine ⟨originalGood.inherited, originalGood.input, ?_⟩
    intro value same
    cases same
    exact ⟨resident, law⟩
  have changed := FlatMemoThunk.setStatus_valid handle (.returned result) before.edgeResults _ _
    (edge_valid formulas solver sound) _ running next
  refine ⟨finishEdge_valid handle result before sound.valid, sound.nodes, ?_⟩
  simpa only [finishEdge, FlatMemoThunk.finish, running] using changed.checked

end MicroCFTA.SourceCurrentAllocatedPartialMemoSound
