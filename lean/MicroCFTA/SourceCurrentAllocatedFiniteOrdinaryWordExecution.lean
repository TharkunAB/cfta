import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryWordCode
import MicroCFTA.SourceCurrentAllocatedNativeRequestBounds
import MicroCFTA.SourceCurrentAllocatedNativePhysicalCache

/-!
# Word checks through actual finite ordinary query prefixes

Memo cells retain their original operands in one fixed initial machine.
This invariant does not constrain returned values or their identities.
The proof follows actual yielded prefixes, including driver finish frames.
It does not assume a completed physical trace or a future word check.
-/
namespace MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryWordExecution
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceEqualityNativeDemand
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Native" => SourceRecursiveIntersectionThunks.State
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "WCode" => SourceCurrentAllocatedFiniteOrdinaryWordCode.Certified
local notation "NInputs" => SourceCurrentAllocatedFiniteOrdinaryWordCode.NodeInputs
local notation "EInputs" => SourceCurrentAllocatedFiniteOrdinaryWordCode.EdgeInputs
local notation "Words" => SourceCurrentAllocatedNativeRequestBounds.Words
local instance : DecidableEq (SourceGuards.Guard FullSyntax.Formula) :=
  SourceEqualityPCSNativeEdge.guardDecidableEq
variable {width : Nat}

/-- All cell phases retain the checked original request in a fixed machine. -/
structure Origins (source : Machine Symbol Guard) (state : Native width Symbol Guard) : Prop where
  nodes : FlatMemoThunk.Valid (NodeKey width) (fun cell => NodeReady source cell.request) state.nodes
  edges : FlatMemoThunk.Valid (EdgeKeyOf width) (fun cell => EdgeReady source cell.request) state.edges

/-- Initial physical validity supplies original operands without a returned-result law. -/
theorem Origins.of_valid (state : Native width Symbol Guard)
    (valid : SourceCurrentAllocatedNativePhysicalCache.Valid state) : Origins state.machine state :=
  ⟨FlatMemoThunk.Valid.map _ _ _ _ valid.nodes (fun _ good => good.1),
    FlatMemoThunk.Valid.map _ _ _ _ valid.edges (fun _ good => good.1)⟩

/-- Heap work does not change original requests or either native table. -/
theorem Origins.advance (source : Machine Symbol Guard) (state : Native width Symbol Guard)
    (origins : Origins source state) (machine : Machine Symbol Guard) : Origins source (advance state machine) :=
  ⟨origins.nodes, origins.edges⟩

/-- Publication adds only the actual bounded original node request. -/
theorem Origins.lookupNode (source : Machine Symbol Guard) (state : Native width Symbol Guard)
    (origins : Origins source state) (request : NodeRequest Symbol Guard) (ready : NodeReady source request)
    (safe : SourceRecursiveIntersectionMemo.KeySafe width request.domain request.left request.right) :
    Origins source (SourceRecursiveIntersectionThunks.lookupNode width request state).2 := by
  cases encoded : SourceRecursiveIntersectionMemo.requestKey width request.domain request.left request.right with
  | none => simpa only [SourceRecursiveIntersectionThunks.lookupNode, encoded] using origins
  | some key =>
      exact ⟨by simpa only [SourceRecursiveIntersectionThunks.lookupNode, encoded] using
        FlatMemoThunk.lookup_valid key request state.nodes _ _ origins.nodes ⟨encoded, safe⟩ ready,
        by simpa only [SourceRecursiveIntersectionThunks.lookupNode, encoded] using origins.edges⟩

/-- Edge publication retains the complete original ordered rows. -/
theorem Origins.lookupEdge (source : Machine Symbol Guard) (state : Native width Symbol Guard)
    (origins : Origins source state) (request : EdgeRequest Symbol Guard) (ready : EdgeReady source request)
    (safe : SourceRecursiveIntersectionEdgeMemo.KeySafe width request.domain request.left request.right) :
    Origins source (SourceRecursiveIntersectionThunks.lookupEdge width request state).2 :=
  ⟨origins.nodes, FlatMemoThunk.lookup_valid _ request state.edges _ _ origins.edges ⟨rfl, safe⟩ ready⟩

private theorem demand_origins (keyOf : Request → Key → Prop) (good : Request → Prop)
    (state : FlatMemoThunk.State Key Request OutputValue)
    (valid : FlatMemoThunk.Valid keyOf (fun cell => good cell.request) state) (handle : Nat) :
    FlatMemoThunk.Valid keyOf (fun cell => good cell.request) (FlatMemoThunk.demand handle state).2 := by
  cases stored : state.cells handle with
  | none => simpa only [FlatMemoThunk.demand, stored] using valid
  | some cell =>
      have checked := valid.checked handle cell stored
      cases cell with
      | mk request status =>
          cases status with
          | evaluating | returned value => simpa only [FlatMemoThunk.demand, stored] using valid
          | suspended =>
              simpa only [FlatMemoThunk.demand, stored] using
                FlatMemoThunk.setStatus_valid handle .evaluating state _ _ valid _ stored checked

/-- Starting or observing a node retains every original request. -/
theorem Origins.demandNode (source : Machine Symbol Guard) (state : Native width Symbol Guard)
    (origins : Origins source state) (handle : Nat) : Origins source (SourceRecursiveIntersectionThunks.demandNode handle state).2 :=
  ⟨demand_origins _ _ _ origins.nodes handle, origins.edges⟩

/-- Starting or observing an edge retains every original request. -/
theorem Origins.demandEdge (source : Machine Symbol Guard) (state : Native width Symbol Guard)
    (origins : Origins source state) (handle : Nat) : Origins source (SourceRecursiveIntersectionThunks.demandEdge handle state).2 :=
  ⟨origins.nodes, demand_origins _ _ _ origins.edges handle⟩

private theorem finish_origins (keyOf : Request → Key → Prop) (good : Request → Prop)
    (state : FlatMemoThunk.State Key Request OutputValue)
    (valid : FlatMemoThunk.Valid keyOf (fun cell => good cell.request) state) (handle : Nat) (value : OutputValue) :
    FlatMemoThunk.Valid keyOf (fun cell => good cell.request) (FlatMemoThunk.finish handle value state) := by
  cases stored : state.cells handle with
  | none => simpa only [FlatMemoThunk.finish, stored] using valid
  | some cell =>
      have checked := valid.checked handle cell stored
      cases cell with
      | mk request status =>
          cases status with
          | suspended | returned value => simpa only [FlatMemoThunk.finish, stored] using valid
          | evaluating =>
              simpa only [FlatMemoThunk.finish, stored] using
                FlatMemoThunk.setStatus_valid handle (.returned value) state _ _ valid _ stored checked

/-- A node finish changes only the actual evaluating phase and retains its owner. -/
theorem Origins.finishNode (source : Machine Symbol Guard) (state : Native width Symbol Guard)
    (origins : Origins source state) (handle : Nat) (value : Value Symbol Guard) :
    Origins source (SourceRecursiveIntersectionThunks.finishNode handle value state) :=
  ⟨finish_origins _ _ _ origins.nodes handle value, origins.edges⟩

/-- An edge finish retains the exact captured request independently of its result. -/
theorem Origins.finishEdge (source : Machine Symbol Guard) (state : Native width Symbol Guard)
    (origins : Origins source state) (handle : Nat) (value : EdgeValue Symbol Guard) :
    Origins source (SourceRecursiveIntersectionThunks.finishEdge handle value state) :=
  ⟨origins.nodes, finish_origins _ _ _ origins.edges handle value⟩

/-- Safe equal keys identify complete original node requests in the fixed initial machine. -/
theorem Origins.node_exact (source : Machine Symbol Guard) (sourceValid : SourceRecursiveIntersectionKernel.Valid source)
    (state : Native width Symbol Guard) (origins : Origins source state)
    (request : NodeRequest Symbol Guard) (ready : NodeReady source request)
    (key : IntersectionFlatMemoKeyDomain.Triple width) (checked : NodeKey width request key)
    (handle : Nat) (published : state.nodes.table key = some handle)
    (cell : FlatMemoThunk.Cell (NodeRequest Symbol Guard) (Value Symbol Guard))
    (stored : state.nodes.cells handle = some cell) : cell.request = request := by
  obtain ⟨original, present, originalKey⟩ := origins.nodes.linked key handle published
  have same : original = cell := Option.some.inj (present.symm.trans stored)
  subst original
  have good := origins.nodes.checked handle cell stored
  exact NodeRequest.components _ _ (SourceRecursiveIntersectionMemo.requestKey_injective width source sourceValid
    cell.request.domain request.domain cell.request.left cell.request.right request.left request.right good.1 ready.1
    originalKey.2 checked.2 good.2.1 good.2.2 ready.2.1 ready.2.2 (originalKey.1.trans checked.1.symm))

/-- Safe equal edge keys identify complete original row requests in the initial machine. -/
theorem Origins.edge_exact (source : Machine Symbol Guard) (sourceValid : SourceRecursiveIntersectionKernel.Valid source)
    (state : Native width Symbol Guard) (origins : Origins source state)
    (request : EdgeRequest Symbol Guard) (ready : EdgeReady source request)
    (key : IntersectionFlatMemoKeyDomain.Triple width) (checked : EdgeKeyOf width request key)
    (handle : Nat) (published : state.edges.table key = some handle)
    (cell : FlatMemoThunk.Cell (EdgeRequest Symbol Guard) (EdgeValue Symbol Guard))
    (stored : state.edges.cells handle = some cell) : cell.request = request := by
  obtain ⟨original, present, originalKey⟩ := origins.edges.linked key handle published
  have same : original = cell := Option.some.inj (present.symm.trans stored)
  subst original
  have good := origins.edges.checked handle cell stored
  exact EdgeRequest.components _ _ (SourceRecursiveIntersectionEdgeMemo.requestKey_injective width source sourceValid
    cell.request.domain request.domain cell.request.left cell.request.right request.left request.right good.1 ready.1
    originalKey.2 checked.2 good.2.1 good.2.2 ready.2.1 ready.2.2 (originalKey.1.trans checked.1.symm))

/-- Actual node starts recover the complete requested operands from the fixed source. -/
theorem Origins.node_started (source : Machine Symbol Guard) (valid : SourceRecursiveIntersectionKernel.Valid source)
    (request actual : NodeRequest Symbol Guard) (before chosen running : Native width Symbol Guard)
    (handle : Nat) (origins : Origins source before) (ready : NodeReady source request)
    (safe : SourceRecursiveIntersectionMemo.KeySafe width request.domain request.left request.right)
    (selected : SourceRecursiveIntersectionThunks.lookupNode width request before = (.memoized handle, chosen))
    (demanded : SourceRecursiveIntersectionThunks.demandNode handle chosen = (.evaluate actual, running)) : actual = request := by
  have chosenOrigins := origins.lookupNode source before request ready safe
  simp only [selected] at chosenOrigins
  obtain ⟨key, requested, published, _⟩ :=
    SourceRecursiveIntersectionNative.lookupNode_memoized request before chosen handle selected
  have suspended := (SourceRecursiveIntersectionNative.demandNode_evaluate handle chosen running actual demanded).1
  exact chosenOrigins.node_exact source valid chosen request ready key ⟨requested, safe⟩ handle published _ suspended

/-- Edge starts recover the exact original ordered rows before their checked body. -/
theorem Origins.edge_started (source : Machine Symbol Guard) (valid : SourceRecursiveIntersectionKernel.Valid source)
    (request actual : EdgeRequest Symbol Guard) (before chosen running : Native width Symbol Guard)
    (handle : Nat) (origins : Origins source before) (ready : EdgeReady source request)
    (safe : SourceRecursiveIntersectionEdgeMemo.KeySafe width request.domain request.left request.right)
    (selected : SourceRecursiveIntersectionThunks.lookupEdge width request before = (handle, chosen))
    (demanded : SourceRecursiveIntersectionThunks.demandEdge handle chosen = (.evaluate actual, running)) : actual = request := by
  have chosenOrigins := origins.lookupEdge source before request ready safe
  simp only [selected] at chosenOrigins
  obtain ⟨published, _⟩ :=
    SourceRecursiveIntersectionNative.lookupEdge_selected request before chosen handle selected
  have suspended := (SourceRecursiveIntersectionNative.demandEdge_evaluate handle chosen running actual demanded).1
  exact chosenOrigins.edge_exact source valid chosen request ready _ ⟨rfl, safe⟩ handle published _ suspended

/-- An expanded checked body retains its original request and all source continuations. -/
def Certified (bits : Nat) (source : Machine Symbol Guard) : Control A → Prop
  | .code code => WCode bits source code
  | .edgeBody request next => EInputs bits source request ∧ ∀ value, WCode bits source (next value)

private theorem node_ready (bits : Nat) (source : Machine Symbol Guard) (request : NodeRequest Symbol Guard)
    (inputs : NInputs bits source request) : NodeReady source request := by
  refine ⟨?_, inputs.2.2.2.1, inputs.2.2.2.2⟩
  rw [inputs.1]
  exact SourceRecursiveIntersectionKernel.empty_domain source

private theorem edge_ready (bits : Nat) (source : Machine Symbol Guard) (request : EdgeRequest Symbol Guard)
    (inputs : EInputs bits source request) : EdgeReady source request := by
  refine ⟨?_, inputs.2.2.2.1, inputs.2.2.2.2⟩
  rw [inputs.1]
  exact SourceRecursiveIntersectionKernel.empty_domain source

private theorem node_safe (bits : Nat) (source : Machine Symbol Guard) (request : NodeRequest Symbol Guard)
    (inputs : NInputs bits source request) :
    SourceRecursiveIntersectionMemo.KeySafe (bits + 2) request.domain request.left request.right := by
  rw [inputs.1]
  exact SourceCurrentAllocatedFiniteOrdinaryKeys.node_key_safe_empty inputs.2.1 inputs.2.2.1

private theorem edge_safe (bits : Nat) (source : Machine Symbol Guard) (request : EdgeRequest Symbol Guard)
    (inputs : EInputs bits source request) :
    SourceRecursiveIntersectionEdgeMemo.KeySafe (bits + 2) request.domain request.left request.right := by
  rw [inputs.1]
  exact SourceCurrentAllocatedFiniteOrdinaryKeys.edge_key_safe_empty inputs.2.1 inputs.2.2.1

/-- The current certificate derives the exact conditional node and unconditional edge word checks. -/
theorem Certified.words (bits : Nat) (source : Machine Symbol Guard) (control : Control A)
    (certificate : Certified bits source control) : Words (bits + 2) control := by
  cases control with
  | edgeBody => trivial
  | code code =>
      cases code with
      | node request next => exact fun _ _ => node_safe bits source request certificate.1
      | edge request next => exact edge_safe bits source request certificate.1
      | pure | fail | work | enter | read | optionalBinder | finishNode | finishEdge => trivial

private theorem body_code (request : EdgeRequest Symbol Guard) (next : EdgeValue Symbol Guard → Code Symbol Guard A)
    (before after : Checked width) (rest : Control A)
    (one : body request next before = .yielded rest after) : ∃ code, rest = .code code := by
  unfold SourceEqualityNativeDemand.body at one
  split at one
  · simp only [sentinel] at one
    cases one
    exact ⟨_, rfl⟩
  · split at one
    · cases one
    · cases one
    · split at one
      · cases one
      · cases one
      · dsimp only at one
        split at one
        · cases one
        · simp only [sentinel] at one
          cases one
          exact ⟨_, rfl⟩
        · simp only [sentinel] at one
          cases one
          exact ⟨_, rfl⟩
        · cases one
          exact ⟨_, rfl⟩

/-- One actual yielded step retains original owners and the next word certificate. -/
theorem step_preserves [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (bits : Nat) (source : Machine Symbol Guard) (valid : SourceRecursiveIntersectionKernel.Valid source)
    (control next : Control A) (before after : Checked (bits + 2))
    (origins : Origins source before.native) (certificate : Certified bits source control)
    (one : step control before = .yielded next after) :
    Origins source after.native ∧ Certified bits source next := by
  cases control with
  | edgeBody request resume =>
      have same := SourceEqualityNativeDemandOperations.body_native request resume before
      have bodyStep : SourceEqualityNativeDemand.body request resume before = .yielded next after := one
      rw [bodyStep] at same
      have native : after.native = before.native := same
      obtain ⟨code, rfl⟩ := body_code request resume before after next one
      exact ⟨native ▸ origins,
        SourceCurrentAllocatedFiniteOrdinaryWordCode.body_certified bits source valid request certificate.1
          resume before after code one certificate.2⟩
  | code code =>
      cases code with
      | pure | fail => simp only [step, SourceRecursiveIntersectionNative.step, lift] at one; cases one
      | enter | read | optionalBinder => cases certificate
      | work job resume =>
          simp only [step, SourceRecursiveIntersectionNative.step, lift] at one
          cases one
          exact ⟨origins.advance source before.native _, certificate _⟩
      | finishNode handle value rest =>
          simp only [step, SourceRecursiveIntersectionNative.step, lift] at one
          cases one
          exact ⟨origins.finishNode source before.native handle value, certificate⟩
      | finishEdge handle value rest =>
          simp only [step, SourceRecursiveIntersectionNative.step, lift] at one
          cases one
          exact ⟨origins.finishEdge source before.native handle value, certificate⟩
      | node request resume =>
          have ready := node_ready bits source request certificate.1
          have safe := node_safe bits source request certificate.1
          have chosenOrigins := origins.lookupNode source before.native request ready safe
          cases selected : SourceRecursiveIntersectionThunks.lookupNode (bits + 2) request before.native with
          | mk selection chosen =>
              simp only [selected] at chosenOrigins
              cases selection with
              | direct actual =>
                  obtain ⟨same, unchanged⟩ := SourceRecursiveIntersectionNative.lookupNode_direct request actual before.native chosen selected
                  subst actual
                  subst chosen
                  simp only [step, SourceRecursiveIntersectionNative.step, selected, lift] at one
                  cases one
                  exact ⟨origins, SourceCurrentAllocatedFiniteOrdinaryWordCode.certified_bind bits source _ _
                    (SourceCurrentAllocatedFiniteOrdinaryWordCode.node_certified bits source valid request certificate.1) certificate.2⟩
              | memoized handle =>
                  have runningOrigins := chosenOrigins.demandNode source chosen handle
                  cases demanded : SourceRecursiveIntersectionThunks.demandNode handle chosen with
                  | mk observation running =>
                      simp only [demanded] at runningOrigins
                      cases observation with
                      | absent | busy => simp only [step, SourceRecursiveIntersectionNative.step, selected, demanded, lift] at one; cases one
                      | ready value =>
                          simp only [step, SourceRecursiveIntersectionNative.step, selected, demanded, lift] at one
                          cases one
                          exact ⟨runningOrigins, certificate.2 value⟩
                      | evaluate actual =>
                          have same := origins.node_started source valid request actual before.native chosen running handle ready safe selected demanded
                          subst actual
                          simp only [step, SourceRecursiveIntersectionNative.step, selected, demanded, lift] at one
                          cases one
                          exact ⟨runningOrigins, SourceCurrentAllocatedFiniteOrdinaryWordCode.certified_bind bits source _ _
                            (SourceCurrentAllocatedFiniteOrdinaryWordCode.node_certified bits source valid request certificate.1)
                            (fun value => certificate.2 value)⟩
      | edge request resume =>
          have ready := edge_ready bits source request certificate.1
          have safe := edge_safe bits source request certificate.1
          have chosenOrigins := origins.lookupEdge source before.native request ready safe
          cases selected : SourceRecursiveIntersectionThunks.lookupEdge (bits + 2) request before.native with
          | mk handle chosen =>
              simp only [selected] at chosenOrigins
              have runningOrigins := chosenOrigins.demandEdge source chosen handle
              cases demanded : SourceRecursiveIntersectionThunks.demandEdge handle chosen with
              | mk observation running =>
                  simp only [demanded] at runningOrigins
                  cases observation with
                  | absent | busy => simp only [step, selected, demanded] at one; cases one
                  | ready value =>
                      simp only [step, selected, demanded] at one
                      cases one
                      exact ⟨runningOrigins, certificate.2 value⟩
                  | evaluate actual =>
                      have same := origins.edge_started source valid request actual before.native chosen running handle ready safe selected demanded
                      subst actual
                      simp only [step, selected, demanded] at one
                      cases one
                      exact ⟨runningOrigins, certificate.1, fun value => certificate.2 value⟩

/-- Every finite actual prefix retains the initial original requests and all current word checks. -/
theorem reached [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (bits : Nat) (source : Machine Symbol Guard) (valid : SourceRecursiveIntersectionKernel.Valid source)
    (fuel : Nat) (control next : Control A) (before after : Checked (bits + 2))
    (origins : Origins source before.native) (certificate : Certified bits source control)
    (trace : Steps fuel control before next after) :
    Origins source after.native ∧ Certified bits source next ∧ Words (bits + 2) next := by
  induction trace with
  | refl control before => exact ⟨origins, certificate, certificate.words bits source control⟩
  | cons control before middle current next after count one tail ih =>
      have current := step_preserves bits source valid control middle before current origins certificate one
      exact ih current.1 current.2

/-- Initial original operands suffice for every word check on the actual checked schedule. -/
theorem word_ranges [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (bits : Nat) (source : Machine Symbol Guard) (valid : SourceRecursiveIntersectionKernel.Valid source)
    (control : Control A) (before : Checked (bits + 2))
    (origins : Origins source before.native) (certificate : Certified bits source control) :
    SourceCurrentAllocatedNativeRequestBounds.WordRanges control before := by
  intro fuel next after trace
  exact (reached bits source valid fuel control next before after origins certificate trace).2.2

end MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryWordExecution
