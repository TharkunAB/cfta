import MicroCFTA.SourceCurrentConstrainedCapNativeCache
import MicroCFTA.SourceCurrentConstrainedCapNativeCode
import MicroCFTA.SourceCurrentHereditaryNativeEffects
import MicroCFTA.SourceCurrentAllocatedRecursivePrefixReceipt

/-!
# Actual body returns and conditional cap publication

The existing physical receipt retains the exact trace and checked state.
An internal smaller-body return also carries its causal stores and local law.
The captured finish installs that law at its actual evaluating owner.
This module does not derive the missing mixed optional-binder cap producer.
-/
namespace MicroCFTA.SourceCurrentConstrainedCapNativeTraceGlue
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceEqualityNativeDemand
open SourceCurrentHereditaryConstruction (MuStored)
open SourceCurrentConstrainedCapNativeLaws (NodeLaw EdgeLaw)
open SourceCurrentAllocatedRecursivePrefixState (Current)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "DomainKey" => IntersectionFlatMemoKeyDomain.DomainKey
local notation "PhysicalReceipt" => SourceCurrentAllocatedRecursivePrefixReceipt.Receipt
variable {width : Nat}

/-- Returned cells retain their conditional cap laws for each possible later source heap. -/
structure Stored (annotation : Guard → Prop) (state : Checked width) : Prop where
  /-- Actual Mu records retain the local conditional constructor law. -/
  constructors : MuStored annotation state.native.machine.heap
  /-- Each returned native cell retains its law for every later source heap. -/
  native : ∀ source, SourceCurrentConstrainedCapNativeCache.Stored annotation source state.native

/-- Empty native tables derive the universal cell invariant from the actual constructor store. -/
theorem initial_stored (annotation : Guard → Prop) (width : Nat) (machine : Machine Symbol Guard)
    (operations : SourceEqualityConstraintMemoAllocation.State) (constructors : MuStored annotation machine.heap) :
    Stored annotation ⟨initial width machine, operations⟩ :=
  ⟨constructors, fun source => SourceCurrentConstrainedCapNativeCache.initial_stored annotation source width machine⟩

/-- Literal Work retains causal stores when its primitive constructor effect preserves Mu records. -/
theorem work_stored [DecidableEq (EdgeKey Symbol Guard)] (annotation : Guard → Prop)
    (job : Work Symbol Guard A) (before : Checked width)
    (safe : SourceCurrentHereditaryNativeEffects.WorkSafe annotation job) (stored : Stored annotation before) :
    Stored annotation {before with native := advance before.native
      ({before.native.machine with heap := (run job before.native.machine.heap).2})} :=
  ⟨safe before.native.machine.heap stored.constructors,
    fun source => SourceCurrentConstrainedCapNativeCache.advance_stored annotation source before.native _ (stored.native source)⟩

/-- Actual domain allocation retains the unchanged heap and every returned cell law. -/
theorem enter_stored (annotation : Guard → Prop) (before : Checked width)
    (domain : Interned DomainKey) (left right : Value Symbol Guard) (first second : Nat)
    (stored : Stored annotation before) :
    Stored annotation {before with native := advance before.native {before.native.machine with domains :=
      (SourceRecursiveIntersectionEnvironment.enter before.native.machine.domains domain.key left right first second).2}} :=
  ⟨stored.constructors,
    fun source => SourceCurrentConstrainedCapNativeCache.advance_stored annotation source before.native _ (stored.native source)⟩

/-- A checked edge-body prefix changes operations and retains the same native causal stores. -/
theorem body_stored (annotation : Guard → Prop) (request : EdgeRequest Symbol Guard)
    (next : EdgeValue Symbol Guard → Code Symbol Guard A) (before after : Checked width)
    (control : Control A) (stored : Stored annotation before)
    (yielded : body request next before = .yielded control after) : Stored annotation after := by
  classical
  have same : after.native = before.native := by
    simpa only [yielded, Outcome.state] using SourceEqualityNativeDemandOperations.body_native request next before
  refine ⟨?_, ?_⟩
  · rw [same]
    exact stored.constructors
  · rw [same]
    exact stored.native

section Actual
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

/-- This internal return combines one actual physical body with its already-derived local result. -/
structure Receipt (annotation : Guard → Prop) (source : State Symbol Guard)
    (inventory : List DomainKey) (initial : Cache.State DomainKey)
    (fuel : Nat) (control : Control A) (before : Checked width) (value : A) (after : Checked width)
    (physicalPost post : Machine Symbol Guard → A → Prop) : Prop where
  /-- The same actual body trace retains all physical postconditions and state effects. -/
  physical : PhysicalReceipt source inventory initial fuel control before (.code (.pure value)) after physicalPost
  /-- The actual returned state retains both causal stores. -/
  stored : Stored annotation after
  /-- The smaller actual body supplies its local result law. -/
  result : post after.native.machine value

variable {annotation : Guard → Prop} {source : State Symbol Guard}
variable {inventory : List DomainKey} {initial : Cache.State DomainKey}

/-- Two actual completed receipts compose without an assumed future completion callback. -/
theorem join (next : A → Code Symbol Guard B) {fuel extra : Nat} {control : Control A}
    {before middle after : Checked width} {value : A} {output : B}
    {physicalPost post : Machine Symbol Guard → A → Prop} {outputPhysical outputPost : Machine Symbol Guard → B → Prop}
    (first : Receipt annotation source inventory initial fuel control before value middle physicalPost post)
    (last : Receipt annotation source inventory initial extra (.code (next value)) middle output after outputPhysical outputPost) :
    Receipt annotation source inventory initial (fuel + extra) (control.bind next) before output after outputPhysical outputPost :=
  ⟨SourceCurrentAllocatedRecursivePrefixReceipt.join next value first.physical last.physical, last.stored, last.result⟩

/-- The exact actual node body supplies its universal law before its captured finish step. -/
theorem finish_node {fuel handle : Nat} (request : NodeRequest Symbol Guard) {before middle : Checked width}
    {value : Value Symbol Guard} (known : Current source inventory initial before)
    (running : before.native.nodes.cells handle = some ⟨request, .evaluating⟩)
    (body : Receipt annotation source inventory initial fuel (.code (compileNode request)) before value middle
      (fun state value => Available state.heap value) (fun _ value => ∀ scope, NodeLaw annotation scope request value)) :
    Receipt annotation source inventory initial (fuel + 1)
        ((.code (compileNode request) : Control (Value Symbol Guard)).bind (fun value => .finishNode handle value (.pure value)))
        before value {middle with native := finishNode handle value middle.native}
        (fun state value => Available state.heap value) (fun _ value => ∀ scope, NodeLaw annotation scope request value) ∧
      (finishNode handle value middle.native).nodes.cells handle = some ⟨request, .returned value⟩ := by
  have available := body.physical.result value rfl
  have owner := SourceEqualityNativeDemandProtectedPrefix.node_body_owner fuel handle request before middle value
    known.good.native.shape running body.physical.trace.steps
  let finished : Checked width := {middle with native := finishNode handle value middle.native}
  have one : step (.code (.finishNode handle value (.pure value))) middle = .yielded (.code (.pure value)) finished := rfl
  have effects := SourceCurrentAllocatedRecursivePrefixState.yielded
    (.code (.finishNode handle value (.pure value))) (.code (.pure value)) middle finished body.physical.current
    ⟨request, owner.1, available⟩ trivial trivial one
  have terminal : PhysicalReceipt source inventory initial 0 (.code (.pure value)) finished (.code (.pure value)) finished
      (fun state value => Available state.heap value) :=
    SourceCurrentAllocatedRecursivePrefixReceipt.zero _ _ effects.1 trivial trivial trivial
      (by intro result same; cases same; exact effects.2.1.available value available)
  have frame := SourceCurrentAllocatedRecursivePrefixReceipt.before_step
    (.code (.finishNode handle value (.pure value))) (.code (.pure value)) middle finished body.physical.current
    ⟨request, owner.1, available⟩ trivial trivial one terminal
  have stored : Stored annotation finished := ⟨body.stored.constructors, fun scope =>
    SourceCurrentConstrainedCapNativeCache.finishNode_stored annotation scope middle.native handle request value
      body.physical.current.good.native (body.stored.native scope) owner.1 (body.result scope)⟩
  exact ⟨⟨SourceCurrentAllocatedRecursivePrefixReceipt.join (fun value => .finishNode handle value (.pure value))
    value body.physical frame, stored, body.result⟩, owner.2⟩

/-- The same checked edge body supplies its universal row law before exact owner publication. -/
theorem finish_edge {fuel handle : Nat} (request : EdgeRequest Symbol Guard) {before middle : Checked width}
    {value : EdgeValue Symbol Guard} (known : Current source inventory initial before)
    (running : before.native.edges.cells handle = some ⟨request, .evaluating⟩)
    (body : Receipt annotation source inventory initial fuel (.edgeBody request .pure) before value middle
      (fun state value => EdgeResident state.heap value) (fun _ value => ∀ scope, EdgeLaw annotation scope request value)) :
    Receipt annotation source inventory initial (fuel + 1)
        ((.edgeBody request .pure : Control (EdgeValue Symbol Guard)).bind (fun value => .finishEdge handle value (.pure value)))
        before value {middle with native := finishEdge handle value middle.native}
        (fun state value => EdgeResident state.heap value) (fun _ value => ∀ scope, EdgeLaw annotation scope request value) ∧
      (finishEdge handle value middle.native).edges.cells handle = some ⟨request, .returned value⟩ := by
  have resident := body.physical.result value rfl
  have owner := SourceEqualityNativeDemandProtectedPrefix.edge_body_owner fuel handle request before middle value
    known.good.native.shape running body.physical.trace.steps
  let finished : Checked width := {middle with native := finishEdge handle value middle.native}
  have one : step (.code (.finishEdge handle value (.pure value))) middle = .yielded (.code (.pure value)) finished := rfl
  have effects := SourceCurrentAllocatedRecursivePrefixState.yielded
    (.code (.finishEdge handle value (.pure value))) (.code (.pure value)) middle finished body.physical.current
    ⟨request, owner.1, resident⟩ trivial trivial one
  have terminal : PhysicalReceipt source inventory initial 0 (.code (.pure value)) finished (.code (.pure value)) finished
      (fun state value => EdgeResident state.heap value) :=
    SourceCurrentAllocatedRecursivePrefixReceipt.zero _ _ effects.1 trivial trivial trivial
      (by intro result same; cases same; exact edge_grows _ _ effects.2.1.heap value resident)
  have frame := SourceCurrentAllocatedRecursivePrefixReceipt.before_step
    (.code (.finishEdge handle value (.pure value))) (.code (.pure value)) middle finished body.physical.current
    ⟨request, owner.1, resident⟩ trivial trivial one terminal
  have stored : Stored annotation finished := ⟨body.stored.constructors, fun scope =>
    SourceCurrentConstrainedCapNativeCache.finishEdge_stored annotation scope middle.native handle request value
      body.physical.current.good.native (body.stored.native scope) owner.1 (body.result scope)⟩
  exact ⟨⟨SourceCurrentAllocatedRecursivePrefixReceipt.join (fun value => .finishEdge handle value (.pure value))
    value body.physical frame, stored, body.result⟩, owner.2⟩

/-- The produced node law supplies the original cap-code continuation at the same returned machine. -/
theorem next_node {fuel : Nat} {control : Control (Value Symbol Guard)} {before after : Checked width}
    {request : NodeRequest Symbol Guard} {value : Value Symbol Guard} {next : Value Symbol Guard → Code Symbol Guard A}
    {post : Machine Symbol Guard → A → Prop}
    (certificate : SourceCurrentConstrainedCapNativeCode.Certified annotation source (MuStored annotation)
      (.node request next) before.native.machine post)
    (body : Receipt annotation source inventory initial fuel control before value after
      (fun state value => Available state.heap value) (fun _ value => ∀ scope, NodeLaw annotation scope request value)) :
    SourceCurrentConstrainedCapNativeCode.Certified annotation source (MuStored annotation) (next value) after.native.machine post :=
  certificate value after.native.machine body.physical.current.good.native.machine body.physical.extension
    body.stored.constructors (body.physical.result value rfl) (body.result source)

/-- The produced row law supplies the original cap-code continuation at that exact returned machine. -/
theorem next_edge {fuel : Nat} {control : Control (EdgeValue Symbol Guard)} {before after : Checked width}
    {request : EdgeRequest Symbol Guard} {value : EdgeValue Symbol Guard} {next : EdgeValue Symbol Guard → Code Symbol Guard A}
    {post : Machine Symbol Guard → A → Prop}
    (certificate : SourceCurrentConstrainedCapNativeCode.Certified annotation source (MuStored annotation)
      (.edge request next) before.native.machine post)
    (body : Receipt annotation source inventory initial fuel control before value after
      (fun state value => EdgeResident state.heap value) (fun _ value => ∀ scope, EdgeLaw annotation scope request value)) :
    SourceCurrentConstrainedCapNativeCode.Certified annotation source (MuStored annotation) (next value) after.native.machine post :=
  certificate value after.native.machine body.physical.current.good.native.machine body.physical.extension
    body.stored.constructors (body.physical.result value rfl) (body.result source)

end Actual
end MicroCFTA.SourceCurrentConstrainedCapNativeTraceGlue
