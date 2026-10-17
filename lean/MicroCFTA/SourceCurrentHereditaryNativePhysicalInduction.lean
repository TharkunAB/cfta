import MicroCFTA.SourceCurrentHereditaryNativeUniversalStore
import MicroCFTA.SourceCurrentHereditaryNativePhysicalSplit

/-!
# Smaller completed native traces and local hereditary laws

The supplied physical trace retains checks at the actual inner return.
The smaller completed trace supplies its local result and causal stores.
A captured finish installs that derived law for its exact running owner.
-/
namespace MicroCFTA.SourceCurrentHereditaryNativePhysicalInduction
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceEqualityNativeDemand SourceEqualityAnnotationLanguage
open SourceCurrentAllocatedRecursivePrefixState
open SourceCurrentAllocatedNativeFieldClosure (Fields)
open SourceCurrentAllocatedNativePhysicalTraceCompletion (Trace)
open SourceCurrentHereditaryNativeCode (NodeLaw EdgeLaw)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "CodeFields" => SourceCurrentAllocatedNativeCodeFields.Fields
local notation "Physical" => SourceCurrentAllocatedRecursivePrefixControl.Certified
local notation "Local" => SourceCurrentHereditaryNativeControl.Certified
local notation "Stored" => SourceCurrentHereditaryNativeUniversalStore.Stored
local notation "DomainKey" => IntersectionFlatMemoKeyDomain.DomainKey
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
variable {width : Nat} {source : InternedConstructorTemplates.State Symbol Guard}
variable {inventory : List DomainKey} {initial : Cache.State DomainKey}

/-- The literal source gate requires empty equalities and supported positive syntax. -/
def Plain (guard : Guard) : Prop := SourceMemoGate.plain guard = true

/-- An actual completed return derives its physical and hereditary facts together. -/
structure Return [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (before after : Checked width) (value : A)
    (physicalPost post : Machine Symbol Guard → A → Prop) : Prop where
  /-- The returned machine retains physical and semantic readiness. -/
  current : Current source inventory initial after
  /-- The actual return retains the initial machine records. -/
  extension : Extension before.native.machine after.native.machine
  /-- The actual return retains equality-operation entries. -/
  operations : SourceEqualityConstraintMemoAllocation.Grows before.operations after.operations
  /-- Both causal annotation stores hold at the returned state. -/
  stored : Stored Plain after
  /-- The returned value satisfies the local physical postcondition. -/
  physical : physicalPost after.native.machine value
  /-- The returned value satisfies the local hereditary postcondition. -/
  result : post after.native.machine value

/-- Earlier actual machine effects compose with the same completed return. -/
theorem Return.prepend {middle : Checked width}
    (growth : Extension before.native.machine middle.native.machine)
    (operations : SourceEqualityConstraintMemoAllocation.Grows before.operations middle.operations)
    (later : Return (source := source) (inventory := inventory) (initial := initial) middle after value physicalPost post) :
    Return (source := source) (inventory := inventory) (initial := initial) before after value physicalPost post :=
  ⟨later.current, growth.trans later.extension,
    SourceCurrentAllocatedRecursivePrefixReceipt.operations_trans operations later.operations,
    later.stored, later.physical, later.result⟩

/-- A physical trace supplies the current checks without an initial capacity premise. -/
def Preserves (source : InternedConstructorTemplates.State Symbol Guard)
    (inventory : List DomainKey) (initial : Cache.State DomainKey) (width fuel : Nat) : Prop :=
  ∀ {A : Type} (control : Control A) (before after : Checked width) (value : A)
    (physicalPost post : Machine Symbol Guard → A → Prop),
    Current source inventory initial before → Physical source inventory control before.native.machine physicalPost →
    Fields control before → Local Plain source control before.native.machine post → Stored Plain before →
    Trace fuel control before (.code (.pure value)) after →
    Return (source := source) (inventory := inventory) (initial := initial) before after value physicalPost post

/-- Actual completed body and continuation traces compose at the same returned state. -/
theorem bind {A B : Type} (bound fuel : Nat)
    (ih : ∀ count, count < bound → Preserves source inventory initial width count) (smaller : fuel < bound)
    (control : Control A) (next : A → Code Symbol Guard B)
    (before after : Checked width) (value : B)
    (bodyPhysical bodyPost : Machine Symbol Guard → A → Prop)
    (physicalPost post : Machine Symbol Guard → B → Prop)
    (known : Current source inventory initial before)
    (certificate : Physical source inventory control before.native.machine bodyPhysical)
    (fields : Fields control before) (nextFields : ∀ result, CodeFields before.operations (next result))
    (localCertificate : Local Plain source control before.native.machine bodyPost) (stored : Stored Plain before)
    (physicalContinuation : ∀ result (current : Checked width), Current source inventory initial current →
      Extension before.native.machine current.native.machine → bodyPhysical current.native.machine result →
      Physical source inventory (.code (next result)) current.native.machine physicalPost)
    (continuation : ∀ result (current : Checked width), Current source inventory initial current →
      Extension before.native.machine current.native.machine → Stored Plain current → bodyPost current.native.machine result →
      Local Plain source (.code (next result)) current.native.machine post)
    (trace : Trace fuel (control.bind next) before (.code (.pure value)) after) : Return (source := source) (inventory := inventory) (initial := initial) before after value physicalPost post := by
  obtain ⟨inner, outer, result, middle, count, bodyTrace, outerTrace⟩ := SourceCurrentHereditaryNativePhysicalSplit.bind_split control next before after value trace
  have body := ih inner (by omega) control before middle result bodyPhysical bodyPost known certificate fields localCertificate stored bodyTrace
  have physical := body
  have nextCertificate := physicalContinuation result middle physical.current physical.extension physical.physical
  have nextLocal := continuation result middle physical.current physical.extension body.stored body.result
  have nextField := SourceCurrentAllocatedNativeCodeFields.fields_grows before.operations middle.operations
    (next result) (nextFields result) physical.operations
  have outerResult := ih outer (by omega) (.code (next result)) middle after value _ post physical.current nextCertificate nextField nextLocal body.stored outerTrace
  exact ⟨outerResult.current, body.extension.trans outerResult.extension,
    SourceCurrentAllocatedRecursivePrefixReceipt.operations_trans body.operations outerResult.operations,
    outerResult.stored, outerResult.physical, outerResult.result⟩

/-- A node finish stores the local result derived from its strictly smaller actual body. -/
theorem node_bind {A : Type} (bound fuel handle : Nat)
    (ih : ∀ count, count < bound → Preserves source inventory initial width count) (smaller : fuel < bound)
    (request : NodeRequest Symbol Guard) (next : Value Symbol Guard → Code Symbol Guard A)
    (before after : Checked width) (value : A) (physicalPost post : Machine Symbol Guard → A → Prop)
    (known : Current source inventory initial before)
    (certificate : Physical source inventory (.code (compileNode request)) before.native.machine (fun state result => Available state.heap result))
    (fields : Fields (.code (compileNode request)) before) (nextFields : ∀ result, CodeFields before.operations (next result))
    (localCertificate : Local Plain source (.code (compileNode request)) before.native.machine (fun state result => Available state.heap result ∧ Annotated Plain result))
    (stored : Stored Plain before) (running : before.native.nodes.cells handle = some ⟨request, .evaluating⟩)
    (physicalContinuation : ∀ result (current : Checked width), Current source inventory initial current →
      Extension before.native.machine current.native.machine → Available current.native.machine.heap result →
      Physical source inventory (.code (next result)) current.native.machine physicalPost)
    (continuation : ∀ result (current : Checked width), Current source inventory initial current →
      Extension before.native.machine current.native.machine → Stored Plain current →
      (Available current.native.machine.heap result ∧ Annotated Plain result) →
      Local Plain source (.code (next result)) current.native.machine post)
    (trace : Trace fuel ((.code (compileNode request) : Control (Value Symbol Guard)).bind
      (fun result => .finishNode handle result (next result))) before (.code (.pure value)) after) :
    Return (source := source) (inventory := inventory) (initial := initial) before after value physicalPost post := by
  obtain ⟨inner, frame, result, middle, count, bodyTrace, frameTrace⟩ := SourceCurrentHereditaryNativePhysicalSplit.bind_split
    (.code (compileNode request)) (fun result => .finishNode handle result (next result)) before after value trace
  cases frameTrace with
  | cons _ _ chosen reached _ _ rest frameInputs frameStep outerTrace =>
    have finishStep : SourceEqualityNativeDemand.step (.code (.finishNode handle result (next result))) middle =
        .yielded (.code (next result)) {middle with native := SourceRecursiveIntersectionThunks.finishNode handle result middle.native} := rfl
    obtain ⟨rfl, rfl⟩ := Outcome.yielded.inj (frameStep.symm.trans finishStep)
    have body := ih inner (by omega) _ before middle result _ _ known certificate fields localCertificate stored bodyTrace
    have physical := body
    have available := physical.physical
    have owner := (SourceEqualityNativeDemandProtectedPrefix.node_body_owner inner handle request before middle result
      known.good.native.shape running bodyTrace.steps).1
    let finished : Checked width := {middle with native := SourceRecursiveIntersectionThunks.finishNode handle result middle.native}
    have frameFields : CodeFields middle.operations (.finishNode handle result (next result)) :=
      SourceCurrentAllocatedNativeCodeFields.fields_grows before.operations middle.operations (next result) (nextFields result) physical.operations
    have one : SourceEqualityNativeDemand.step (.code (.finishNode handle result (next result))) middle =
        .yielded (.code (next result)) finished := rfl
    have effects := SourceCurrentAllocatedRecursivePrefixState.yielded
      (.code (.finishNode handle result (next result))) (.code (next result)) middle finished physical.current
      ⟨request, owner, available⟩ trivial frameFields one
    have kept : Stored Plain finished := SourceCurrentHereditaryNativeUniversalStore.finishNode Plain middle handle request result body.stored owner body.result.2
    have output : Available finished.native.machine.heap result := effects.2.1.available result available
    have nextCertificate := physicalContinuation result finished effects.1 (physical.extension.trans effects.2.1) output
    have nextLocal := continuation result finished effects.1 (physical.extension.trans effects.2.1) kept ⟨output, body.result.2⟩
    have outerResult := ih rest (by omega) (.code (next result)) finished after value physicalPost post effects.1 nextCertificate
      effects.2.2.2.2 nextLocal kept outerTrace
    exact ⟨outerResult.current, body.extension.trans (effects.2.1.trans outerResult.extension),
      SourceCurrentAllocatedRecursivePrefixReceipt.operations_trans body.operations
        (SourceCurrentAllocatedRecursivePrefixReceipt.operations_trans effects.2.2.2.1 outerResult.operations),
      outerResult.stored, outerResult.physical, outerResult.result⟩

/-- An edge finish stores the full annotated row derived from its actual checked body. -/
theorem edge_bind {A : Type} (bound fuel handle : Nat)
    (ih : ∀ count, count < bound → Preserves source inventory initial width count) (smaller : fuel < bound)
    (request : EdgeRequest Symbol Guard) (next : EdgeValue Symbol Guard → Code Symbol Guard A)
    (before after : Checked width) (value : A) (physicalPost post : Machine Symbol Guard → A → Prop)
    (known : Current source inventory initial before)
    (certificate : Physical source inventory (.edgeBody request .pure) before.native.machine (fun state result => EdgeResident state.heap result))
    (fields : Fields (.edgeBody request .pure) before) (nextFields : ∀ result, CodeFields before.operations (next result))
    (localCertificate : Local Plain source (.edgeBody request .pure) before.native.machine
      (fun state result => EdgeResident state.heap result ∧ SourceCurrentHereditaryConstructors.Edge Plain result)) (stored : Stored Plain before)
    (running : before.native.edges.cells handle = some ⟨request, .evaluating⟩)
    (physicalContinuation : ∀ result (current : Checked width), Current source inventory initial current →
      Extension before.native.machine current.native.machine → EdgeResident current.native.machine.heap result →
      Physical source inventory (.code (next result)) current.native.machine physicalPost)
    (continuation : ∀ result (current : Checked width), Current source inventory initial current →
      Extension before.native.machine current.native.machine → Stored Plain current →
      (EdgeResident current.native.machine.heap result ∧ SourceCurrentHereditaryConstructors.Edge Plain result) →
      Local Plain source (.code (next result)) current.native.machine post)
    (trace : Trace fuel ((.edgeBody request .pure : Control (EdgeValue Symbol Guard)).bind
      (fun result => .finishEdge handle result (next result))) before (.code (.pure value)) after) :
    Return (source := source) (inventory := inventory) (initial := initial) before after value physicalPost post := by
  obtain ⟨inner, frame, result, middle, count, bodyTrace, frameTrace⟩ := SourceCurrentHereditaryNativePhysicalSplit.bind_split
    (.edgeBody request .pure) (fun result => .finishEdge handle result (next result)) before after value trace
  cases frameTrace with
  | cons _ _ chosen reached _ _ rest frameInputs frameStep outerTrace =>
    have finishStep : SourceEqualityNativeDemand.step (.code (.finishEdge handle result (next result))) middle =
        .yielded (.code (next result)) {middle with native := SourceRecursiveIntersectionThunks.finishEdge handle result middle.native} := rfl
    obtain ⟨rfl, rfl⟩ := Outcome.yielded.inj (frameStep.symm.trans finishStep)
    have body := ih inner (by omega) _ before middle result _ _ known certificate fields localCertificate stored bodyTrace
    have physical := body
    have resident := physical.physical
    have owner := (SourceEqualityNativeDemandProtectedPrefix.edge_body_owner inner handle request before middle result
      known.good.native.shape running bodyTrace.steps).1
    let finished : Checked width := {middle with native := SourceRecursiveIntersectionThunks.finishEdge handle result middle.native}
    have frameFields : CodeFields middle.operations (.finishEdge handle result (next result)) :=
      SourceCurrentAllocatedNativeCodeFields.fields_grows before.operations middle.operations (next result) (nextFields result) physical.operations
    have one : SourceEqualityNativeDemand.step (.code (.finishEdge handle result (next result))) middle =
        .yielded (.code (next result)) finished := rfl
    have effects := SourceCurrentAllocatedRecursivePrefixState.yielded
      (.code (.finishEdge handle result (next result))) (.code (next result)) middle finished physical.current
      ⟨request, owner, resident⟩ trivial frameFields one
    have kept : Stored Plain finished := SourceCurrentHereditaryNativeUniversalStore.finishEdge Plain middle handle request result body.stored owner body.result.2
    have output : EdgeResident finished.native.machine.heap result := edge_grows _ _ effects.2.1.heap result resident
    have nextCertificate := physicalContinuation result finished effects.1 (physical.extension.trans effects.2.1) output
    have nextLocal := continuation result finished effects.1 (physical.extension.trans effects.2.1) kept ⟨output, body.result.2⟩
    have outerResult := ih rest (by omega) (.code (next result)) finished after value physicalPost post effects.1 nextCertificate
      effects.2.2.2.2 nextLocal kept outerTrace
    exact ⟨outerResult.current, body.extension.trans (effects.2.1.trans outerResult.extension),
      SourceCurrentAllocatedRecursivePrefixReceipt.operations_trans body.operations
        (SourceCurrentAllocatedRecursivePrefixReceipt.operations_trans effects.2.2.2.1 outerResult.operations),
      outerResult.stored, outerResult.physical, outerResult.result⟩

end MicroCFTA.SourceCurrentHereditaryNativePhysicalInduction
