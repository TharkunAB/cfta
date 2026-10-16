import MicroCFTA.SourceCurrentHereditaryNativeControl

/-!
# Smaller completed native traces and localCertificate hereditary laws

The physical prefix theorem supplies checks at the actual inner return.
The smaller completed trace supplies its localCertificate result and causal stores.
A captured finish installs that derived law for its exact running owner.
-/
namespace MicroCFTA.SourceCurrentHereditaryNativeTraceInduction
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceEqualityNativeDemand SourceEqualityAnnotationLanguage
open SourceCurrentAllocatedRecursivePrefixState
open SourceCurrentAllocatedNativeFieldClosure (Fields)
open SourceCurrentAllocatedRecursivePrefixAdmission (Resources)
open SourceCurrentHereditaryNativeCode (NodeLaw EdgeLaw)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "CodeFields" => SourceCurrentAllocatedNativeCodeFields.Fields
local notation "Physical" => SourceCurrentAllocatedRecursivePrefixControl.Certified
local notation "Local" => SourceCurrentHereditaryNativeControl.Certified
local notation "Stored" => SourceCurrentHereditaryNativeControl.Stored
local notation "DomainKey" => IntersectionFlatMemoKeyDomain.DomainKey
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
variable {bits : Nat} {source : InternedConstructorTemplates.State Symbol Guard}
variable {inventory : List DomainKey} {initial : Cache.State DomainKey}

/-- The literal source gate requires both empty equality extraction and no positive residual. -/
def Plain (guard : Guard) : Prop := SourceMemoGate.plain guard = true

/-- A completed trace retains both causal stores and its actual localCertificate result postcondition. -/
def Preserves (source : InternedConstructorTemplates.State Symbol Guard)
    (inventory : List DomainKey) (initial : Cache.State DomainKey) (bits fuel : Nat) : Prop :=
  ∀ {A : Type} (control : Control A) (before after : Checked (bits + 2)) (value : A)
    (physicalPost post : Machine Symbol Guard → A → Prop),
    Current source inventory initial before → Physical source inventory control before.native.machine physicalPost →
    Fields control before → Local Plain source control before.native.machine post → Stored Plain source before →
    Steps fuel control before (.code (.pure value)) after → Stored Plain source after ∧ post after.native.machine value

/-- Actual completed body and continuation traces compose at the same returned state. -/
theorem bind {A B : Type} (resources : Resources bits source inventory initial) (bound fuel : Nat)
    (ih : ∀ count, count < bound → Preserves source inventory initial bits count) (smaller : fuel < bound)
    (control : Control A) (next : A → Code Symbol Guard B)
    (before after : Checked (bits + 2)) (value : B)
    (bodyPhysical bodyPost : Machine Symbol Guard → A → Prop)
    (physicalPost post : Machine Symbol Guard → B → Prop)
    (known : Current source inventory initial before)
    (certificate : Physical source inventory control before.native.machine bodyPhysical)
    (fields : Fields control before) (nextFields : ∀ result, CodeFields before.operations (next result))
    (localCertificate : Local Plain source control before.native.machine bodyPost) (stored : Stored Plain source before)
    (physicalContinuation : ∀ result (current : Checked (bits + 2)), Current source inventory initial current →
      Extension before.native.machine current.native.machine → bodyPhysical current.native.machine result →
      Physical source inventory (.code (next result)) current.native.machine physicalPost)
    (continuation : ∀ result (current : Checked (bits + 2)), Current source inventory initial current →
      Extension before.native.machine current.native.machine → Stored Plain source current → bodyPost current.native.machine result →
      Local Plain source (.code (next result)) current.native.machine post)
    (trace : Steps fuel (control.bind next) before (.code (.pure value)) after) : Stored Plain source after ∧ post after.native.machine value := by
  obtain ⟨inner, outer, result, middle, count, bodyTrace, outerTrace⟩ := steps_bind_inverse fuel control next before after value trace
  have physical := SourceCurrentAllocatedRecursivePrefixAdmission.prefixes resources inner control before (.code (.pure result)) middle
    bodyPhysical known certificate fields bodyTrace
  have body := ih inner (by omega) control before middle result bodyPhysical bodyPost known certificate fields localCertificate stored bodyTrace
  have nextCertificate := physicalContinuation result middle physical.current physical.extension (physical.result result rfl)
  have nextLocal := continuation result middle physical.current physical.extension body.1 body.2
  have nextField := SourceCurrentAllocatedNativeCodeFields.fields_grows before.operations middle.operations
    (next result) (nextFields result) physical.operations
  exact ih outer (by omega) (.code (next result)) middle after value _ post physical.current nextCertificate nextField nextLocal body.1 outerTrace

/-- A node finish stores the localCertificate result derived from its strictly smaller actual body. -/
theorem node_bind {A : Type} (resources : Resources bits source inventory initial) (bound fuel handle : Nat)
    (ih : ∀ count, count < bound → Preserves source inventory initial bits count) (smaller : fuel < bound)
    (request : NodeRequest Symbol Guard) (next : Value Symbol Guard → Code Symbol Guard A)
    (before after : Checked (bits + 2)) (value : A) (physicalPost post : Machine Symbol Guard → A → Prop)
    (known : Current source inventory initial before)
    (certificate : Physical source inventory (.code (compileNode request)) before.native.machine (fun state result => Available state.heap result))
    (fields : Fields (.code (compileNode request)) before) (nextFields : ∀ result, CodeFields before.operations (next result))
    (localCertificate : Local Plain source (.code (compileNode request)) before.native.machine (fun state result => Available state.heap result ∧ Annotated Plain result))
    (stored : Stored Plain source before) (running : before.native.nodes.cells handle = some ⟨request, .evaluating⟩)
    (physicalContinuation : ∀ result (current : Checked (bits + 2)), Current source inventory initial current →
      Extension before.native.machine current.native.machine → Available current.native.machine.heap result →
      Physical source inventory (.code (next result)) current.native.machine physicalPost)
    (continuation : ∀ result (current : Checked (bits + 2)), Current source inventory initial current →
      Extension before.native.machine current.native.machine → Stored Plain source current →
      (Available current.native.machine.heap result ∧ Annotated Plain result) →
      Local Plain source (.code (next result)) current.native.machine post)
    (trace : Steps fuel ((.code (compileNode request) : Control (Value Symbol Guard)).bind
      (fun result => .finishNode handle result (next result))) before (.code (.pure value)) after) :
    Stored Plain source after ∧ post after.native.machine value := by
  obtain ⟨inner, frame, result, middle, count, bodyTrace, frameTrace⟩ := steps_bind_inverse fuel
    (.code (compileNode request)) (fun result => .finishNode handle result (next result)) before after value trace
  obtain ⟨rest, frameCount, outerTrace⟩ := SourceEqualityNativeDemandNodeReadback.finish_trace frame handle result (next result)
    middle after value frameTrace
  have physical := SourceCurrentAllocatedRecursivePrefixAdmission.prefixes resources inner _ before (.code (.pure result)) middle _
    known certificate fields bodyTrace
  have body := ih inner (by omega) _ before middle result _ _ known certificate fields localCertificate stored bodyTrace
  have available := physical.result result rfl
  have owner := (SourceEqualityNativeDemandProtectedPrefix.node_body_owner inner handle request before middle result
    known.good.native.shape running bodyTrace).1
  have law : NodeLaw Plain source request result := SourceCurrentHereditaryNativeControl.node_law Plain source request result body.2.2
  let finished : Checked (bits + 2) := {middle with native := SourceRecursiveIntersectionThunks.finishNode handle result middle.native}
  have frameFields : CodeFields middle.operations (.finishNode handle result (next result)) :=
    SourceCurrentAllocatedNativeCodeFields.fields_grows before.operations middle.operations (next result) (nextFields result) physical.operations
  have one : SourceEqualityNativeDemand.step (.code (.finishNode handle result (next result))) middle =
      .yielded (.code (next result)) finished := rfl
  have effects := SourceCurrentAllocatedRecursivePrefixState.yielded _ _ middle finished physical.current
    ⟨request, owner, available⟩ trivial frameFields one
  have kept : Stored Plain source finished := ⟨body.1.constructors,
    SourceCurrentHereditaryNativeCache.finishNode_stored Plain source middle.native handle request result body.1.native owner law⟩
  have output : Available finished.native.machine.heap result := effects.2.1.available result available
  have nextCertificate := physicalContinuation result finished effects.1 (physical.extension.trans effects.2.1) output
  have nextLocal := continuation result finished effects.1 (physical.extension.trans effects.2.1) kept ⟨output, body.2.2⟩
  exact ih rest (by omega) (.code (next result)) finished after value physicalPost post effects.1 nextCertificate
    effects.2.2.2.2 nextLocal kept outerTrace

/-- An edge finish stores the full annotated row derived from its actual checked body. -/
theorem edge_bind {A : Type} (resources : Resources bits source inventory initial) (bound fuel handle : Nat)
    (ih : ∀ count, count < bound → Preserves source inventory initial bits count) (smaller : fuel < bound)
    (request : EdgeRequest Symbol Guard) (next : EdgeValue Symbol Guard → Code Symbol Guard A)
    (before after : Checked (bits + 2)) (value : A) (physicalPost post : Machine Symbol Guard → A → Prop)
    (known : Current source inventory initial before)
    (certificate : Physical source inventory (.edgeBody request .pure) before.native.machine (fun state result => EdgeResident state.heap result))
    (fields : Fields (.edgeBody request .pure) before) (nextFields : ∀ result, CodeFields before.operations (next result))
    (localCertificate : Local Plain source (.edgeBody request .pure) before.native.machine
      (fun state result => EdgeResident state.heap result ∧ SourceCurrentHereditaryConstructors.Edge Plain result)) (stored : Stored Plain source before)
    (running : before.native.edges.cells handle = some ⟨request, .evaluating⟩)
    (physicalContinuation : ∀ result (current : Checked (bits + 2)), Current source inventory initial current →
      Extension before.native.machine current.native.machine → EdgeResident current.native.machine.heap result →
      Physical source inventory (.code (next result)) current.native.machine physicalPost)
    (continuation : ∀ result (current : Checked (bits + 2)), Current source inventory initial current →
      Extension before.native.machine current.native.machine → Stored Plain source current →
      (EdgeResident current.native.machine.heap result ∧ SourceCurrentHereditaryConstructors.Edge Plain result) →
      Local Plain source (.code (next result)) current.native.machine post)
    (trace : Steps fuel ((.edgeBody request .pure : Control (EdgeValue Symbol Guard)).bind
      (fun result => .finishEdge handle result (next result))) before (.code (.pure value)) after) :
    Stored Plain source after ∧ post after.native.machine value := by
  obtain ⟨inner, frame, result, middle, count, bodyTrace, frameTrace⟩ := steps_bind_inverse fuel
    (.edgeBody request .pure) (fun result => .finishEdge handle result (next result)) before after value trace
  obtain ⟨rest, frameCount, outerTrace⟩ := SourceEqualityNativeDemandRunning.finish_edge_trace frame handle result (next result)
    middle after value frameTrace
  have physical := SourceCurrentAllocatedRecursivePrefixAdmission.prefixes resources inner _ before (.code (.pure result)) middle _
    known certificate fields bodyTrace
  have body := ih inner (by omega) _ before middle result _ _ known certificate fields localCertificate stored bodyTrace
  have resident := physical.result result rfl
  have owner := (SourceEqualityNativeDemandProtectedPrefix.edge_body_owner inner handle request before middle result
    known.good.native.shape running bodyTrace).1
  have law : EdgeLaw Plain source request result := SourceCurrentHereditaryNativeControl.edge_law Plain source request result body.2.2
  let finished : Checked (bits + 2) := {middle with native := SourceRecursiveIntersectionThunks.finishEdge handle result middle.native}
  have frameFields : CodeFields middle.operations (.finishEdge handle result (next result)) :=
    SourceCurrentAllocatedNativeCodeFields.fields_grows before.operations middle.operations (next result) (nextFields result) physical.operations
  have one : SourceEqualityNativeDemand.step (.code (.finishEdge handle result (next result))) middle =
      .yielded (.code (next result)) finished := rfl
  have effects := SourceCurrentAllocatedRecursivePrefixState.yielded _ _ middle finished physical.current
    ⟨request, owner, resident⟩ trivial frameFields one
  have kept : Stored Plain source finished := ⟨body.1.constructors,
    SourceCurrentHereditaryNativeCache.finishEdge_stored Plain source middle.native handle request result body.1.native owner law⟩
  have output : EdgeResident finished.native.machine.heap result := edge_grows _ _ effects.2.1.heap result resident
  have nextCertificate := physicalContinuation result finished effects.1 (physical.extension.trans effects.2.1) output
  have nextLocal := continuation result finished effects.1 (physical.extension.trans effects.2.1) kept ⟨output, body.2.2⟩
  exact ih rest (by omega) (.code (next result)) finished after value physicalPost post effects.1 nextCertificate
    effects.2.2.2.2 nextLocal kept outerTrace

end MicroCFTA.SourceCurrentHereditaryNativeTraceInduction
