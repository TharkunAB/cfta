import MicroCFTA.SourceCurrentAllocatedRecursivePrefixControl
import MicroCFTA.SourceCurrentAllocatedRecursivePrefixReceipt

/-!
# Smaller actual body prefixes and captured finish continuations

The induction hypothesis applies only to strictly shorter raw prefixes.
An actual inner return supplies the physical post before the captured finish
step. An unfinished inner prefix retains its literal outer continuation.
-/
namespace MicroCFTA.SourceCurrentAllocatedRecursivePrefixInduction
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceEqualityNativeDemand SourceCurrentAllocatedRecursivePrefixState
open SourceCurrentAllocatedNativeFieldClosure (Fields)
open SourceCurrentAllocatedRecursivePrefixReceipt (Receipt)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "CodeFields" => SourceCurrentAllocatedNativeCodeFields.Fields
local notation "Certified" => SourceCurrentAllocatedRecursivePrefixControl.Certified
local notation "DomainKey" => IntersectionFlatMemoKeyDomain.DomainKey
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
variable {width : Nat} {source : InternedConstructorTemplates.State Symbol Guard}
variable {inventory : List DomainKey} {initial : Cache.State DomainKey}

/-- Admission constructs the checks of a supplied raw prefix from its local source certificate. -/
def Admits (source : InternedConstructorTemplates.State Symbol Guard)
    (inventory : List DomainKey) (initial : Cache.State DomainKey) (width fuel : Nat) : Prop :=
  ∀ {A : Type} (control : Control A) (before : Checked width) (remaining : Control A) (after : Checked width)
    (post : Machine Symbol Guard → A → Prop), Current source inventory initial before →
    Certified source inventory control before.native.machine post → Fields control before →
    Steps fuel control before remaining after → Receipt source inventory initial fuel control before remaining after post

/-- Smaller body and continuation prefixes compose at their exact actual return. -/
theorem bind {A B : Type} (bound fuel : Nat)
    (ih : ∀ count, count < bound → Admits source inventory initial width count)
    (smaller : fuel < bound) (control : Control A) (next : A → Code Symbol Guard B)
    (before after : Checked width) (remaining : Control B)
    (bodyPost : Machine Symbol Guard → A → Prop) (post : Machine Symbol Guard → B → Prop)
    (known : Current source inventory initial before)
    (certificate : Certified source inventory control before.native.machine bodyPost)
    (fields : Fields control before) (nextFields : ∀ value, CodeFields before.operations (next value))
    (continuation : ∀ value (current : Checked width), Current source inventory initial current →
      Extension before.native.machine current.native.machine → bodyPost current.native.machine value →
      Certified source inventory (.code (next value)) current.native.machine post)
    (trace : Steps fuel (control.bind next) before remaining after) :
    Receipt source inventory initial fuel (control.bind next) before remaining after post := by
  rcases steps_bind_cases fuel control next before after remaining trace with
    ⟨inner, bodyTrace, nonpure, rfl⟩ | ⟨inner, outer, value, middle, count, bodyTrace, outerTrace⟩
  · exact SourceCurrentAllocatedRecursivePrefixReceipt.bind_inside next
      (ih fuel smaller control before inner after bodyPost known certificate fields bodyTrace)
      nonpure nextFields post
  · have body := ih inner (by omega) control before (.code (.pure value)) middle bodyPost known certificate fields bodyTrace
    have nextCertificate := continuation value middle body.current body.extension (body.result value rfl)
    have nextField := SourceCurrentAllocatedNativeCodeFields.fields_grows before.operations middle.operations
      (next value) (nextFields value) body.operations
    have later := ih outer (by omega) (.code (next value)) middle remaining after post
      body.current nextCertificate nextField outerTrace
    simpa only [count] using SourceCurrentAllocatedRecursivePrefixReceipt.join next value body later

/-- A captured node finish receives its physical post from a smaller actual body trace. -/
theorem node_bind {A : Type} (bound fuel handle : Nat)
    (ih : ∀ count, count < bound → Admits source inventory initial width count)
    (smaller : fuel < bound) (request : NodeRequest Symbol Guard)
    (next : Value Symbol Guard → Code Symbol Guard A)
    (before after : Checked width) (remaining : Control A) (post : Machine Symbol Guard → A → Prop)
    (known : Current source inventory initial before)
    (certificate : Certified source inventory (.code (compileNode request)) before.native.machine
      (fun final value => Available final.heap value))
    (fields : Fields (.code (compileNode request)) before)
    (nextFields : ∀ value, CodeFields before.operations (next value))
    (running : before.native.nodes.cells handle = some ⟨request, .evaluating⟩)
    (continuation : ∀ value (current : Checked width), Current source inventory initial current →
      Extension before.native.machine current.native.machine → Available current.native.machine.heap value →
      Certified source inventory (.code (next value)) current.native.machine post)
    (trace : Steps fuel ((.code (compileNode request) : Control (Value Symbol Guard)).bind
      (fun value => .finishNode handle value (next value))) before remaining after) :
    Receipt source inventory initial fuel ((.code (compileNode request) : Control (Value Symbol Guard)).bind
      (fun value => .finishNode handle value (next value))) before remaining after post := by
  rcases SourceEqualityNativeDemandProtectedPrefix.node_cases fuel handle request next before after remaining
      known.good.native.shape running trace with
    ⟨inner, bodyTrace, nonpure, rfl⟩ |
      ⟨bodyFuel, frameFuel, value, middle, count, _, bodyTrace, owner, _, frame⟩
  · exact SourceCurrentAllocatedRecursivePrefixReceipt.bind_inside (fun value => .finishNode handle value (next value))
      (ih fuel smaller _ before inner after _ known certificate fields bodyTrace)
      nonpure nextFields post
  · have body := ih bodyFuel (by omega) _ before (.code (.pure value)) middle _ known certificate fields bodyTrace
    have available := body.result value rfl
    have frameFields : CodeFields middle.operations (.finishNode handle value (next value)) :=
      SourceCurrentAllocatedNativeCodeFields.fields_grows before.operations middle.operations
        (next value) (nextFields value) body.operations
    rcases frame with ⟨zeroFrame, same, retained⟩ | ⟨rest, rfl, outerTrace⟩
    · subst frameFuel
      subst remaining
      subst after
      have stopped : Receipt source inventory initial 0
          (.code (.finishNode handle value (next value))) middle
          (.code (.finishNode handle value (next value))) middle post :=
        SourceCurrentAllocatedRecursivePrefixReceipt.zero _ middle body.current ⟨request, owner, available⟩
          trivial frameFields (by intro output impossible; cases impossible)
      simpa only [count] using SourceCurrentAllocatedRecursivePrefixReceipt.join
        (fun value => .finishNode handle value (next value)) value body stopped
    · let finished : Checked width := {middle with native := SourceRecursiveIntersectionThunks.finishNode handle value middle.native}
      have one : SourceEqualityNativeDemand.step (.code (.finishNode handle value (next value))) middle =
          .yielded (.code (next value)) finished := rfl
      have effects := SourceCurrentAllocatedRecursivePrefixState.yielded
        (.code (.finishNode handle value (next value))) (.code (next value)) middle finished body.current
        ⟨request, owner, available⟩ trivial frameFields one
      have output : Available finished.native.machine.heap value := effects.2.1.available value available
      have nextCertificate := continuation value finished effects.1 (body.extension.trans effects.2.1) output
      have later := ih rest (by omega) (.code (next value)) finished remaining after post
        effects.1 nextCertificate effects.2.2.2.2 outerTrace
      have frame := SourceCurrentAllocatedRecursivePrefixReceipt.before_step
        (.code (.finishNode handle value (next value))) (.code (next value)) middle finished body.current
        ⟨request, owner, available⟩ trivial frameFields one later
      simpa only [count] using SourceCurrentAllocatedRecursivePrefixReceipt.join
        (fun value => .finishNode handle value (next value)) value body frame

/-- A captured edge finish uses the actual checked body's physical resident return. -/
theorem edge_bind {A : Type} (bound fuel handle : Nat)
    (ih : ∀ count, count < bound → Admits source inventory initial width count)
    (smaller : fuel < bound) (request : EdgeRequest Symbol Guard)
    (next : EdgeValue Symbol Guard → Code Symbol Guard A)
    (before after : Checked width) (remaining : Control A) (post : Machine Symbol Guard → A → Prop)
    (known : Current source inventory initial before)
    (certificate : Certified source inventory (.edgeBody request .pure) before.native.machine
      (fun final value => EdgeResident final.heap value))
    (fields : Fields (.edgeBody request .pure) before)
    (nextFields : ∀ value, CodeFields before.operations (next value))
    (running : before.native.edges.cells handle = some ⟨request, .evaluating⟩)
    (continuation : ∀ value (current : Checked width), Current source inventory initial current →
      Extension before.native.machine current.native.machine → EdgeResident current.native.machine.heap value →
      Certified source inventory (.code (next value)) current.native.machine post)
    (trace : Steps fuel ((.edgeBody request .pure : Control (EdgeValue Symbol Guard)).bind
      (fun value => .finishEdge handle value (next value))) before remaining after) :
    Receipt source inventory initial fuel ((.edgeBody request .pure : Control (EdgeValue Symbol Guard)).bind
      (fun value => .finishEdge handle value (next value))) before remaining after post := by
  rcases SourceEqualityNativeDemandProtectedPrefix.edge_cases fuel handle request next before after remaining
      known.good.native.shape running trace with
    ⟨inner, bodyTrace, nonpure, rfl⟩ |
      ⟨bodyFuel, frameFuel, value, middle, count, _, bodyTrace, owner, _, frame⟩
  · exact SourceCurrentAllocatedRecursivePrefixReceipt.bind_inside (fun value => .finishEdge handle value (next value))
      (ih fuel smaller _ before inner after _ known certificate fields bodyTrace)
      nonpure nextFields post
  · have body := ih bodyFuel (by omega) _ before (.code (.pure value)) middle _ known certificate fields bodyTrace
    have resident := body.result value rfl
    have frameFields : CodeFields middle.operations (.finishEdge handle value (next value)) :=
      SourceCurrentAllocatedNativeCodeFields.fields_grows before.operations middle.operations
        (next value) (nextFields value) body.operations
    rcases frame with ⟨zeroFrame, same, retained⟩ | ⟨rest, rfl, outerTrace⟩
    · subst frameFuel
      subst remaining
      subst after
      have stopped : Receipt source inventory initial 0
          (.code (.finishEdge handle value (next value))) middle
          (.code (.finishEdge handle value (next value))) middle post :=
        SourceCurrentAllocatedRecursivePrefixReceipt.zero _ middle body.current ⟨request, owner, resident⟩
          trivial frameFields (by intro output impossible; cases impossible)
      simpa only [count] using SourceCurrentAllocatedRecursivePrefixReceipt.join
        (fun value => .finishEdge handle value (next value)) value body stopped
    · let finished : Checked width := {middle with native := SourceRecursiveIntersectionThunks.finishEdge handle value middle.native}
      have one : SourceEqualityNativeDemand.step (.code (.finishEdge handle value (next value))) middle =
          .yielded (.code (next value)) finished := rfl
      have effects := SourceCurrentAllocatedRecursivePrefixState.yielded
        (.code (.finishEdge handle value (next value))) (.code (next value)) middle finished body.current
        ⟨request, owner, resident⟩ trivial frameFields one
      have output : EdgeResident finished.native.machine.heap value := edge_grows _ _ effects.2.1.heap value resident
      have nextCertificate := continuation value finished effects.1 (body.extension.trans effects.2.1) output
      have later := ih rest (by omega) (.code (next value)) finished remaining after post
        effects.1 nextCertificate effects.2.2.2.2 outerTrace
      have frame := SourceCurrentAllocatedRecursivePrefixReceipt.before_step
        (.code (.finishEdge handle value (next value))) (.code (next value)) middle finished body.current
        ⟨request, owner, resident⟩ trivial frameFields one later
      simpa only [count] using SourceCurrentAllocatedRecursivePrefixReceipt.join
        (fun value => .finishEdge handle value (next value)) value body frame

end MicroCFTA.SourceCurrentAllocatedRecursivePrefixInduction
