import MicroCFTA.SourceCurrentAllocatedRecursivePrefixAdmission

/-!
# Fixed-source scope at an actual reached node request

An actual raw prefix retains the original operand scope of its reached
node instruction. Protected finish frames need no source certificate.
The fixed source heap is separate from an original source-program path.
-/
namespace MicroCFTA.SourceCurrentAllocatedRecursivePrefixScope
open Cache InternedConstructorTemplates InternedProbeProvenance InternedNestedFacts InternedEdgeResidency
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceEqualityNativeDemand SourceCurrentAllocatedRecursivePrefixState
open SourceCurrentAllocatedNativeFieldClosure (Fields)
open SourceCurrentAllocatedRecursivePrefixInduction (Admits)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Certified" => SourceCurrentAllocatedRecursivePrefixControl.Certified
local notation "CodeFields" => SourceCurrentAllocatedNativeCodeFields.Fields
local notation "DomainKey" => IntersectionFlatMemoKeyDomain.DomainKey

private def Head (source : InternedConstructorTemplates.State Symbol Guard)
    (inventory : List DomainKey) : Control A → Prop
  | .code (.node request _) => NodeScope source request ∧ request.domain.key ∈ inventory
  | _ => True

private theorem head_bind (source : InternedConstructorTemplates.State Symbol Guard)
    (inventory : List DomainKey) (control : Control A) (next : A → Code Symbol Guard B)
    (nonpure : ∀ value, control ≠ .code (.pure value)) (head : Head source inventory control) :
    Head source inventory (control.bind next) := by
  cases control with
  | edgeBody => trivial
  | code code =>
    cases code with
    | pure value => exact False.elim (nonpure value rfl)
    | node => exact head
    | _ => trivial

private theorem head_certified [DecidableEq (EdgeKey Symbol Guard)]
    (source : InternedConstructorTemplates.State Symbol Guard) (inventory : List DomainKey)
    (control : Control A) (state : Machine Symbol Guard) (post : Machine Symbol Guard → A → Prop)
    (certificate : Certified source inventory control state post) : Head source inventory control := by
  cases control with
  | edgeBody => trivial
  | code code =>
    cases code with
    | node request next =>
      exact (SourceCurrentAllocatedRecursivePrefixCode.node_data source inventory request next state post certificate).2
    | _ => trivial

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
variable {width : Nat} {source : InternedConstructorTemplates.State Symbol Guard}
variable {inventory : List DomainKey} {initial : Cache.State DomainKey}

private def Scoped (fuel : Nat) : Prop :=
  ∀ {A : Type} (control : Control A) (before : Checked width) (remaining : Control A) (after : Checked width)
    (post : Machine Symbol Guard → A → Prop), Current source inventory initial before →
    Certified source inventory control before.native.machine post → Fields control before →
    Steps fuel control before remaining after → Head source inventory remaining

private theorem scoped_bind {A B : Type} (bound fuel : Nat)
    (admit : ∀ count, Admits source inventory initial width count)
    (ih : ∀ count, count < bound → Scoped (width := width) (source := source) (inventory := inventory) (initial := initial) count)
    (smaller : fuel < bound) (control : Control A) (next : A → Code Symbol Guard B)
    (before after : Checked width) (remaining : Control B)
    (bodyPost : Machine Symbol Guard → A → Prop) (post : Machine Symbol Guard → B → Prop)
    (known : Current source inventory initial before)
    (certificate : Certified source inventory control before.native.machine bodyPost)
    (fields : Fields control before) (nextFields : ∀ value, CodeFields before.operations (next value))
    (continuation : ∀ value (current : Checked width), Current source inventory initial current →
      Extension before.native.machine current.native.machine → bodyPost current.native.machine value →
      Certified source inventory (.code (next value)) current.native.machine post)
    (trace : Steps fuel (control.bind next) before remaining after) : Head source inventory remaining := by
  rcases steps_bind_cases fuel control next before after remaining trace with
    ⟨inner,bodyTrace,nonpure,rfl⟩ | ⟨inner,outer,value,middle,count,bodyTrace,outerTrace⟩
  · exact head_bind source inventory inner next nonpure
      (ih fuel smaller control before inner after bodyPost known certificate fields bodyTrace)
  · have body := admit inner control before (.code (.pure value)) middle bodyPost known certificate fields bodyTrace
    have nextCertificate := continuation value middle body.current body.extension (body.result value rfl)
    have nextField := SourceCurrentAllocatedNativeCodeFields.fields_grows before.operations middle.operations
      (next value) (nextFields value) body.operations
    exact ih outer (by omega) (.code (next value)) middle remaining after post
      body.current nextCertificate nextField outerTrace

private theorem scoped_node_bind {A : Type} (bound fuel handle : Nat)
    (admit : ∀ count, Admits source inventory initial width count)
    (ih : ∀ count, count < bound → Scoped (width := width) (source := source) (inventory := inventory) (initial := initial) count)
    (smaller : fuel < bound) (request : NodeRequest Symbol Guard)
    (next : Value Symbol Guard → Code Symbol Guard A)
    (before after : Checked width) (remaining : Control A) (post : Machine Symbol Guard → A → Prop)
    (known : Current source inventory initial before)
    (certificate : Certified source inventory (.code (compileNode request)) before.native.machine
      (fun final value => Available final.heap value))
    (fields : Fields (.code (compileNode request)) before)
    (nextFields : ∀ value, CodeFields before.operations (next value))
    (running : before.native.nodes.cells handle = some ⟨request,.evaluating⟩)
    (continuation : ∀ value (current : Checked width), Current source inventory initial current →
      Extension before.native.machine current.native.machine → Available current.native.machine.heap value →
      Certified source inventory (.code (next value)) current.native.machine post)
    (trace : Steps fuel ((.code (compileNode request) : Control (Value Symbol Guard)).bind
      (fun value => .finishNode handle value (next value))) before remaining after) : Head source inventory remaining := by
  rcases SourceEqualityNativeDemandProtectedPrefix.node_cases fuel handle request next before after remaining
      known.good.native.shape running trace with
    ⟨inner,bodyTrace,nonpure,rfl⟩ |
      ⟨bodyFuel,frameFuel,value,middle,count,_,bodyTrace,owner,_,frame⟩
  · exact head_bind source inventory inner (fun value => .finishNode handle value (next value)) nonpure
      (ih fuel smaller _ before inner after _ known certificate fields bodyTrace)
  · have body := admit bodyFuel _ before (.code (.pure value)) middle _ known certificate fields bodyTrace
    have available := body.result value rfl
    have frameFields : CodeFields middle.operations (.finishNode handle value (next value)) :=
      SourceCurrentAllocatedNativeCodeFields.fields_grows before.operations middle.operations
        (next value) (nextFields value) body.operations
    rcases frame with ⟨zeroFrame,same,retained⟩ | ⟨rest,rfl,outerTrace⟩
    · subst frameFuel
      subst remaining
      trivial
    · let finished : Checked width := {middle with native := SourceRecursiveIntersectionThunks.finishNode handle value middle.native}
      have one : step (.code (.finishNode handle value (next value))) middle =
          .yielded (.code (next value)) finished := rfl
      have effects := SourceCurrentAllocatedRecursivePrefixState.yielded
        (.code (.finishNode handle value (next value))) (.code (next value)) middle finished body.current
        ⟨request,owner,available⟩ trivial frameFields one
      have output : Available finished.native.machine.heap value := effects.2.1.available value available
      have nextCertificate := continuation value finished effects.1 (body.extension.trans effects.2.1) output
      exact ih rest (by omega) (.code (next value)) finished remaining after post
        effects.1 nextCertificate effects.2.2.2.2 outerTrace

private theorem scoped_edge_bind {A : Type} (bound fuel handle : Nat)
    (admit : ∀ count, Admits source inventory initial width count)
    (ih : ∀ count, count < bound → Scoped (width := width) (source := source) (inventory := inventory) (initial := initial) count)
    (smaller : fuel < bound) (request : EdgeRequest Symbol Guard)
    (next : EdgeValue Symbol Guard → Code Symbol Guard A)
    (before after : Checked width) (remaining : Control A) (post : Machine Symbol Guard → A → Prop)
    (known : Current source inventory initial before)
    (certificate : Certified source inventory (.edgeBody request .pure) before.native.machine
      (fun final value => EdgeResident final.heap value))
    (fields : Fields (.edgeBody request .pure) before)
    (nextFields : ∀ value, CodeFields before.operations (next value))
    (running : before.native.edges.cells handle = some ⟨request,.evaluating⟩)
    (continuation : ∀ value (current : Checked width), Current source inventory initial current →
      Extension before.native.machine current.native.machine → EdgeResident current.native.machine.heap value →
      Certified source inventory (.code (next value)) current.native.machine post)
    (trace : Steps fuel ((.edgeBody request .pure : Control (EdgeValue Symbol Guard)).bind
      (fun value => .finishEdge handle value (next value))) before remaining after) : Head source inventory remaining := by
  rcases SourceEqualityNativeDemandProtectedPrefix.edge_cases fuel handle request next before after remaining
      known.good.native.shape running trace with
    ⟨inner,bodyTrace,nonpure,rfl⟩ |
      ⟨bodyFuel,frameFuel,value,middle,count,_,bodyTrace,owner,_,frame⟩
  · exact head_bind source inventory inner (fun value => .finishEdge handle value (next value)) nonpure
      (ih fuel smaller _ before inner after _ known certificate fields bodyTrace)
  · have body := admit bodyFuel _ before (.code (.pure value)) middle _ known certificate fields bodyTrace
    have resident := body.result value rfl
    have frameFields : CodeFields middle.operations (.finishEdge handle value (next value)) :=
      SourceCurrentAllocatedNativeCodeFields.fields_grows before.operations middle.operations
        (next value) (nextFields value) body.operations
    rcases frame with ⟨zeroFrame,same,retained⟩ | ⟨rest,rfl,outerTrace⟩
    · subst frameFuel
      subst remaining
      trivial
    · let finished : Checked width := {middle with native := SourceRecursiveIntersectionThunks.finishEdge handle value middle.native}
      have one : step (.code (.finishEdge handle value (next value))) middle =
          .yielded (.code (next value)) finished := rfl
      have effects := SourceCurrentAllocatedRecursivePrefixState.yielded
        (.code (.finishEdge handle value (next value))) (.code (next value)) middle finished body.current
        ⟨request,owner,resident⟩ trivial frameFields one
      have output : EdgeResident finished.native.machine.heap value :=
        InternedEdgeResidency.edge_grows _ _ effects.2.1.heap _ resident
      have nextCertificate := continuation value finished effects.1 (body.extension.trans effects.2.1) output
      exact ih rest (by omega) (.code (next value)) finished remaining after post
        effects.1 nextCertificate effects.2.2.2.2 outerTrace

variable {bits : Nat}

private theorem scopes (resources : SourceCurrentAllocatedRecursivePrefixAdmission.Resources bits source inventory initial) (fuel : Nat) :
    Scoped (width := bits + 2) (source := source) (inventory := inventory) (initial := initial) fuel := by
  have admit := SourceCurrentAllocatedRecursivePrefixAdmission.prefixes resources
  induction fuel using Nat.strongRecOn with
  | ind count ih =>
    intro A control before remaining after post known certificate fields trace
    have inputs := SourceCurrentAllocatedRecursivePrefixControl.inputs source inventory bits resources.facts initial
      control before post known certificate resources.valid resources.nodes resources.edges resources.room
    have admitted := SourceCurrentAllocatedRecursivePrefixControl.entered source inventory control before.native.machine post certificate
    cases count with
    | zero =>
      obtain ⟨rfl, rfl⟩ := steps_zero _ _ _ _ trace
      exact head_certified source inventory control before.native.machine post certificate
    | succ fuel =>
      obtain ⟨resume, middle, one, tail⟩ := steps_succ fuel _ _ _ _ trace
      have effects := SourceCurrentAllocatedRecursivePrefixState.yielded control resume before middle known inputs admitted fields one
      cases control with
      | edgeBody request next =>
        obtain ⟨body, pureBody, same⟩ := SourceEqualityNativeDemandBodyYield.yielded_unbind request next
          before middle resume one
        subst resume
        have data := SourceCurrentAllocatedRecursivePrefixControl.edge_data source inventory request next before.native.machine post certificate
        have bodyCertificate : Certified source inventory (.code body) middle.native.machine
            (fun final value => EdgeResident final.heap value) :=
          SourceCurrentAllocatedRecursivePrefixCode.body_certified source inventory resources.facts request data.1 data.2.1
            before middle body known.good.native.machine known.semantic data.2.2 pureBody
        have bodyFields := SourceCurrentAllocatedNativeFieldClosure.body_fields request .pure before middle (.code body)
          known.good.fields data.2.2 known.good.operations (fun _ => trivial) pureBody
        apply scoped_bind (fuel + 1) fuel admit ih (by omega)
          (.code body) next middle after remaining _ post effects.1 bodyCertificate bodyFields
          (fun value => SourceCurrentAllocatedNativeCodeFields.fields_grows before.operations middle.operations
            (next value) (fields.2 value) effects.2.2.2.1) ?_ tail
        intro value final current growth resident
        exact SourceCurrentAllocatedRecursivePrefixControl.edge_next source inventory request next before.native.machine post
          certificate value final.native.machine current.good.native.machine (effects.2.1.trans growth) current.semantic resident
      | code code =>
        cases code with
        | pure | fail => cases one
        | finishNode | finishEdge => cases certificate.safe
        | work job next =>
          obtain ⟨rfl, rfl⟩ := Outcome.yielded.inj one
          have nextCertificate := SourceCurrentAllocatedRecursivePrefixCode.work_next source inventory job next
            before.native.machine post certificate known.semantic _ _ rfl
          exact ih fuel (by omega) (.code (next (run job before.native.machine.heap).1)) _ remaining after post effects.1 nextCertificate.2.2.2 effects.2.2.2.2 tail
        | enter domain left right first second next =>
          obtain ⟨rfl, rfl⟩ := Outcome.yielded.inj one
          have nextCertificate := SourceCurrentAllocatedRecursivePrefixCode.enter_next source inventory domain left right first second next
            before.native.machine post certificate known.semantic
          exact ih fuel (by omega) (.code (next (SourceRecursiveIntersectionEnvironment.enter before.native.machine.domains domain.key left right first second).1)) _ remaining after post effects.1 nextCertificate.2.2.2 effects.2.2.2.2 tail
        | read name next =>
          obtain ⟨rfl, rfl⟩ := Outcome.yielded.inj one
          exact ih fuel (by omega) (.code (next (SourcePreparedSharedRows.read before.native.machine.heap name))) _ remaining after post effects.1
            (SourceCurrentAllocatedRecursivePrefixCode.read_next source inventory name next before.native.machine post certificate)
            effects.2.2.2.2 tail
        | optionalBinder pair value next =>
          cases actual : SourceRecursiveIntersectionMaybeMu.maybeMu pair value before.native.machine.heap with
          | pending key heap =>
            simp only [SourceEqualityNativeDemand.step, SourceRecursiveIntersectionNative.step, actual, lift] at one
            cases one
          | done result heap =>
            simp only [SourceEqualityNativeDemand.step, SourceRecursiveIntersectionNative.step, actual, lift] at one
            obtain ⟨rfl, rfl⟩ := Outcome.yielded.inj one
            have done : construction (SourceRecursiveIntersectionMaybeMu.maybeMu pair value before.native.machine.heap)
                before.native.machine = .done result {before.native.machine with heap := heap} := by rw [actual]; rfl
            have nextCertificate := SourceCurrentAllocatedRecursivePrefixCode.optionalBinder_next source inventory pair value next
              before.native.machine post certificate known.semantic _ _ done
            exact ih fuel (by omega) (.code (next result)) _ remaining after post effects.1 nextCertificate.2.2.2 effects.2.2.2.2 tail
        | node request next =>
          have data := SourceCurrentAllocatedRecursivePrefixCode.node_data source inventory request next before.native.machine post certificate
          have words := SourceCurrentAllocatedRecursivePrefixControl.words source inventory bits resources.facts initial
            (.code (.node request next)) before post known certificate resources.valid resources.nodes resources.edges resources.room
          obtain ⟨machine, operations, branches⟩ := SourceCurrentAllocatedRecursiveRequestStep.node_yielded request next
            before resume middle known.good.native data.1 words one
          have ready : NodeReady middle.native.machine request := by rw [machine]; exact data.1
          have bodyCertificate := SourceCurrentAllocatedRecursivePrefixCode.node_certified source inventory
            resources.facts resources.closed request data.2.1 data.2.2 middle.native.machine
            effects.1.good.native.machine effects.1.semantic ready effects.1.growth effects.1.history
          have bodyFields := SourceCurrentAllocatedNativeCodeFields.compileNode_fields middle.operations request
          have nextFields : ∀ value, CodeFields middle.operations (next value) := by rw [operations]; exact fields
          have continuation : ∀ value (final : Checked (bits + 2)), Current source inventory initial final →
              Extension middle.native.machine final.native.machine → Available final.native.machine.heap value →
              Certified source inventory (.code (next value)) final.native.machine post := by
            intro value final current growth available
            exact SourceCurrentAllocatedRecursivePrefixCode.node_next source inventory request next before.native.machine post
              certificate value final.native.machine current.good.native.machine (effects.2.1.trans growth) current.semantic available
          rcases branches with ⟨rfl, _⟩ | ⟨value, rfl, available⟩ | ⟨handle, rfl, running⟩
          · exact scoped_bind (fuel + 1) fuel admit ih (by omega)
              (.code (compileNode request)) next middle after remaining _ post effects.1 bodyCertificate bodyFields nextFields continuation tail
          · exact ih fuel (by omega) _ middle remaining after post effects.1
              (continuation value middle effects.1 (.refl _) available) (nextFields value) tail
          · exact scoped_node_bind (fuel + 1) fuel handle admit ih (by omega)
              request next middle after remaining post effects.1 bodyCertificate bodyFields nextFields running continuation tail
        | edge request next =>
          have data := SourceCurrentAllocatedRecursivePrefixCode.edge_data source inventory request next before.native.machine post certificate
          have words := SourceCurrentAllocatedRecursivePrefixControl.words source inventory bits resources.facts initial
            (.code (.edge request next)) before post known certificate resources.valid resources.nodes resources.edges resources.room
          obtain ⟨machine, operations, branches⟩ := SourceCurrentAllocatedRecursiveRequestStep.edge_yielded request next
            before resume middle known.good.native data.1 words one
          have ready : EdgeReady middle.native.machine request := by rw [machine]; exact data.1
          have bodyCertificate := SourceCurrentAllocatedRecursivePrefixControl.edge_body source inventory request
            middle.native.machine data.2.1 data.2.2 ready
          have bodyFields : Fields (.edgeBody request .pure) middle := ⟨ready, fun _ => trivial⟩
          have nextFields : ∀ value, CodeFields middle.operations (next value) := by rw [operations]; exact fields
          have continuation : ∀ value (final : Checked (bits + 2)), Current source inventory initial final →
              Extension middle.native.machine final.native.machine → EdgeResident final.native.machine.heap value →
              Certified source inventory (.code (next value)) final.native.machine post := by
            intro value final current growth resident
            exact SourceCurrentAllocatedRecursivePrefixCode.edge_next source inventory request next before.native.machine post
              certificate value final.native.machine current.good.native.machine (effects.2.1.trans growth) current.semantic resident
          rcases branches with ⟨value, rfl, resident⟩ | ⟨handle, rfl, running⟩
          · exact ih fuel (by omega) _ middle remaining after post effects.1
              (continuation value middle effects.1 (.refl _) resident) (nextFields value) tail
          · exact scoped_edge_bind (fuel + 1) fuel handle admit ih (by omega)
              request next middle after remaining post effects.1 bodyCertificate bodyFields nextFields running continuation tail

/-- An actual reached node instruction keeps its original fixed-source operands and binding scope. -/
theorem node_scope {A : Type}
    (resources : SourceCurrentAllocatedRecursivePrefixAdmission.Resources bits source inventory initial)
    (fuel : Nat) (control : Control A) (before after : Checked (bits + 2))
    (post : Machine Symbol Guard → A → Prop)
    (known : Current source inventory initial before)
    (certificate : Certified source inventory control before.native.machine post)
    (fields : Fields control before)
    (request : NodeRequest Symbol Guard) (next : Value Symbol Guard → Code Symbol Guard A)
    (actual : Steps fuel control before (.code (.node request next)) after) :
    NodeScope source request ∧ request.domain.key ∈ inventory :=
  scopes resources fuel control before (.code (.node request next)) after post known certificate fields actual

end MicroCFTA.SourceCurrentAllocatedRecursivePrefixScope

set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.proofs.threshold 254
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
#check @MicroCFTA.SourceCurrentAllocatedRecursivePrefixScope.node_scope
#print MicroCFTA.SourceCurrentAllocatedRecursivePrefixScope.node_scope
#print axioms MicroCFTA.SourceCurrentAllocatedRecursivePrefixScope.node_scope
