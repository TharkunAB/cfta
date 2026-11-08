import MicroCFTA.SourceCurrentNativeKeyAdmission
import MicroCFTA.SourceCurrentAllocatedRecursiveMassTrace

/-!
# Native word checks through a bounded raw prefix

Each actual instruction allocates at most one domain. Initial domain
headroom for the supplied fuel therefore bounds every reached domain.
Original source records bound operand keys. The source domain inventory
supplies compiler scope only. Its cardinality is not a capacity premise.
The statements include unfinished prefixes and all next-step outcomes.
They do not assert completion or a bound for an unbounded driver.
-/
namespace MicroCFTA.SourceCurrentAllocatedNativeFuelWordRanges
open Cache InternedConstructorTemplates InternedProbeProvenance InternedNestedFacts InternedEdgeResidency
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceEqualityNativeDemand SourceCurrentAllocatedRecursivePrefixState
open SourceCurrentAllocatedNativeFieldClosure (Fields)
open SourceCurrentAllocatedRecursivePrefixReceipt (Receipt)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Certified" => SourceCurrentAllocatedRecursivePrefixControl.Certified
local notation "CodeFields" => SourceCurrentAllocatedNativeCodeFields.Fields
local notation "DomainKey" => IntersectionFlatMemoKeyDomain.DomainKey
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
variable {A : Type} {width fuel : Nat}

/-- Raw prefixes bound domain allocation without prior word or physical checks. -/
theorem raw_domain_prefix {control next : Control A} {before after : Checked width}
    (actual : Steps fuel control before next after) :
    after.native.machine.domains.next ≤ before.native.machine.domains.next + fuel := by
  induction actual with
  | refl => omega
  | cons control before next middle remaining after count one rest ih =>
      have own := SourceCurrentAllocatedRecursiveMassTrace.domain_step_bound control before
      rw [one] at own
      change middle.native.machine.domains.next ≤ before.native.machine.domains.next + 1 at own
      omega

private structure Limits (bits : Nat) (source : InternedConstructorTemplates.State Symbol Guard)
    (inventory : List DomainKey) : Prop where
  facts : Facts source
  closed : SourceCurrentAllocatedRecursiveDomainCode.Closed source inventory
  nodes : source.nodes.next < 2 ^ bits
  edges : source.edges.next ≤ 2 ^ (bits + 2)

omit [DecidableEq Symbol] in
private theorem current_words {bits : Nat} {source : InternedConstructorTemplates.State Symbol Guard}
    {inventory : List DomainKey} {initial : Cache.State DomainKey}
    (limits : Limits bits source inventory) (control : Control A) (before : Checked (bits + 2))
    (post : Machine Symbol Guard → A → Prop) (current : Current source inventory initial before)
    (certificate : Certified source inventory control before.native.machine post)
    (room : before.native.machine.domains.next < 2 ^ (bits + 1)) :
    SourceCurrentAllocatedNativeRequestBounds.Words (bits + 2) control := by
  cases control with
  | edgeBody => trivial
  | code body =>
      cases body with
      | node request next =>
          have domainBound := SourceRecursiveIntersectionDomainAllocation.represented_identity_le
            current.good.native.machine.2 certificate.safe.1.1.represented
          exact fun key encoded => SourceRecursiveIntersectionSourceInventory.node_key_safe bits source limits.facts
            limits.nodes request certificate.domain.1 (by omega) key encoded
      | edge request next =>
          have domainBound := SourceRecursiveIntersectionDomainAllocation.represented_identity_le
            current.good.native.machine.2 certificate.safe.1.1.represented
          exact SourceRecursiveIntersectionSourceInventory.edge_key_safe bits source limits.facts
            limits.edges request certificate.domain.1 (by omega)
      | pure | fail | work | enter | read | optionalBinder | finishNode | finishEdge => trivial

private theorem current_inputs {bits : Nat} {source : InternedConstructorTemplates.State Symbol Guard}
    {inventory : List DomainKey} {initial : Cache.State DomainKey}
    (limits : Limits bits source inventory) (control : Control A) (before : Checked (bits + 2))
    (post : Machine Symbol Guard → A → Prop) (current : Current source inventory initial before)
    (certificate : Certified source inventory control before.native.machine post)
    (room : before.native.machine.domains.next < 2 ^ (bits + 1)) :
    SourceCurrentAllocatedNativePhysicalExecution.Inputs control before := by
  cases control with
  | edgeBody => trivial
  | code body =>
      exact SourceCurrentAllocatedRecursivePrefixCode.current_inputs source inventory body before post certificate
        (current_words limits (.code body) before post current certificate room)

variable {source : InternedConstructorTemplates.State Symbol Guard}
variable {inventory : List DomainKey} {initial : Cache.State DomainKey}

private def Admits (source : InternedConstructorTemplates.State Symbol Guard)
    (inventory : List DomainKey) (initial : Cache.State DomainKey) (width fuel : Nat) : Prop :=
  ∀ {A : Type} (control : Control A) (before : Checked width) (remaining : Control A) (after : Checked width)
    (post : Machine Symbol Guard → A → Prop), Current source inventory initial before →
    Certified source inventory control before.native.machine post → Fields control before →
    before.native.machine.domains.next + fuel < 2 ^ (width - 1) →
    Steps fuel control before remaining after → Receipt source inventory initial fuel control before remaining after post

/-- Smaller body and continuation prefixes compose at their exact actual return. -/
private theorem bounded_bind {A B : Type} (bound fuel : Nat)
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
    (room : before.native.machine.domains.next + fuel < 2 ^ (width - 1))
    (trace : Steps fuel (control.bind next) before remaining after) :
    Receipt source inventory initial fuel (control.bind next) before remaining after post := by
  rcases steps_bind_cases fuel control next before after remaining trace with
    ⟨inner, bodyTrace, nonpure, rfl⟩ | ⟨inner, outer, value, middle, count, bodyTrace, outerTrace⟩
  · exact SourceCurrentAllocatedRecursivePrefixReceipt.bind_inside next
      (ih fuel smaller control before inner after bodyPost known certificate fields room bodyTrace)
      nonpure nextFields post
  · have body := ih inner (by omega) control before (.code (.pure value)) middle bodyPost known certificate fields (by omega) bodyTrace
    have domainBound := raw_domain_prefix bodyTrace
    have nextCertificate := continuation value middle body.current body.extension (body.result value rfl)
    have nextField := SourceCurrentAllocatedNativeCodeFields.fields_grows before.operations middle.operations
      (next value) (nextFields value) body.operations
    have later := ih outer (by omega) (.code (next value)) middle remaining after post
      body.current nextCertificate nextField (by omega) outerTrace
    simpa only [count] using SourceCurrentAllocatedRecursivePrefixReceipt.join next value body later

/-- A captured node finish receives its physical post from a smaller actual body trace. -/
private theorem bounded_node_bind {A : Type} (bound fuel handle : Nat)
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
    (room : before.native.machine.domains.next + fuel < 2 ^ (width - 1))
    (trace : Steps fuel ((.code (compileNode request) : Control (Value Symbol Guard)).bind
      (fun value => .finishNode handle value (next value))) before remaining after) :
    Receipt source inventory initial fuel ((.code (compileNode request) : Control (Value Symbol Guard)).bind
      (fun value => .finishNode handle value (next value))) before remaining after post := by
  rcases SourceEqualityNativeDemandProtectedPrefix.node_cases fuel handle request next before after remaining
      known.good.native.shape running trace with
    ⟨inner, bodyTrace, nonpure, rfl⟩ |
      ⟨bodyFuel, frameFuel, value, middle, count, _, bodyTrace, owner, _, frame⟩
  · exact SourceCurrentAllocatedRecursivePrefixReceipt.bind_inside (fun value => .finishNode handle value (next value))
      (ih fuel smaller _ before inner after _ known certificate fields room bodyTrace)
      nonpure nextFields post
  · have body := ih bodyFuel (by omega) _ before (.code (.pure value)) middle _ known certificate fields (by omega) bodyTrace
    have domainBound := raw_domain_prefix bodyTrace
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
      have sameDomain : finished.native.machine.domains.next = middle.native.machine.domains.next := rfl
      have later := ih rest (by omega) (.code (next value)) finished remaining after post
        effects.1 nextCertificate effects.2.2.2.2 (by omega) outerTrace
      have frame := SourceCurrentAllocatedRecursivePrefixReceipt.before_step
        (.code (.finishNode handle value (next value))) (.code (next value)) middle finished body.current
        ⟨request, owner, available⟩ trivial frameFields one later
      simpa only [count] using SourceCurrentAllocatedRecursivePrefixReceipt.join
        (fun value => .finishNode handle value (next value)) value body frame

/-- A captured edge finish uses the actual checked body's physical resident return. -/
private theorem bounded_edge_bind {A : Type} (bound fuel handle : Nat)
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
    (room : before.native.machine.domains.next + fuel < 2 ^ (width - 1))
    (trace : Steps fuel ((.edgeBody request .pure : Control (EdgeValue Symbol Guard)).bind
      (fun value => .finishEdge handle value (next value))) before remaining after) :
    Receipt source inventory initial fuel ((.edgeBody request .pure : Control (EdgeValue Symbol Guard)).bind
      (fun value => .finishEdge handle value (next value))) before remaining after post := by
  rcases SourceEqualityNativeDemandProtectedPrefix.edge_cases fuel handle request next before after remaining
      known.good.native.shape running trace with
    ⟨inner, bodyTrace, nonpure, rfl⟩ |
      ⟨bodyFuel, frameFuel, value, middle, count, _, bodyTrace, owner, _, frame⟩
  · exact SourceCurrentAllocatedRecursivePrefixReceipt.bind_inside (fun value => .finishEdge handle value (next value))
      (ih fuel smaller _ before inner after _ known certificate fields room bodyTrace)
      nonpure nextFields post
  · have body := ih bodyFuel (by omega) _ before (.code (.pure value)) middle _ known certificate fields (by omega) bodyTrace
    have domainBound := raw_domain_prefix bodyTrace
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
      have sameDomain : finished.native.machine.domains.next = middle.native.machine.domains.next := rfl
      have later := ih rest (by omega) (.code (next value)) finished remaining after post
        effects.1 nextCertificate effects.2.2.2.2 (by omega) outerTrace
      have frame := SourceCurrentAllocatedRecursivePrefixReceipt.before_step
        (.code (.finishEdge handle value (next value))) (.code (next value)) middle finished body.current
        ⟨request, owner, resident⟩ trivial frameFields one later
      simpa only [count] using SourceCurrentAllocatedRecursivePrefixReceipt.join
        (fun value => .finishEdge handle value (next value)) value body frame


/-- Every actual recursive raw prefix derives its physical checks and current source facts. -/
private theorem prefixes {bits : Nat} (resources : Limits bits source inventory) (fuel : Nat) :
    Admits source inventory initial (bits + 2) fuel := by
  induction fuel using Nat.strongRecOn with
  | ind count ih =>
    intro A control before remaining after post known certificate fields room trace
    have currentRoom : before.native.machine.domains.next < 2 ^ (bits + 1) := by
      have reduced : before.native.machine.domains.next + count < 2 ^ (bits + 1) := by
        simpa only [show bits + 2 - 1 = bits + 1 from by omega] using room
      omega
    have inputs := current_inputs resources control before post known certificate currentRoom
    have admitted := SourceCurrentAllocatedRecursivePrefixControl.entered source inventory control before.native.machine post certificate
    cases count with
    | zero =>
      obtain ⟨rfl, rfl⟩ := steps_zero _ _ _ _ trace
      apply SourceCurrentAllocatedRecursivePrefixReceipt.zero _ before known inputs admitted fields
      intro value same
      subst control
      exact SourceCurrentAllocatedRecursivePrefixControl.pure_result source inventory value before.native.machine post certificate
    | succ fuel =>
      obtain ⟨resume, middle, one, tail⟩ := steps_succ fuel _ _ _ _ trace
      have middleRoom : middle.native.machine.domains.next + fuel < 2 ^ (bits + 2 - 1) := by
        have own := SourceCurrentAllocatedRecursiveMassTrace.domain_step_bound control before
        rw [one] at own
        change middle.native.machine.domains.next ≤ before.native.machine.domains.next + 1 at own
        omega
      have effects := SourceCurrentAllocatedRecursivePrefixState.yielded control resume before middle known inputs admitted fields one
      apply SourceCurrentAllocatedRecursivePrefixReceipt.before_step control resume before middle known inputs admitted fields one
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
        apply bounded_bind (fuel + 1) fuel ih (by omega)
          (.code body) next middle after remaining _ post effects.1 bodyCertificate bodyFields
          (fun value => SourceCurrentAllocatedNativeCodeFields.fields_grows before.operations middle.operations
            (next value) (fields.2 value) effects.2.2.2.1) ?_ middleRoom tail
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
          exact ih fuel (by omega) _ _ remaining after post effects.1 nextCertificate.2.2.2 effects.2.2.2.2 middleRoom tail
        | enter domain left right first second next =>
          obtain ⟨rfl, rfl⟩ := Outcome.yielded.inj one
          have nextCertificate := SourceCurrentAllocatedRecursivePrefixCode.enter_next source inventory domain left right first second next
            before.native.machine post certificate known.semantic
          exact ih fuel (by omega) _ _ remaining after post effects.1 nextCertificate.2.2.2 effects.2.2.2.2 middleRoom tail
        | read name next =>
          obtain ⟨rfl, rfl⟩ := Outcome.yielded.inj one
          exact ih fuel (by omega) _ _ remaining after post effects.1
            (SourceCurrentAllocatedRecursivePrefixCode.read_next source inventory name next before.native.machine post certificate)
            effects.2.2.2.2 middleRoom tail
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
            exact ih fuel (by omega) _ _ remaining after post effects.1 nextCertificate.2.2.2 effects.2.2.2.2 middleRoom tail
        | node request next =>
          have data := SourceCurrentAllocatedRecursivePrefixCode.node_data source inventory request next before.native.machine post certificate
          have words := current_words resources (.code (.node request next)) before post known certificate currentRoom
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
          · exact bounded_bind (fuel + 1) fuel ih (by omega)
              (.code (compileNode request)) next middle after remaining _ post effects.1 bodyCertificate bodyFields nextFields continuation middleRoom tail
          · exact ih fuel (by omega) _ middle remaining after post effects.1
              (continuation value middle effects.1 (.refl _) available) (nextFields value) middleRoom tail
          · exact bounded_node_bind (fuel + 1) fuel handle ih (by omega)
              request next middle after remaining post effects.1 bodyCertificate bodyFields nextFields running continuation middleRoom tail
        | edge request next =>
          have data := SourceCurrentAllocatedRecursivePrefixCode.edge_data source inventory request next before.native.machine post certificate
          have words := current_words resources (.code (.edge request next)) before post known certificate currentRoom
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
              (continuation value middle effects.1 (.refl _) resident) (nextFields value) middleRoom tail
          · exact bounded_edge_bind (fuel + 1) fuel handle ih (by omega)
              request next middle after remaining post effects.1 bodyCertificate bodyFields nextFields running continuation middleRoom tail



/-- Initial closed operands derive every reached physical check within domain fuel headroom. -/
theorem node_prefix (bits fuel : Nat) (before : Checked (bits + 2))
    (good : SourceCurrentAllocatedNativePhysicalCompletion.Good before)
    (semantic : SourceEqualityRequiredSemanticCache.SemanticReady before.native.machine.heap)
    (left right : Value Symbol Guard) (leftAvailable : Available before.native.machine.heap left)
    (rightAvailable : Available before.native.machine.heap right)
    (leftClosed : left.free = []) (rightClosed : right.free = [])
    (nodes : before.native.machine.heap.nodes.next < 2 ^ bits)
    (edges : before.native.machine.heap.edges.next ≤ 2 ^ (bits + 2))
    (room : before.native.machine.domains.next + fuel < 2 ^ (bits + 1))
    {count : Nat} {next : Control (Value Symbol Guard)} {after : Checked (bits + 2)}
    (within : count ≤ fuel)
    (actual : Steps count (.code (requestNode IntersectionEmptyDomain.emptyDomain left right)) before next after) :
    Receipt before.native.machine.heap
      (SourceRecursiveIntersectionSourceInventory.domains before.native.machine.heap)
      before.native.machine.domains count
      (.code (requestNode IntersectionEmptyDomain.emptyDomain left right)) before next after
      (fun final value => Available final.heap value) := by
  let source := before.native.machine.heap
  let inventory := SourceRecursiveIntersectionSourceInventory.domains source
  let request : NodeRequest Symbol Guard := ⟨IntersectionEmptyDomain.emptyDomain, left, right⟩
  have facts := good.native.machine.1
  have limits : Limits bits source inventory :=
    ⟨facts, SourceCurrentAllocatedRecursiveDomainCode.source_closed source facts, nodes, edges⟩
  have current := SourceCurrentAllocatedRecursivePrefixState.initial source inventory before good semantic rfl
  have leftOriginal := SourceRecursiveIntersectionOriginalOutput.closed_original left source facts.coherent leftAvailable leftClosed
  have rightOriginal := SourceRecursiveIntersectionOriginalOutput.closed_original right source facts.coherent rightAvailable rightClosed
  have scope := SourceRecursiveIntersectionCode.initial_scope source left right
    leftOriginal rightOriginal leftAvailable rightAvailable
  have certificate : Certified source inventory
      (.code (requestNode request.domain request.left request.right)) before.native.machine
      (fun final value => Available final.heap value) :=
    SourceCurrentAllocatedRecursivePrefixCode.request_node source inventory request before.native.machine
      ⟨empty_domain _, leftAvailable, rightAvailable⟩ scope (SourceRecursiveIntersectionSourceInventory.empty_mem source)
  exact prefixes limits count _ before next after _ current certificate (fun _ => trivial)
    (by simpa only [show bits + 2 - 1 = bits + 1 from by omega] using
      (show before.native.machine.domains.next + count < 2 ^ (bits + 1) from by omega)) actual

/-- Every next outcome retains physical facts, including failure and blocked outcomes. -/
theorem node_step (bits fuel : Nat) (before : Checked (bits + 2))
    (good : SourceCurrentAllocatedNativePhysicalCompletion.Good before)
    (semantic : SourceEqualityRequiredSemanticCache.SemanticReady before.native.machine.heap)
    (left right : Value Symbol Guard) (leftAvailable : Available before.native.machine.heap left)
    (rightAvailable : Available before.native.machine.heap right)
    (leftClosed : left.free = []) (rightClosed : right.free = [])
    (nodes : before.native.machine.heap.nodes.next < 2 ^ bits)
    (edges : before.native.machine.heap.edges.next ≤ 2 ^ (bits + 2))
    (room : before.native.machine.domains.next + fuel < 2 ^ (bits + 1))
    {count : Nat} {next : Control (Value Symbol Guard)} {after : Checked (bits + 2)}
    (within : count < fuel)
    (actual : Steps count (.code (requestNode IntersectionEmptyDomain.emptyDomain left right)) before next after) :
    SourceCurrentAllocatedNativePhysicalCompletion.Good (step next after).state ∧
      Extension after.native.machine (step next after).state.native.machine ∧
      SourceEqualityRequiredCache.Keeps after.native.machine.heap (step next after).state.native.machine.heap ∧
      SourceEqualityConstraintMemoAllocation.Grows after.operations (step next after).state.operations ∧
      SourceCurrentAllocatedNativeFieldClosure.OutcomeFields (step next after) ∧
      (step next after).state.native.machine.domains.next ≤ before.native.machine.domains.next + (count + 1) ∧
      (step next after).state.native.machine.domains.next < 2 ^ (bits + 1) := by
  have receipt := node_prefix bits fuel before good semantic left right leftAvailable rightAvailable leftClosed rightClosed
    nodes edges room (Nat.le_of_lt within) actual
  have effects := SourceCurrentAllocatedNativePhysicalCompletion.step_invariants next after receipt.current.good
    receipt.inputs receipt.fields
  have past := raw_domain_prefix actual
  have current := SourceCurrentAllocatedRecursiveMassTrace.domain_step_bound next after
  exact ⟨effects.1, effects.2.1, effects.2.2.1, effects.2.2.2.1, effects.2.2.2.2, by omega, by omega⟩

end MicroCFTA.SourceCurrentAllocatedNativeFuelWordRanges
