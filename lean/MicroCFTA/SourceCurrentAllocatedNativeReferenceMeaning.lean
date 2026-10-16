import MicroCFTA.SourceCurrentAllocatedNativeNodeRowsMeaning

/-!
# Contextual meaning of actual original reference resolution

Source bindings supply original available Mu payloads at their own names.
The fixed input model gives the same language and rank to a reference and
its Mu identity. Actual lookup and readback precede the exact child request.
Only that reached child supplies a local node law and physical effects.
This component does not derive recursive completion or a global finish plan.
-/
namespace MicroCFTA.SourceCurrentAllocatedNativeReferenceMeaning
open Cache Language BinderLanguage InternedConstructorTemplates InternedProbeProvenance
open InternedNestedFacts SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceRecursiveIntersectionInputView SourceEqualityNativeDemand
open SourceCurrentAllocatedNativePairContexts SourceCurrentAllocatedNativeContextCache
open InternedBinderProtocol
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula

/-- Original source bindings supply the actual complete available Mu payloads. -/
theorem bindings_available (source : InternedConstructorTemplates.State Symbol Guard)
    (domain : IntersectionFlatMemoKeyDomain.DomainKey) (bindings : OriginalBindings source domain) :
    SourceRecursiveIntersectionDomain.AvailableBindings source domain := by
  intro name member
  obtain ⟨value, original, available, complete⟩ := bindings name member
  cases original <;> simp only [Value.referenceOf, IntersectionFlatMemoKey.input, Option.some.injEq, reduceCtorEq] at complete <;> try contradiction
  case mu entry body depth ordinary original =>
    cases complete
    exact ⟨entry, body, depth, ordinary, rfl, available⟩

/-- Coherent identity readback transfers original scope to the exact selected binder. -/
theorem bound_original (source : InternedConstructorTemplates.State Symbol Guard) (facts : Facts source)
    (domain : IntersectionFlatMemoKeyDomain.DomainKey) (bindings : OriginalBindings source domain)
    (entry : Interned InternedBinderProtocol.NodeKey) (body depth ordinary : Value Symbol Guard)
    (available : Available source (.mu entry body depth ordinary))
    (member : entry.identity ∈ SourceRecursiveIntersectionDomain.names domain) : Original (.mu entry body depth ordinary) := by
  obtain ⟨value, original, stored, complete⟩ := bindings entry.identity member
  have references : value.referenceOf = (Value.mu entry body depth ordinary).referenceOf := by
    rw [IntersectionFlatMemoKey.input_reconstruct _ _ complete]
    rfl
  have same := InternedFreshProbeKeys.resident_reference_injective source facts.coherent value (.mu entry body depth ordinary)
    stored.resident available.resident references
  exact same ▸ original

/-- Typed source lookup and semantic lookup select the exact original available Mu record. -/
theorem bound_record (source : InternedConstructorTemplates.State Symbol Guard) (facts : Facts source)
    (domain : IntersectionFlatMemoKeyDomain.DomainKey) (typed : SourceRecursiveIntersectionDomain.Typed domain)
    (bindings : OriginalBindings source domain) (name : Nat) (member : name ∈ SourceRecursiveIntersectionDomain.names domain) :
    ∃ entry body depth ordinary, entry.identity = name ∧ Original (.mu entry body depth ordinary) ∧
      Available source (.mu entry body depth ordinary) ∧
      SourceRecursiveIntersectionDomain.keyLookup domain name = some (.mu name) ∧
      IntersectSchedule.lookup (SourceRecursiveIntersectionSchedule.domain domain) name = some (.mu name) ∧
      SourceRecursiveIntersectionDomain.lookup source domain name = some (.mu entry body depth ordinary) ∧
      SourcePreparedSharedRows.read source name = some (.mu entry body depth ordinary) := by
  have semantic : IntersectSchedule.lookup (SourceRecursiveIntersectionSchedule.domain domain) name = some (.mu name) := by
    rw [SourceRecursiveIntersectionSchedule.lookup_domain, ite_eq_left member]
  obtain ⟨entry, body, depth, ordinary, same, available, found⟩ :=
    SourceRecursiveIntersectionSchedule.lookup_record source facts domain (bindings_available source domain bindings) name semantic
  have named : entry.identity ∈ SourceRecursiveIntersectionDomain.names domain := same ▸ member
  refine ⟨entry, body, depth, ordinary, same, bound_original source facts domain bindings entry body depth ordinary available named,
    available, ?_, semantic, found, ?_⟩
  · rw [SourceRecursiveIntersectionDomain.keyLookup_typed domain typed name, ite_eq_left member]
  · rw [SourceRecursiveIntersectionDomain.lookup, ite_eq_left member] at found
    exact found

/-- Current reference validity derives the bound Mu's validity in the same original model. -/
theorem left_inputs (view : IntersectSchedule.View Symbol) (model : IntersectSchedule.InputMeaning view)
    (domain : Interned IntersectionFlatMemoKeyDomain.DomainKey) (name : Nat) (other : Value Symbol Guard)
    (entry : Interned InternedBinderProtocol.NodeKey) (body depth ordinary : Value Symbol Guard)
    (same : entry.identity = name) (original : Original (.mu entry body depth ordinary))
    (inputs : NodeInputs view model ⟨domain, .reference (.interned name), other⟩) :
    NodeInputs view model ⟨domain, .mu entry body depth ordinary, other⟩ := by
  subst name
  exact ⟨original, inputs.2.1, model.reference_valid entry.identity inputs.2.2.1, inputs.2.2.2⟩

/-- A right reference derives the same original bound scope without changing operand order. -/
theorem right_inputs (view : IntersectSchedule.View Symbol) (model : IntersectSchedule.InputMeaning view)
    (domain : Interned IntersectionFlatMemoKeyDomain.DomainKey) (name : Nat) (other : Value Symbol Guard)
    (entry : Interned InternedBinderProtocol.NodeKey) (body depth ordinary : Value Symbol Guard)
    (same : entry.identity = name) (original : Original (.mu entry body depth ordinary))
    (inputs : NodeInputs view model ⟨domain, other, .reference (.interned name)⟩) :
    NodeInputs view model ⟨domain, other, .mu entry body depth ordinary⟩ := by
  subst name
  exact ⟨inputs.1, original, inputs.2.2.1, model.reference_valid entry.identity inputs.2.2.2⟩

/-- A left bound reference and its original Mu share the independent input language and rank. -/
theorem left_law (view : IntersectSchedule.View Symbol) (model : IntersectSchedule.InputMeaning view)
    (ranked : IntersectSchedule.RankedInput view model.valid) (holds : Guard → Term Symbol → Bool)
    (domain : Interned IntersectionFlatMemoKeyDomain.DomainKey) (name : Nat) (other : Value Symbol Guard)
    (entry : Interned InternedBinderProtocol.NodeKey) (body depth ordinary : Value Symbol Guard) (result : Value Symbol Guard)
    (same : entry.identity = name) (original : Original (.mu entry body depth ordinary))
    (child : NodeLaw view model ranked holds ⟨domain, .mu entry body depth ordinary, other⟩ result) :
    NodeLaw view model ranked holds ⟨domain, .reference (.interned name), other⟩ result := by
  subst name
  constructor
  · intro inputs output sound term accepted
    exact child.sound (left_inputs view model domain _ other entry body depth ordinary rfl original inputs) output sound term accepted
  · intro inputs bound output complete first second bounded term left right
    exact child.complete (left_inputs view model domain _ other entry body depth ordinary rfl original inputs)
      bound output complete first second bounded term left right

/-- A right bound reference transports the exact right-child law without swapping the source request. -/
theorem right_law (view : IntersectSchedule.View Symbol) (model : IntersectSchedule.InputMeaning view)
    (ranked : IntersectSchedule.RankedInput view model.valid) (holds : Guard → Term Symbol → Bool)
    (domain : Interned IntersectionFlatMemoKeyDomain.DomainKey) (name : Nat) (other : Value Symbol Guard)
    (entry : Interned InternedBinderProtocol.NodeKey) (body depth ordinary : Value Symbol Guard) (result : Value Symbol Guard)
    (same : entry.identity = name) (original : Original (.mu entry body depth ordinary))
    (child : NodeLaw view model ranked holds ⟨domain, other, .mu entry body depth ordinary⟩ result) :
    NodeLaw view model ranked holds ⟨domain, other, .reference (.interned name)⟩ result := by
  subst name
  constructor
  · intro inputs output sound term accepted
    exact child.sound (right_inputs view model domain _ other entry body depth ordinary rfl original inputs) output sound term accepted
  · intro inputs bound output complete first second bounded term left right
    exact child.complete (right_inputs view model domain _ other entry body depth ordinary rfl original inputs)
      bound output complete first second bounded term left right

/-- Actual available binder readback precedes the next request and leaves the full state unchanged. -/
theorem reference_trace [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (domain : Interned IntersectionFlatMemoKeyDomain.DomainKey) (name : Nat) (other : Value Symbol Guard) (left : Bool)
    (entry : Interned InternedBinderProtocol.NodeKey) (body depth ordinary : Value Symbol Guard)
    (before after : SourceEqualityNativeDemand.State width) (result : Value Symbol Guard) (fuel : Nat)
    (same : entry.identity = name) (member : name ∈ SourceRecursiveIntersectionDomain.names domain.key)
    (ready : SourceEqualityRequiredCache.Ready before.native.machine.heap)
    (available : Available before.native.machine.heap (.mu entry body depth ordinary))
    (called : Steps fuel (.code (if left then requestNode domain (.mu entry body depth ordinary) other
      else requestNode domain other (.mu entry body depth ordinary))) before (.code (.pure result)) after) :
    Steps (fuel + 1) (.code (compileReference domain name other left)) before (.code (.pure result)) after := by
  have found := SourcePreparedSharedRows.read_identity before.native.machine.heap ready.semantic.1.normal.facts
    (.mu entry body depth ordinary) available name (by simpa only [SourcePreparedSharedRows.reference] using congrArg some same)
  apply Steps.cons _ _ _ _ _ _ fuel ?_ called
  cases left <;>
    simp only [compileReference, ite_eq_left member, SourceEqualityNativeDemand.step, SourceRecursiveIntersectionNative.step,
      found, SourceEqualityNativeDemand.lift]

/-- The selected left reference branch runs the actual read before its exact child trace. -/
theorem left_node_trace [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (domain : Interned IntersectionFlatMemoKeyDomain.DomainKey) (name : Nat) (other : Value Symbol Guard)
    (entry : Interned InternedBinderProtocol.NodeKey) (body depth ordinary : Value Symbol Guard)
    (before after : SourceEqualityNativeDemand.State width) (result : Value Symbol Guard) (fuel : Nat)
    (selected : SourceRecursiveIntersectionControl.decision domain.key (.reference (.interned name)) other = .leftReference)
    (same : entry.identity = name) (member : name ∈ SourceRecursiveIntersectionDomain.names domain.key)
    (ready : SourceEqualityRequiredCache.Ready before.native.machine.heap)
    (available : Available before.native.machine.heap (.mu entry body depth ordinary))
    (called : Steps fuel (.code (requestNode domain (.mu entry body depth ordinary) other)) before (.code (.pure result)) after) :
    Steps (fuel + 1) (.code (compileNode ⟨domain, .reference (.interned name), other⟩)) before (.code (.pure result)) after := by
  simpa only [compileNode, selected] using
    reference_trace domain name other true entry body depth ordinary before after result fuel same member ready available called

/-- The selected right reference branch retains the actual read and original operand order. -/
theorem right_node_trace [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (domain : Interned IntersectionFlatMemoKeyDomain.DomainKey) (name : Nat) (other : Value Symbol Guard)
    (entry : Interned InternedBinderProtocol.NodeKey) (body depth ordinary : Value Symbol Guard)
    (before after : SourceEqualityNativeDemand.State width) (result : Value Symbol Guard) (fuel : Nat)
    (selected : SourceRecursiveIntersectionControl.decision domain.key other (.reference (.interned name)) = .rightReference)
    (same : entry.identity = name) (member : name ∈ SourceRecursiveIntersectionDomain.names domain.key)
    (ready : SourceEqualityRequiredCache.Ready before.native.machine.heap)
    (available : Available before.native.machine.heap (.mu entry body depth ordinary))
    (called : Steps fuel (.code (requestNode domain other (.mu entry body depth ordinary))) before (.code (.pure result)) after) :
    Steps (fuel + 1) (.code (compileNode ⟨domain, other, .reference (.interned name)⟩)) before (.code (.pure result)) after := by
  simpa only [compileNode, selected] using
    reference_trace domain name other false entry body depth ordinary before after result fuel same member ready available called

/-- Left reference execution derives original scope and readback from actual retained source bindings. -/
theorem left_body [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (source : InternedConstructorTemplates.State Symbol Guard) (sourceFacts : Facts source)
    (holds : Guard → Term Symbol → Bool) (model : IntersectSchedule.InputMeaning (view source holds))
    (ranked : IntersectSchedule.RankedInput (view source holds) model.valid)
    (domain : Interned IntersectionFlatMemoKeyDomain.DomainKey) (bindings : OriginalBindings source domain.key)
    (name : Nat) (other : Value Symbol Guard) (entry : Interned InternedBinderProtocol.NodeKey) (body depth ordinary : Value Symbol Guard)
    (same : entry.identity = name) (member : name ∈ SourceRecursiveIntersectionDomain.names domain.key)
    (sourceAvailable : Available source (.mu entry body depth ordinary))
    (before after : SourceEqualityNativeDemand.State width) (result : Value Symbol Guard) (fuel : Nat)
    (retained : SourceEqualityRequiredCache.Keeps source before.native.machine.heap)
    (called : Steps fuel (.code (requestNode domain (.mu entry body depth ordinary) other)) before (.code (.pure result)) after)
    (keeps : SourceEqualityRequiredCache.Keeps before.native.machine.heap after.native.machine.heap)
    (available : Available after.native.machine.heap result)
    (law : NodeLaw (view source holds) model ranked holds ⟨domain, .mu entry body depth ordinary, other⟩ result) :
    execute (fuel + 2) (.code (compileReference domain name other true)) before = .done result after ∧
      NodeLaw (view source holds) model ranked holds ⟨domain, .reference (.interned name), other⟩ result ∧
      SourceEqualityRequiredCache.Keeps before.native.machine.heap after.native.machine.heap ∧ Available after.native.machine.heap result := by
  have original := bound_original source sourceFacts domain.key bindings entry body depth ordinary sourceAvailable (same ▸ member)
  exact ⟨trace_done (fuel + 1) _ before after result
    (reference_trace domain name other true entry body depth ordinary before after result fuel same member retained.ready
      (retained.available _ sourceAvailable) called),
    left_law (view source holds) model ranked holds domain name other entry body depth ordinary result same original law, keeps, available⟩

/-- Right reference execution preserves source operand order and uses the exact returned child state. -/
theorem right_body [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (source : InternedConstructorTemplates.State Symbol Guard) (sourceFacts : Facts source)
    (holds : Guard → Term Symbol → Bool) (model : IntersectSchedule.InputMeaning (view source holds))
    (ranked : IntersectSchedule.RankedInput (view source holds) model.valid)
    (domain : Interned IntersectionFlatMemoKeyDomain.DomainKey) (bindings : OriginalBindings source domain.key)
    (name : Nat) (other : Value Symbol Guard) (entry : Interned InternedBinderProtocol.NodeKey) (body depth ordinary : Value Symbol Guard)
    (same : entry.identity = name) (member : name ∈ SourceRecursiveIntersectionDomain.names domain.key)
    (sourceAvailable : Available source (.mu entry body depth ordinary))
    (before after : SourceEqualityNativeDemand.State width) (result : Value Symbol Guard) (fuel : Nat)
    (retained : SourceEqualityRequiredCache.Keeps source before.native.machine.heap)
    (called : Steps fuel (.code (requestNode domain other (.mu entry body depth ordinary))) before (.code (.pure result)) after)
    (keeps : SourceEqualityRequiredCache.Keeps before.native.machine.heap after.native.machine.heap)
    (available : Available after.native.machine.heap result)
    (law : NodeLaw (view source holds) model ranked holds ⟨domain, other, .mu entry body depth ordinary⟩ result) :
    execute (fuel + 2) (.code (compileReference domain name other false)) before = .done result after ∧
      NodeLaw (view source holds) model ranked holds ⟨domain, other, .reference (.interned name)⟩ result ∧
      SourceEqualityRequiredCache.Keeps before.native.machine.heap after.native.machine.heap ∧ Available after.native.machine.heap result := by
  have original := bound_original source sourceFacts domain.key bindings entry body depth ordinary sourceAvailable (same ▸ member)
  exact ⟨trace_done (fuel + 1) _ before after result
    (reference_trace domain name other false entry body depth ordinary before after result fuel same member retained.ready
      (retained.available _ sourceAvailable) called),
    right_law (view source holds) model ranked holds domain name other entry body depth ordinary result same original law, keeps, available⟩

end MicroCFTA.SourceCurrentAllocatedNativeReferenceMeaning
