import MicroCFTA.SourceCurrentAllocatedNativeReferenceMeaning
open MicroCFTA Cache Language BinderLanguage InternedBinderProtocol
open InternedConstructorTemplates InternedProbeProvenance SourceRecursiveIntersectionCode
open SourceRecursiveIntersectionThunks SourceEqualityNativeDemand SourceRecursiveIntersectionInputView
open SourceCurrentAllocatedNativeContextCache SourceCurrentAllocatedNativeReferenceMeaning
#print axioms MicroCFTA.SourceCurrentAllocatedNativeReferenceMeaning.bindings_available
#print axioms MicroCFTA.SourceCurrentAllocatedNativeReferenceMeaning.bound_original
#print axioms MicroCFTA.SourceCurrentAllocatedNativeReferenceMeaning.bound_record
#print axioms MicroCFTA.SourceCurrentAllocatedNativeReferenceMeaning.left_inputs
#print axioms MicroCFTA.SourceCurrentAllocatedNativeReferenceMeaning.right_inputs
#print axioms MicroCFTA.SourceCurrentAllocatedNativeReferenceMeaning.left_law
#print axioms MicroCFTA.SourceCurrentAllocatedNativeReferenceMeaning.right_law
#print axioms MicroCFTA.SourceCurrentAllocatedNativeReferenceMeaning.reference_trace
#print axioms MicroCFTA.SourceCurrentAllocatedNativeReferenceMeaning.left_node_trace
#print axioms MicroCFTA.SourceCurrentAllocatedNativeReferenceMeaning.right_node_trace
#print axioms MicroCFTA.SourceCurrentAllocatedNativeReferenceMeaning.left_body
#print axioms MicroCFTA.SourceCurrentAllocatedNativeReferenceMeaning.right_body
#check @MicroCFTA.SourceCurrentAllocatedNativeReferenceMeaning.bindings_available
#check @MicroCFTA.SourceCurrentAllocatedNativeReferenceMeaning.bound_original
#check @MicroCFTA.SourceCurrentAllocatedNativeReferenceMeaning.bound_record
#check @MicroCFTA.SourceCurrentAllocatedNativeReferenceMeaning.left_inputs
#check @MicroCFTA.SourceCurrentAllocatedNativeReferenceMeaning.right_inputs
#check @MicroCFTA.SourceCurrentAllocatedNativeReferenceMeaning.left_law
#check @MicroCFTA.SourceCurrentAllocatedNativeReferenceMeaning.right_law
#check @MicroCFTA.SourceCurrentAllocatedNativeReferenceMeaning.reference_trace
#check @MicroCFTA.SourceCurrentAllocatedNativeReferenceMeaning.left_node_trace
#check @MicroCFTA.SourceCurrentAllocatedNativeReferenceMeaning.right_node_trace
#check @MicroCFTA.SourceCurrentAllocatedNativeReferenceMeaning.left_body
#check @MicroCFTA.SourceCurrentAllocatedNativeReferenceMeaning.right_body

namespace ReferenceChecks
noncomputable section
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local instance : DecidableEq Symbol := Classical.typeDecidableEq _
local instance : DecidableEq (EdgeKey Symbol Guard) := Classical.typeDecidableEq _

-- 1. Reference and Mu language identity is independent of result semantics.
example (languages : Nat → Lang Symbol) (entry : Interned InternedBinderProtocol.NodeKey)
    (body depth ordinary : Value Symbol Guard) :
    IntersectSchedule.inputLanguage languages (inputOf (.reference (.interned entry.identity) : Value Symbol Guard)) =
      IntersectSchedule.inputLanguage languages (inputOf (.mu entry body depth ordinary)) := rfl

-- 2. The same identity preserves each original finite rank.
example (ranks : Nat → Nat → Lang Symbol) (entry : Interned InternedBinderProtocol.NodeKey)
    (body depth ordinary : Value Symbol Guard) (rank : Nat) :
    IntersectSchedule.inputAt ranks (inputOf (.reference (.interned entry.identity) : Value Symbol Guard)) rank =
      IntersectSchedule.inputAt ranks (inputOf (.mu entry body depth ordinary)) rank := rfl

-- 3. A valid original reference derives its bound Mu's validity.
example (view : IntersectSchedule.View Symbol) (model : IntersectSchedule.InputMeaning view)
    (domain : Interned IntersectionFlatMemoKeyDomain.DomainKey) (other : Value Symbol Guard)
    (entry : Interned InternedBinderProtocol.NodeKey) (body depth ordinary : Value Symbol Guard)
    (original : Original (.mu entry body depth ordinary))
    (inputs : NodeInputs view model ⟨domain, .reference (.interned entry.identity), other⟩) :
    model.valid (inputOf (.mu entry body depth ordinary)) :=
  (left_inputs view model domain entry.identity other entry body depth ordinary rfl original inputs).2.2.1

-- 4. Empty original domains need no supplied binder payload.
example (source : InternedConstructorTemplates.State Symbol Guard) :
    SourceRecursiveIntersectionDomain.AvailableBindings source IntersectionEmptyDomain.emptyDomain.key :=
  bindings_available source _ (by intro name member; cases member)

-- 5. Typed actual lookup derives raw readback, original scope, and exact identity.
example (source : InternedConstructorTemplates.State Symbol Guard) (facts : InternedNestedFacts.Facts source)
    (domain : IntersectionFlatMemoKeyDomain.DomainKey) (typed : SourceRecursiveIntersectionDomain.Typed domain)
    (bindings : OriginalBindings source domain) (name : Nat)
    (member : name ∈ SourceRecursiveIntersectionDomain.names domain) :
    ∃ entry body depth ordinary, entry.identity = name ∧ Original (.mu entry body depth ordinary) ∧
      Available source (.mu entry body depth ordinary) ∧
      SourcePreparedSharedRows.read source name = some (.mu entry body depth ordinary) := by
  obtain ⟨entry, body, depth, ordinary, same, original, available, _, _, _, readback⟩ :=
    bound_record source facts domain typed bindings name member
  exact ⟨entry, body, depth, ordinary, same, original, available, readback⟩

-- 6. A missing binder remains the literal source diagnostic before a read or child call.
example (domain : Interned IntersectionFlatMemoKeyDomain.DomainKey) (name : Nat) (other : Value Symbol Guard)
    (side : Bool) (absent : name ∉ SourceRecursiveIntersectionDomain.names domain.key) :
    compileReference domain name other side = .fail (.missingBinder name) := by
  simp only [compileReference, ite_eq_right absent]

-- 7. The actual left source read preserves the entire reached state before its child.
example (domain : Interned IntersectionFlatMemoKeyDomain.DomainKey)
    (entry : Interned InternedBinderProtocol.NodeKey) (body depth ordinary other : Value Symbol Guard)
    (state : SourceEqualityNativeDemand.State 8)
    (member : entry.identity ∈ SourceRecursiveIntersectionDomain.names domain.key)
    (ready : SourceEqualityRequiredCache.Ready state.native.machine.heap)
    (available : Available state.native.machine.heap (.mu entry body depth ordinary)) :
    step (.code (compileReference domain entry.identity other true)) state =
      .yielded (.code (requestNode domain (.mu entry body depth ordinary) other)) state := by
  have readback := SourcePreparedSharedRows.read_identity state.native.machine.heap ready.semantic.1.normal.facts
    (.mu entry body depth ordinary) available entry.identity rfl
  simp only [compileReference, ite_eq_left member, SourceEqualityNativeDemand.step,
    SourceRecursiveIntersectionNative.step, readback, SourceEqualityNativeDemand.lift] <;> rfl

-- 8. The actual right read keeps the original operand order and entire state.
example (domain : Interned IntersectionFlatMemoKeyDomain.DomainKey)
    (entry : Interned InternedBinderProtocol.NodeKey) (body depth ordinary other : Value Symbol Guard)
    (state : SourceEqualityNativeDemand.State 8)
    (member : entry.identity ∈ SourceRecursiveIntersectionDomain.names domain.key)
    (ready : SourceEqualityRequiredCache.Ready state.native.machine.heap)
    (available : Available state.native.machine.heap (.mu entry body depth ordinary)) :
    step (.code (compileReference domain entry.identity other false)) state =
      .yielded (.code (requestNode domain other (.mu entry body depth ordinary))) state := by
  have readback := SourcePreparedSharedRows.read_identity state.native.machine.heap ready.semantic.1.normal.facts
    (.mu entry body depth ordinary) available entry.identity rfl
  simp only [compileReference, ite_eq_left member, SourceEqualityNativeDemand.step,
    SourceRecursiveIntersectionNative.step, readback, SourceEqualityNativeDemand.lift] <;> rfl

-- 9. Left meaning transport consumes only the resolved child's local law.
example (view : IntersectSchedule.View Symbol) (model : IntersectSchedule.InputMeaning view)
    (ranked : IntersectSchedule.RankedInput view model.valid) (holds : Guard → Term Symbol → Bool)
    (domain : Interned IntersectionFlatMemoKeyDomain.DomainKey)
    (entry : Interned InternedBinderProtocol.NodeKey) (body depth ordinary other result : Value Symbol Guard)
    (original : Original (.mu entry body depth ordinary))
    (child : NodeLaw view model ranked holds ⟨domain, .mu entry body depth ordinary, other⟩ result) :
    NodeLaw view model ranked holds ⟨domain, .reference (.interned entry.identity), other⟩ result :=
  left_law view model ranked holds domain entry.identity other entry body depth ordinary result rfl original child

-- 10. Right meaning transport does not swap the actual source child request.
example (view : IntersectSchedule.View Symbol) (model : IntersectSchedule.InputMeaning view)
    (ranked : IntersectSchedule.RankedInput view model.valid) (holds : Guard → Term Symbol → Bool)
    (domain : Interned IntersectionFlatMemoKeyDomain.DomainKey)
    (entry : Interned InternedBinderProtocol.NodeKey) (body depth ordinary other result : Value Symbol Guard)
    (original : Original (.mu entry body depth ordinary))
    (child : NodeLaw view model ranked holds ⟨domain, other, .mu entry body depth ordinary⟩ result) :
    NodeLaw view model ranked holds ⟨domain, other, .reference (.interned entry.identity)⟩ result :=
  right_law view model ranked holds domain entry.identity other entry body depth ordinary result rfl original child
end
end ReferenceChecks
