import MicroCFTA.SourceCurrentAllocatedNativeMuSource

/-!
# Local contextual laws for checked source node branches

Empty and repeated references have direct contextual laws. Swap and reset
transport a child law. Closed self reuse follows the original input
copy laws and actual coherent physical identity. No parent finish law or
completed native callback supplies these branch results.
-/
namespace MicroCFTA.SourceCurrentAllocatedNativeNodeBranches
open Language BinderLanguage Cache InternedBinderProtocol InternedConstructorTemplates InternedProbeProvenance
open InternedNestedFacts InternedNestedProvenance
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionInputView
open SourceCurrentAllocatedNativePairContexts SourceCurrentAllocatedNativeContextCache
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula

/-- The fixed input copy law derives physical readback for each closed original operand. -/
theorem original_closed_language (source : InternedConstructorTemplates.State Symbol Guard) (facts : Facts source)
    (holds : Guard → Term Symbol → Bool) (model : IntersectSchedule.InputMeaning (view source holds))
    (value : Value Symbol Guard) (original : Original value) (available : Available source value)
    (closed : value.free = []) (valid : model.valid (inputOf value))
    (output : InternedGuardedLanguage.Env Symbol) :
    InternedGuardedLanguage.meaning holds output value = IntersectSchedule.inputLanguage model.languages (inputOf value) := by
  have closedInput : IntersectSchedule.closed (view source holds) (inputOf value) = true := by
    rw [closed_readback source facts holds value original available, closed]
    rfl
  have copied := model.copy_exact (inputOf value) valid closedInput
    (SourceRecursiveIntersectionGuardedInput.internedEnv output)
  rw [copy_readback source facts holds value available _ (original.codec value)] at copied
  exact (SourceRecursiveIntersectionGuardedInput.original_meaning holds value original output).trans copied

/-- Ranked copy completeness gives actual closed operand meaning without a result-law premise. -/
theorem original_closed_rank (source : InternedConstructorTemplates.State Symbol Guard) (facts : Facts source)
    (holds : Guard → Term Symbol → Bool) (model : IntersectSchedule.InputMeaning (view source holds))
    (ranked : IntersectSchedule.RankedInput (view source holds) model.valid)
    (value : Value Symbol Guard) (original : Original value) (available : Available source value)
    (closed : value.free = []) (valid : model.valid (inputOf value)) (rank : Nat) (term : Term Symbol)
    (accepted : IntersectSchedule.inputAt ranked.languages (inputOf value) rank term)
    (output : InternedGuardedLanguage.Env Symbol) : InternedGuardedLanguage.meaning holds output value term := by
  have closedInput : IntersectSchedule.closed (view source holds) (inputOf value) = true := by
    rw [closed_readback source facts holds value original available, closed]
    rfl
  have copied := ranked.copy (inputOf value) valid closedInput rank term accepted
    (SourceRecursiveIntersectionGuardedInput.internedEnv output)
  rw [copy_readback source facts holds value available _ (original.codec value)] at copied
  rw [SourceRecursiveIntersectionGuardedInput.original_meaning holds value original output]
  exact copied

section Branches
variable (view : IntersectSchedule.View Symbol) (model : IntersectSchedule.InputMeaning view)
  (ranked : IntersectSchedule.RankedInput view model.valid) (holds : Guard → Term Symbol → Bool)

/-- A literal empty operand has no common term at any input rank. -/
theorem empty_law (request : NodeRequest Symbol Guard) (literal : request.left = .empty ∨ request.right = .empty) :
    NodeLaw view model ranked holds request .empty := by
  constructor
  · intro _ _ _ _ accepted
    simp only [InternedGuardedLanguage.meaning] at accepted
  · intro _ _ _ _ _ _ _ _ left right
    rcases literal with first | second
    · simp only [first, inputOf, Value.referenceOf, IntersectionFlatMemoKey.input, Option.getD,
        IntersectSchedule.inputAt, IntersectSchedule.inputLanguage] at left
    · simp only [second, inputOf, Value.referenceOf, IntersectionFlatMemoKey.input, Option.getD,
        IntersectSchedule.inputAt, IntersectSchedule.inputLanguage] at right

/-- Swapping transports the reversed request law and keeps the same source domain. -/
theorem swap_law (request : NodeRequest Symbol Guard) (value : Value Symbol Guard)
    (child : NodeLaw view model ranked holds ⟨request.domain, request.right, request.left⟩ value) :
    NodeLaw view model ranked holds request value := by
  constructor
  · intro inputs output sound term accepted
    have childInputs : NodeInputs view model ⟨request.domain, request.right, request.left⟩ :=
      ⟨inputs.2.1, inputs.1, inputs.2.2.2, inputs.2.2.1⟩
    have common := child.sound childInputs output sound term accepted
    exact ⟨common.2, common.1⟩
  · intro inputs bound output complete first second bounded term left right
    have childInputs : NodeInputs view model ⟨request.domain, request.right, request.left⟩ :=
      ⟨inputs.2.1, inputs.1, inputs.2.2.2, inputs.2.2.1⟩
    exact child.complete childInputs bound output complete second first (by omega) term right left

/-- The reset child needs no enclosing seen-pair assumptions at its empty domain. -/
theorem reset_law (request : NodeRequest Symbol Guard) (value : Value Symbol Guard)
    (child : NodeLaw view model ranked holds
      ⟨IntersectionEmptyDomain.emptyDomain, request.left, request.right⟩ value) :
    NodeLaw view model ranked holds request value := by
  constructor
  · intro inputs output _ term accepted
    exact child.sound inputs output (sound_empty_domain model.languages output) term accepted
  · intro inputs bound output _ first second bounded term left right
    exact child.complete inputs bound output (complete_empty_domain ranked.languages bound output)
      first second bounded term left right

/-- The actual sorted physical pair inherits the one-sided enclosing pair laws. -/
theorem repeated_law (request : NodeRequest Symbol Guard) (first second : Nat)
    (leftIdentity : SourceRecursiveIntersectionControl.identity request.left = some first)
    (rightIdentity : SourceRecursiveIntersectionControl.identity request.right = some second)
    (leftNonempty : inputOf request.left ≠ .empty) (rightNonempty : inputOf request.right ≠ .empty)
    (seen : SourceRecursiveIntersectionControl.pair first second ∈ request.domain.key.seen) :
    NodeLaw view model ranked holds request
      (SourceRecursiveIntersectionControl.repeatedValue (SourceRecursiveIntersectionControl.pair first second)) := by
  constructor
  · intro inputs output sound term accepted
    have pairEq := SourceRecursiveIntersectionSchedule.pair_encoded request.left request.right
      (inputOf request.left) (inputOf request.right) (inputs.1.codec request.left) (inputs.2.1.codec request.right)
      first second leftIdentity rightIdentity
    have common := repeated_reference_sound holds model.languages request.domain.key output sound _ seen term accepted
    rw [pairEq] at common
    exact (IntersectSchedule.pair_language model.languages _ _ leftNonempty rightNonempty term).mp common
  · intro inputs bound output complete one two bounded term left right
    have pairEq := SourceRecursiveIntersectionSchedule.pair_encoded request.left request.right
      (inputOf request.left) (inputOf request.right) (inputs.1.codec request.left) (inputs.2.1.codec request.right)
      first second leftIdentity rightIdentity
    apply repeated_reference_complete holds ranked.languages bound request.domain.key output complete _ seen term
    rw [pairEq]
    exact (IntersectSchedule.ranked_pair ranked.languages bound _ _ leftNonempty rightNonempty term).mpr
      ⟨one, two, bounded, left, right⟩
end Branches

private theorem member_left {R : A → B → Prop} {inputs : List A} {outputs : List B}
    (related : All₂ R inputs outputs) (input : A) (present : input ∈ inputs) :
    ∃ output ∈ outputs, R input output := by
  induction related with
  | nil => cases present
  | cons first rest ih =>
      rcases List.mem_cons.mp present with rfl | tail
      · exact ⟨_, List.mem_cons_self, first⟩
      · obtain ⟨value, inside, law⟩ := ih tail
        exact ⟨value, List.mem_cons_of_mem _ inside, law⟩

private theorem member_right {R : A → B → Prop} {inputs : List A} {outputs : List B}
    (related : All₂ R inputs outputs) (output : B) (present : output ∈ outputs) :
    ∃ input ∈ inputs, R input output := by
  induction related with
  | nil => cases present
  | cons first rest ih =>
      rcases List.mem_cons.mp present with rfl | tail
      · exact ⟨_, List.mem_cons_self, first⟩
      · obtain ⟨value, inside, law⟩ := ih tail
        exact ⟨value, List.mem_cons_of_mem _ inside, law⟩

/-- The original physical union supplies exactly the member list of the fixed input model. -/
theorem union_members (source : InternedConstructorTemplates.State Symbol Guard) (facts : Facts source)
    (holds : Guard → Term Symbol → Bool) (entry : Cache.Interned NodeKey)
    (members : List (Value Symbol Guard)) (depth : Nat) (free : List Reference)
    (available : Available source (.union entry members depth free)) :
    (view source holds).members entry.identity = members.map inputOf := by
  have selected := payload_readback source facts (.union entry members depth free) available (.union entry.identity) rfl
  simp only [view, selected]

/-- Actual union construction combines only the laws of its original ordered member requests. -/
theorem left_union_law [DecidableEq (EdgeKey Symbol Guard)]
    (source : InternedConstructorTemplates.State Symbol Guard) (sourceFacts : Facts source)
    (holds : Guard → Term Symbol → Bool) (model : IntersectSchedule.InputMeaning (view source holds))
    (ranked : IntersectSchedule.RankedInput (view source holds) model.valid)
    (domain : Cache.Interned IntersectionFlatMemoKeyDomain.DomainKey) (entry : Cache.Interned NodeKey)
    (members : List (Value Symbol Guard)) (depth : Nat) (free : List Reference) (right : Value Symbol Guard)
    (available : Available source (.union entry members depth free))
    (state : InternedConstructorTemplates.State Symbol Guard) (facts : Facts state)
    (values : List (Value Symbol Guard)) (resident : Values state values)
    (laws : All₂ (fun member value => NodeLaw (view source holds) model ranked holds ⟨domain, member, right⟩ value) members values) :
    NodeLaw (view source holds) model ranked holds ⟨domain, .union entry members depth free, right⟩
      (run (makeUnion values) state).1 := by
  have memberList := union_members source sourceFacts holds entry members depth free available
  have childInputs : ∀ (inputs : NodeInputs (view source holds) model ⟨domain, .union entry members depth free, right⟩)
      member, member ∈ members → NodeInputs (view source holds) model ⟨domain, member, right⟩ := by
    intro inputs member present
    have original : Original member := by
      cases inputs.1 with
      | union _ _ _ _ originals => exact originals member present
    have valid : model.valid (inputOf member) := by
      apply model.union_valid entry.identity inputs.2.2.1
      rw [memberList]
      exact List.mem_map.mpr ⟨member, present, rfl⟩
    exact ⟨original, inputs.2.1, valid, inputs.2.2.2⟩
  constructor
  · intro inputs output sound term accepted
    obtain ⟨value, present, accepted⟩ := (InternedGuardedLanguage.makeUnion_exact state facts holds output values resident term).mp accepted
    obtain ⟨member, inside, law⟩ := member_right laws value present
    have common := law.sound (childInputs inputs member inside) output sound term accepted
    constructor
    · apply (model.union_exact entry.identity inputs.2.2.1 term).mpr
      exact ⟨inputOf member, by rw [memberList]; exact List.mem_map.mpr ⟨member, inside, rfl⟩, common.1⟩
    · exact common.2
  · intro inputs bound output complete first second bounded term left rightAccepted
    obtain ⟨child, present, accepted⟩ := ranked.union entry.identity inputs.2.2.1 first term left
    rw [memberList] at present
    obtain ⟨member, inside, rfl⟩ := List.mem_map.mp present
    obtain ⟨value, present, law⟩ := member_left laws member inside
    apply (InternedGuardedLanguage.makeUnion_exact state facts holds output values resident term).mpr
    exact ⟨value, present, law.complete (childInputs inputs member inside) bound output complete first second bounded
      term accepted rightAccepted⟩

/-- A right union retains its original member order and uses the corresponding right-child laws. -/
theorem right_union_law [DecidableEq (EdgeKey Symbol Guard)]
    (source : InternedConstructorTemplates.State Symbol Guard) (sourceFacts : Facts source)
    (holds : Guard → Term Symbol → Bool) (model : IntersectSchedule.InputMeaning (view source holds))
    (ranked : IntersectSchedule.RankedInput (view source holds) model.valid)
    (domain : Cache.Interned IntersectionFlatMemoKeyDomain.DomainKey) (entry : Cache.Interned NodeKey)
    (members : List (Value Symbol Guard)) (depth : Nat) (free : List Reference) (left : Value Symbol Guard)
    (available : Available source (.union entry members depth free))
    (state : InternedConstructorTemplates.State Symbol Guard) (facts : Facts state)
    (values : List (Value Symbol Guard)) (resident : Values state values)
    (laws : All₂ (fun member value => NodeLaw (view source holds) model ranked holds ⟨domain, left, member⟩ value) members values) :
    NodeLaw (view source holds) model ranked holds ⟨domain, left, .union entry members depth free⟩
      (run (makeUnion values) state).1 := by
  apply swap_law (view source holds) model ranked holds
  apply left_union_law source sourceFacts holds model ranked domain entry members depth free left available state facts values resident
  exact laws.imp (fun member value law => swap_law (view source holds) model ranked holds ⟨domain, member, left⟩ value law)

/-- Coherent closed self reuse derives its contextual law from the independent original input model. -/
theorem self_law (source : InternedConstructorTemplates.State Symbol Guard) (facts : Facts source)
    (holds : Guard → Term Symbol → Bool) (model : IntersectSchedule.InputMeaning (view source holds))
    (ranked : IntersectSchedule.RankedInput (view source holds) model.valid)
    (request : NodeRequest Symbol Guard) (leftAvailable : Available source request.left)
    (rightAvailable : Available source request.right)
    (self : SourceRecursiveIntersectionControl.closedSelf request.left request.right = true) :
    NodeLaw (view source holds) model ranked holds request request.left := by
  have same := SourceRecursiveIntersectionControl.self_record source facts request.left request.right
    leftAvailable rightAvailable self
  have closed : request.left.free = [] := by
    simp only [SourceRecursiveIntersectionControl.closedSelf, Bool.and_eq_true] at self
    exact List.isEmpty_iff.mp self.2
  constructor
  · intro inputs output _ term accepted
    have original := original_closed_language source facts holds model request.left inputs.1 leftAvailable closed
      inputs.2.2.1 output
    have left := (iff_of_eq (congrFun original term)).mp accepted
    exact ⟨left, by rw [← same]; exact left⟩
  · intro inputs _ output _ first _ _ term left _
    exact original_closed_rank source facts holds model ranked request.left inputs.1 leftAvailable closed
      inputs.2.2.1 first term left output

end MicroCFTA.SourceCurrentAllocatedNativeNodeBranches
