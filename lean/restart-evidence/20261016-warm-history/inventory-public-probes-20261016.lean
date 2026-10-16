import MicroCFTA.SourceCurrentAllocatedNativeInputInventoryModels

open MicroCFTA Cache Language InternedConstructorTemplates InternedProbeProvenance InternedNestedProvenance
open InternedNestedFacts IntersectSchedule SourceRecursiveIntersectionInputView
open SourceCurrentAllocatedNativeInputInventoryModels

#print axioms MicroCFTA.SourceCurrentAllocatedNativeInputInventoryModels.Reachable
#print axioms MicroCFTA.SourceCurrentAllocatedNativeInputInventoryModels.reachable_original
#print axioms MicroCFTA.SourceCurrentAllocatedNativeInputInventoryModels.reachable_inventory
#print axioms MicroCFTA.SourceCurrentAllocatedNativeInputInventoryModels.finiteInput
#print axioms MicroCFTA.SourceCurrentAllocatedNativeInputInventoryModels.root_valid
#print axioms MicroCFTA.SourceCurrentAllocatedNativeInputInventoryModels.root_language
#print axioms MicroCFTA.SourceCurrentAllocatedNativeInputInventoryModels.source_input_models

#check @MicroCFTA.SourceCurrentAllocatedNativeInputInventoryModels.Reachable
#check @MicroCFTA.SourceCurrentAllocatedNativeInputInventoryModels.reachable_original
#check @MicroCFTA.SourceCurrentAllocatedNativeInputInventoryModels.reachable_inventory
#check @MicroCFTA.SourceCurrentAllocatedNativeInputInventoryModels.finiteInput
#check @MicroCFTA.SourceCurrentAllocatedNativeInputInventoryModels.root_valid
#check @MicroCFTA.SourceCurrentAllocatedNativeInputInventoryModels.root_language
#check @MicroCFTA.SourceCurrentAllocatedNativeInputInventoryModels.source_input_models

namespace InventoryModelChecks
variable {Symbol Guard : Type}
local notation "ListedReachable" => SourceCurrentAllocatedNativeInputInventoryModels.Reachable

-- 1. The empty list introduces no valid input tag.
example (source : InternedConstructorTemplates.State Symbol Guard) (holds : Guard → Term Symbol → Bool)
    (input : Input) : ¬ ListedReachable source holds [] input := by
  rintro ⟨root, member, _⟩
  cases member

-- 2. Both listed operands use one fixed finite interface.
example (source : InternedConstructorTemplates.State Symbol Guard) (facts : Facts source)
    (holds : Guard → Term Symbol → Bool) (first second : Value Symbol Guard)
    (originals : ∀ root ∈ [first, second], Original root) (available : Values source [first, second])
    (closed : ∀ root ∈ [first, second], root.free = []) :
    let inputs := SourceCurrentAllocatedNativeInputInventoryModels.finiteInput source facts holds [first, second] originals available closed
    inputs.valid (inputOf first) ∧ inputs.valid (inputOf second) := by
  exact ⟨root_valid source facts holds _ originals available closed first (by simp),
    root_valid source facts holds _ originals available closed second (by simp)⟩

-- 3. Duplicate roots do not enlarge the reachable domain.
example (source : InternedConstructorTemplates.State Symbol Guard) (holds : Guard → Term Symbol → Bool)
    (roots : List (Value Symbol Guard)) (input : Input) :
    ListedReachable source holds (roots ++ roots) input ↔ ListedReachable source holds roots input := by
  constructor
  · rintro ⟨root, member, reached⟩
    exact ⟨root, (List.mem_append.mp member).elim id id, reached⟩
  · rintro ⟨root, member, reached⟩
    exact ⟨root, List.mem_append_left _ member, reached⟩

-- 4. Root order changes no reachable input tag.
example (source : InternedConstructorTemplates.State Symbol Guard) (holds : Guard → Term Symbol → Bool)
    (first second : List (Value Symbol Guard)) (order : first.Perm second) (input : Input) :
    ListedReachable source holds first input ↔ ListedReachable source holds second input := by
  constructor
  · rintro ⟨root, member, reached⟩
    exact ⟨root, order.mem_iff.mp member, reached⟩
  · rintro ⟨root, member, reached⟩
    exact ⟨root, order.mem_iff.mpr member, reached⟩

section Fixed
variable (source : InternedConstructorTemplates.State Symbol Guard) (facts : Facts source)
  (holds : Guard → Term Symbol → Bool) (roots : List (Value Symbol Guard))
  (originals : ∀ root ∈ roots, Original root) (available : Values source roots)
  (closed : ∀ root ∈ roots, root.free = [])
local notation "inputs" => SourceCurrentAllocatedNativeInputInventoryModels.finiteInput source facts holds roots originals available closed

-- 5. A reached recursive reference resolves inside the same fixed domain.
example (name : Nat) (known : (inputs).valid (.ref name)) : (inputs).valid (.mu name) :=
  (inputs).reference_valid name known

-- 6. A reached binder body remains in that domain.
example (name : Nat) (known : (inputs).valid (.mu name)) : (inputs).valid ((view source holds).body name) :=
  (inputs).body_valid name known

-- 7. Every child of every actual reached row remains in that domain.
example (name : Nat) (known : (inputs).valid (.node name)) (row : Row Symbol)
    (member : row ∈ (view source holds).rows name) (child : Input) (inside : child ∈ row.children) : (inputs).valid child :=
  (inputs).row_valid name known row member child inside

-- 8. Actual union membership retains the same domain.
example (name : Nat) (known : (inputs).valid (.union name)) (child : Input)
    (inside : child ∈ (view source holds).members name) : (inputs).valid child :=
  (inputs).union_valid name known child inside

-- 9. The representative is the actual shared physical lookup, not a root-specific choice.
example : (inputs).representative = SourceRecursiveIntersectionInputView.representative source := rfl

-- 10. Inventory inclusion derives the exact warm-history pair premises.
example (first second : Value Symbol Guard) (firstIn : first ∈ roots) (secondIn : second ∈ roots) :
    Original first ∧ Original second ∧ Available source first ∧ Available source second ∧
      first.free = [] ∧ second.free = [] ∧ (inputs).valid (inputOf first) ∧ (inputs).valid (inputOf second) :=
  ⟨originals first firstIn, originals second secondIn, available first firstIn, available second secondIn,
    closed first firstIn, closed second secondIn,
    root_valid source facts holds roots originals available closed first firstIn,
    root_valid source facts holds roots originals available closed second secondIn⟩

-- 11. Every valid input has an original physical record and lies in the finite issued carrier.
example (input : Input) (known : (inputs).valid input) : OriginalInput source input ∧ input ∈ inventory source :=
  ⟨reachable_original source facts holds roots originals available closed input known,
    reachable_inventory source facts holds roots originals available closed input known⟩

-- 12. Every listed root reads back through the exact same fixed semantic model.
example (root : Value Symbol Guard) (member : root ∈ roots)
    (ambient : InternedGuardedLanguage.Env Symbol) (term : Term Symbol) :
    InternedGuardedLanguage.meaning holds ambient root term ↔
      inputLanguage (finiteInputMeaning (view source holds) inputs).languages (inputOf root) term :=
  root_language source facts holds roots originals available closed root member ambient term

-- 13. All listed roots also use one common independent derivation-rank family.
example (root : Value Symbol Guard) (member : root ∈ roots) (rank : Nat) (term : Term Symbol) :
    inputAt (finiteRankedInput (view source holds) inputs).languages (inputOf root) rank term ↔
      InputDerivation (view source holds) (inputOf root) rank term :=
  finiteRanks_exact (view source holds) inputs (inputOf root)
    (root_valid source facts holds roots originals available closed root member) rank term

end Fixed

-- 14. A free original reference cannot pass the closed-root inventory contract.
example (roots : List (Value Symbol Guard)) (closed : ∀ root ∈ roots, root.free = []) (name : Nat) :
    Value.reference (.interned name) ∉ roots := by
  intro member
  have impossible := closed _ member
  simp [Value.free] at impossible

end InventoryModelChecks
