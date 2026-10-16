import MicroCFTA.SourceRecursiveIntersectionScheduleGrowth
import MicroCFTA.SourceCurrentAllocatedNativeInputInventoryModels

/-!
# Exact input ranks through retained physical views

View agreement applies only on the old closed input domain. Recursive
references also need that domain's Mu closure. The finite input interface
supplies this closure. Each derivation retains its exact unfolding rank.
The lifted interface retains the old domain and representative function.
It does not admit newly allocated inputs.
-/
namespace MicroCFTA.SourceCurrentAllocatedNativeInputGrowthModels
open Language Binding BinderLanguage IntersectSchedule
open Cache InternedConstructorTemplates InternedProbeProvenance InternedNestedProvenance
open SourceRecursiveIntersectionInputView
variable {Symbol Guard : Type} {before after : View Symbol}

private theorem reverse_agreement {valid : Input → Prop} (same : ViewAgreement before after valid) :
    ViewAgreement after before valid where
  free := fun input known => (same.free input known).symm
  copy := fun input known => (same.copy input known).symm
  body := fun name known => (same.body name known).symm
  rows := fun name known => (same.rows name known).symm
  members := fun name known => (same.members name known).symm
  body_valid := by
    intro name known
    rw [same.body name known]
    exact same.body_valid name known
  child_valid := by
    intro name known row member child inside
    rw [same.rows name known] at member
    exact same.child_valid name known row member child inside
  member_valid := by
    intro name known child member
    rw [same.members name known] at member
    exact same.member_valid name known child member

private theorem forward (valid : Input → Prop)
    (references : ∀ name, valid (.ref name) → valid (.mu name))
    (same : ViewAgreement before after valid)
    {input : Input} {rank : Nat} {term : Term Symbol}
    (accepted : InputDerivation before input rank term) (known : valid input) :
    InputDerivation after input rank term := by
  revert known
  induction accepted using InputDerivation.rec
      (motive_2 := fun rank children terms _ =>
        (∀ child ∈ children, valid child) → InputForestDerivation after rank children terms) with
  | node row member terms children guard ih =>
      intro known
      exact .node row (by simpa only [same.rows _ known] using member) terms
        (ih (same.child_valid _ known row member)) guard
  | binder body less ih =>
      intro known
      have entered := ih (same.body_valid _ known)
      exact .binder (by simpa only [same.body _ known] using entered) less
  | reference body less ih =>
      intro known
      have original := references _ known
      have entered := ih (same.body_valid _ original)
      exact .reference (by simpa only [same.body _ original] using entered) less
  | union member body less ih =>
      intro known
      exact .union (by simpa only [same.members _ known] using member)
        (ih (same.member_valid _ known _ member)) less
  | nil => exact .nil
  | cons head bounded tail first rest =>
      rename_i known
      exact .cons (first (known _ List.mem_cons_self)) bounded
        (rest (fun child member => known child (List.mem_cons_of_mem _ member)))

/-- Both input views have the same finite derivations at each exact unfolding rank. -/
theorem derivation_exact (inputs : FiniteInput before) (same : ViewAgreement before after inputs.valid)
    (input : Input) (valid : inputs.valid input) (rank : Nat) (term : Term Symbol) :
    InputDerivation after input rank term ↔ InputDerivation before input rank term :=
  ⟨fun accepted => forward inputs.valid inputs.reference_valid (reverse_agreement same) accepted valid,
    fun accepted => forward inputs.valid inputs.reference_valid same accepted valid⟩

/-- Ordered input forests retain their exact shared bound on the old domain. -/
theorem forest_exact (inputs : FiniteInput before) (same : ViewAgreement before after inputs.valid)
    (rank : Nat) (children : List Input) (valid : ∀ child ∈ children, inputs.valid child)
    (terms : List (Term Symbol)) :
    InputForestDerivation after rank children terms ↔ InputForestDerivation before rank children terms := by
  revert valid
  induction children generalizing terms with
  | nil => intro _; constructor <;> intro accepted <;> cases accepted <;> exact .nil
  | cons child children ih =>
      intro valid
      constructor
      · intro accepted
        cases accepted with
        | cons head bounded tail =>
            exact .cons ((derivation_exact inputs same child (valid child List.mem_cons_self) _ _).mp head) bounded
              ((ih _ (fun value member => valid value (List.mem_cons_of_mem _ member))).mp tail)
      · intro accepted
        cases accepted with
        | cons head bounded tail =>
            exact .cons ((derivation_exact inputs same child (valid child List.mem_cons_self) _ _).mpr head) bounded
              ((ih _ (fun value member => valid value (List.mem_cons_of_mem _ member))).mpr tail)

/-- Actual view agreement lifts the old finite interface without widening its valid domain. -/
def lift (inputs : FiniteInput before) (same : ViewAgreement before after inputs.valid) : FiniteInput after where
  valid := inputs.valid
  representative := inputs.representative
  identity_exact := inputs.identity_exact
  body_valid := by
    intro name valid
    rw [same.body name valid]
    exact inputs.body_valid name valid
  reference_valid := inputs.reference_valid
  row_valid := by
    intro name valid row member child inside
    rw [same.rows name valid] at member
    exact inputs.row_valid name valid row member child inside
  union_valid := by
    intro name valid child member
    rw [same.members name valid] at member
    exact inputs.union_valid name valid child member
  copy_exact := by
    intro input valid isClosed environment
    have closedBefore : closed before input = true := by
      have equal : closed after input = closed before input := congrArg List.isEmpty (same.free input valid)
      exact equal.symm.trans isClosed
    rw [same.copy input valid, inputs.copy_exact input valid closedBefore environment]
    funext term
    exact propext (exists_congr fun rank => (derivation_exact inputs same input valid rank term).symm)

/-- The lifted input ranks retain every old valid input's exact derivation bound. -/
theorem lifted_rank (inputs : FiniteInput before) (same : ViewAgreement before after inputs.valid)
    (input : Input) (valid : inputs.valid input) (rank : Nat) (term : Term Symbol) :
    inputAt (finiteRanks after (lift inputs same)) input rank term ↔
      inputAt (finiteRanks before inputs) input rank term := by
  rw [finiteRanks_exact after (lift inputs same) input valid rank term,
    finiteRanks_exact before inputs input valid rank term]
  exact derivation_exact inputs same input valid rank term

/-- The lifted input language retains exactly the old accepted finite terms. -/
theorem lifted_language (inputs : FiniteInput before) (same : ViewAgreement before after inputs.valid)
    (input : Input) (valid : inputs.valid input) (term : Term Symbol) :
    inputLanguage (finiteLanguages after (lift inputs same)) input term ↔
      inputLanguage (finiteLanguages before inputs) input term := by
  rw [finiteLanguages_exact after (lift inputs same) input valid term,
    finiteLanguages_exact before inputs input valid term]
  exact exists_congr fun rank => derivation_exact inputs same input valid rank term

/-- Actual physical growth supplies view agreement on the old closed-root inventory. -/
theorem inventory_agreement (source target : InternedConstructorTemplates.State Symbol Guard)
    (sourceFacts : InternedNestedFacts.Facts source) (targetFacts : InternedNestedFacts.Facts target)
    (growth : Grows source target) (history : Extends source.nodes.issued target.nodes.issued)
    (holds : Guard → Term Symbol → Bool) (roots : List (Value Symbol Guard))
    (originals : ∀ root ∈ roots, Original root) (available : Values source roots)
    (closed : ∀ root ∈ roots, root.free = []) :
    ViewAgreement (view source holds) (view target holds)
      (SourceCurrentAllocatedNativeInputInventoryModels.finiteInput source sourceFacts holds roots originals available closed).valid := by
  have same := growthAgreement source target sourceFacts targetFacts growth history holds
  have original := SourceCurrentAllocatedNativeInputInventoryModels.reachable_original
    source sourceFacts holds roots originals available closed
  exact ⟨fun input valid => same.free input (original input valid),
    fun input valid => same.copy input (original input valid),
    fun name valid => same.body name (original _ valid),
    fun name valid => same.rows name (original _ valid),
    fun name valid => same.members name (original _ valid),
    (SourceCurrentAllocatedNativeInputInventoryModels.finiteInput source sourceFacts holds roots originals available closed).body_valid,
    (SourceCurrentAllocatedNativeInputInventoryModels.finiteInput source sourceFacts holds roots originals available closed).row_valid,
    (SourceCurrentAllocatedNativeInputInventoryModels.finiteInput source sourceFacts holds roots originals available closed).union_valid⟩

end MicroCFTA.SourceCurrentAllocatedNativeInputGrowthModels
