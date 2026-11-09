import MicroCFTA.SourcePruningEnumerationPolicyOrigins

/-!
# Original callback policies for the actual catalog branch

An empty catalog bypasses the template oracle.
It needs no encoding condition on arbitrary Type subtrees.
A nonempty catalog retains the existing original subtree policies.
These laws do not derive template avoidance from raw source acceptance.
-/
namespace MicroCFTA.SourcePruningTemplates
open Language
local notation "Symbol" => SourcePruningTemplates.Symbol

/-- The empty catalog needs no source policy; other catalogs retain the original policy. -/
def CallbackOriginPolicies (templates : List (Template.Pattern Symbol))
    (whole : Term Symbol) : Prop :=
  templates = [] ∨ OriginPolicies templates whole

/-- Every complete term satisfies the policy when the actual catalog is empty. -/
theorem CallbackOriginPolicies.empty (whole : Term Symbol) :
    CallbackOriginPolicies [] whole :=
  .inl rfl

/-- An actual structural subtree inherits the callback policy. -/
theorem CallbackOriginPolicies.restrict (templates : List (Template.Pattern Symbol))
    (whole term : Term Symbol) (policies : CallbackOriginPolicies templates whole)
    (origin : SourcePruningEnumerationOrigins.Origin whole term) :
    CallbackOriginPolicies templates term := by
  rcases policies with empty | policies
  · exact .inl empty
  · exact .inr (OriginPolicies.restrict templates whole term policies origin)

/-- An allocated variable inherits the policy at its actual original path. -/
theorem CallbackOriginPolicies.assignment (templates : List (Template.Pattern Symbol))
    (whole : Term Symbol) (limit : Nat) (assignment : Nat → Term Symbol)
    (policies : CallbackOriginPolicies templates whole)
    (origins : SourcePruningEnumerationOrigins.AssignmentOrigins whole limit assignment)
    (uv : Nat) (inside : uv < limit) :
    CallbackOriginPolicies templates (assignment uv) :=
  CallbackOriginPolicies.restrict templates whole (assignment uv) policies (origins uv inside)

/-- Root encoding permits a Type subtree that fails the old empty-catalog condition. -/
theorem encoded_root_not_origin_policy :
    ∃ whole : Term Symbol,
      ProgramEncoding whole ∧ CallbackOriginPolicies [] whole ∧ ¬ OriginPolicies [] whole := by
  let leaf : Term Symbol := .node ("type", FullSyntax.Formula.top) []
  let application : Term Symbol := .node ("app", FullSyntax.Formula.top)
    [leaf, .node ("(->)", FullSyntax.Formula.top) [], leaf, leaf]
  let whole : Term Symbol := .node ("constant", FullSyntax.Formula.top) [application]
  have notLeaf : ¬ ProgramEncoding leaf := by
    intro encoded
    change ProgramEncoding (.node ("type", FullSyntax.Formula.top) []) at encoded
    generalize same : Term.node ("type", FullSyntax.Formula.top) [] = value at encoded
    cases encoded
    all_goals
      have impossible := congrArg List.length (Term.node.inj same).2
      simp at impossible
  have notApplication : ¬ ProgramEncoding application := by
    intro encoded
    change ProgramEncoding (.node ("app", FullSyntax.Formula.top)
      [leaf, .node ("(->)", FullSyntax.Formula.top) [], leaf, leaf]) at encoded
    cases encoded with
    | app _ _ _ functionEncoded _ => exact notLeaf functionEncoded
  refine ⟨whole, .constant _ _, CallbackOriginPolicies.empty whole, ?_⟩
  intro policies
  have origin : SourcePruningEnumerationOrigins.Origin whole application := ⟨[0], rfl⟩
  exact notApplication ((policies application origin).2 application (.application _ _ _ _))

end MicroCFTA.SourcePruningTemplates

namespace MicroCFTA.SourcePruningRecordTypes
open Language SourcePruningPartialMatch
local notation "Symbol" => SourcePruningTemplates.Symbol
attribute [local instance] FormulaExecutable.formulaDecidableEq
variable {Guard Typing : Type}

local instance : Monad List where
  pure value := [value]
  bind values continuation := values.flatMap continuation

/-- Actual recording needs original encoding and avoidance only in the oracle branch. -/
theorem recordTypes_inl_refutes_of_callback_origin (graph : EnumerationState.Graph Symbol Guard)
    (language : EnumerationCorrectness.NodeLanguage Symbol) (meaning : Guard → Term Symbol → Prop)
    (original extended : Nat → Term Symbol) (templates : List (Template.Pattern Symbol))
    (whole : Term Symbol) (fuel uv limit : Nat) (metadata : Metadata Typing)
    (fragment : Fragments.Fragment Symbol) (before after : EnumerationState.State Symbol Guard)
    (result : Bool × Metadata Typing) (total : UnionFind.Total before.representatives)
    (satisfied : EnumerationCorrectness.Satisfies language meaning extended before)
    (filled : Fragments.fill extended fragment = extended uv)
    (policies : SourcePruningTemplates.CallbackOriginPolicies templates whole)
    (origin : SourcePruningEnumerationOrigins.Origin whole (extended uv))
    (bounded : ∀ group ∈ metadata.pending, PendingBound limit group)
    (agree : ∀ key < limit, extended key = original key)
    (refuted : ∀ group ∈ metadata.pending, SourcePruningResume.Refutes original group)
    (success : EnumerationCorrectness.Success
      (recordTypes graph templates fuel metadata uv (.inl fragment)) before result after) :
    result.1 = false ∧ ∀ group ∈ result.2.pending, SourcePruningResume.Refutes extended group := by
  rcases policies with empty | policies
  · subst templates
    rw [recordTypes_empty] at success
    obtain ⟨rfl, _same⟩ :=
      (EnumerationCorrectness.success_pure _ result before after).mp success
    exact ⟨rfl, pending_refutes_extension limit original extended metadata bounded agree refuted⟩
  · exact recordTypes_inl_refutes_of_origin graph language meaning original extended templates whole
      fuel uv limit metadata fragment before after result total satisfied filled policies origin
      bounded agree refuted success

end MicroCFTA.SourcePruningRecordTypes
