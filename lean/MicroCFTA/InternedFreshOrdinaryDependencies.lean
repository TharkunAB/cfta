import MicroCFTA.InternedFreshOrdinaryPlanEquivalence
import MicroCFTA.InternedNestedDependencies
import MicroCFTA.InternedFreshOrdinaryReplay
import MicroCFTA.InternedStoredSubstitutionBindings
import MicroCFTA.InternedFreshOrdinaryStoredSubstitution

/-!
# Exact repaired execution from source lexical dependencies

Agreement at the original used lexical slots gives equivalent full plans.
The repaired executor therefore has identical outcomes and cache effects.
Stored substitution reads only the original record's free bindings. This
derives the restricted environment used by the native substitution cache.
-/
namespace MicroCFTA.InternedFreshOrdinaryDependencies
open InternedConstructorTemplates
open InternedNestedConstruction (Syntax EdgeSyntax)
open InternedNestedDependencies (inputs manyInputs edgeInputs Agree)
open InternedFreshOrdinaryPlanEquivalence

mutual
/-- Agreement at every original used slot derives equivalent full constructor plans. -/
theorem equivalent (expression : Syntax Symbol Guard) (first second : List (Value Symbol Guard))
    (agree : Agree (inputs expression) first second) : Equivalent expression first expression second := by
  cases expression with
  | empty => rw [Equivalent]; trivial
  | var index => rw [Equivalent]; exact agree index (by simp [inputs])
  | node edges => rw [Equivalent]; exact edges_equivalent edges first second (by simpa only [inputs] using agree)
  | union members => rw [Equivalent]; exact many_equivalent members first second (by simpa only [inputs] using agree)
  | binder smart body =>
      rw [Equivalent]
      refine ⟨rfl, fun name => ?_⟩
      apply equivalent body (.reference name :: first) (.reference name :: second)
      intro index member
      cases index with
      | zero => rfl
      | succ index =>
          apply agree index
          simp only [inputs]
          exact List.mem_filterMap.mpr ⟨index + 1, member, rfl⟩
termination_by sizeOf expression

/-- Agreement on ordered child dependencies derives equivalent child plans. -/
theorem many_equivalent (expressions : List (Syntax Symbol Guard)) (first second : List (Value Symbol Guard))
    (agree : Agree (manyInputs expressions) first second) : ManyEquivalent expressions first expressions second := by
  cases expressions with
  | nil => rw [ManyEquivalent]; trivial
  | cons head tail =>
      rw [ManyEquivalent]
      simp only [manyInputs] at agree
      exact ⟨equivalent head first second (fun index member => agree index (List.mem_append_left _ member)),
        many_equivalent tail first second (fun index member => agree index (List.mem_append_right _ member))⟩
termination_by sizeOf expressions

/-- Agreement on original edge inputs retains every ordered constructor declaration. -/
theorem edges_equivalent (expressions : List (EdgeSyntax Symbol Guard)) (first second : List (Value Symbol Guard))
    (agree : Agree (edgeInputs expressions) first second) : EdgesEquivalent expressions first expressions second := by
  cases expressions with
  | nil => rw [EdgesEquivalent]; trivial
  | cons head tail =>
      cases head with
      | mk symbol guard children =>
          rw [EdgesEquivalent]
          simp only [edgeInputs] at agree
          exact ⟨rfl, rfl,
            many_equivalent children first second (fun index member => agree index (List.mem_append_left _ member)),
            edges_equivalent tail first second (fun index member => agree index (List.mem_append_right _ member))⟩
termination_by sizeOf expressions
end

/-- Unused input changes preserve the exact repaired outcome, including pending construction and every cache effect. -/
theorem build_congr [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard)
    (first second : List (Value Symbol Guard)) (state : State Symbol Guard)
    (agree : Agree (inputs expression) first second) :
    InternedFreshOrdinaryConstruction.build expression first state = InternedFreshOrdinaryConstruction.build expression second state :=
  build_exact expression first expression second state (equivalent expression first second agree)

/-- Repaired construction reuses a completed result after growth when only unused lexical inputs change. -/
theorem independent_replay [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard)
    (first second : List (Value Symbol Guard)) (before after : State Symbol Guard)
    (value : Value Symbol Guard) (final : State Symbol Guard) (valid : Valid before)
    (done : InternedFreshOrdinaryConstruction.build expression first before = .done value final)
    (growth : Grows final after) (agree : Agree (inputs expression) first second) :
    InternedFreshOrdinaryConstruction.build expression second after = .done value after := by
  rw [← build_congr expression first second after agree]
  exact InternedFreshOrdinaryReplay.build_replay expression first before after value final valid done growth

end MicroCFTA.InternedFreshOrdinaryDependencies

namespace MicroCFTA.InternedFreshOrdinaryStoredSubstitution
open InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedStoredSubstitution (Environment leaves input encode leaves_available)

/-- Only the original free bindings can change an actual repaired stored computation. -/
theorem execute_congr [DecidableEq (EdgeKey Symbol Guard)] (value : Value Symbol Guard)
    (first second : Environment Symbol Guard) (state : State Symbol Guard)
    (coherent : Coherent state) (available : Available state value)
    (agree : ∀ name ∈ value.free, first name = second name) : execute value first state = execute value second state := by
  apply InternedFreshOrdinaryDependencies.build_congr
  simpa only [List.nil_append] using InternedStoredSubstitutionBindings.encode_agree (leaves value) [] [] value
    first second state coherent (leaves_available value state available) available (fun _ member => member) rfl
    (fun name member _ => agree name member)

/-- Restricting replacements to the original free names retains exact repaired execution and cache effects. -/
theorem execute_restrict [DecidableEq (EdgeKey Symbol Guard)] (value : Value Symbol Guard)
    (environment : Environment Symbol Guard) (state : State Symbol Guard)
    (coherent : Coherent state) (available : Available state value) :
    execute value (fun name => if name ∈ value.free then environment name else none) state = execute value environment state := by
  apply execute_congr value _ environment state coherent available
  intro name member
  simp [member]

/-- Equal original free bindings replay the same completed result after cache growth with no new allocation. -/
theorem execute_binding_replay [DecidableEq (EdgeKey Symbol Guard)] (value : Value Symbol Guard)
    (first second : Environment Symbol Guard) (before after : State Symbol Guard)
    (coherent : Coherent before) (available : Available before value)
    (agree : ∀ name ∈ value.free, first name = second name) (result : Value Symbol Guard) (final : State Symbol Guard)
    (done : execute value first before = .done result final) (growth : Grows final after) :
    execute value second after = .done result after := by
  have completed : execute value second before = .done result final := by
    rw [← execute_congr value first second before coherent available agree]
    exact done
  exact InternedFreshOrdinaryReplay.build_replay _ _ before after result final coherent.valid completed growth

end MicroCFTA.InternedFreshOrdinaryStoredSubstitution
