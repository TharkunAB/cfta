import MicroCFTA.InternedNestedTraceSites
import MicroCFTA.InternedIndependentCompletion
import MicroCFTA.InternedErasedBodyCompletion

/-!
# Earlier source probes prepare complete closed subprograms

The original syntax identifies each closed subprogram. A completed enclosing
depth trace supplies its complete canonical result before the enclosing
reservation. Later state growth retains that exact result and every effect.
-/
namespace MicroCFTA.InternedNestedPreparedSites
open InternedConstructorTemplates InternedNestedConstruction InternedNestedDependencies InternedNestedTraceSites
open InternedRecordCoherence

/-- A closed subprogram has an existing syntax-derived first-completion proof. -/
def Leaf (expression : Syntax Symbol Guard) : Prop := inputs expression = [] ∧
  (InternedIndependentCompletion.Staged expression ∨
    ∃ smart body, expression = .binder smart body ∧ InternedErasedBodyResidual.Admitted body)

/-- Earlier complete source executions make every closed descendant ready to replay without allocations. -/
def Ready [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard) (state : State Symbol Guard) : Prop :=
  ∀ target crossed, Site expression target crossed → inputs target = [] →
    ∃ value, build target [] state = .done value state

/-- Source positions compose with the exact number of crossed binders. -/
theorem Site.trans {first middle last : Syntax Symbol Guard} {outer inner : Nat}
    (before : Site first middle outer) (after : Site middle last inner) : Site first last (outer + inner) := by
  induction before with
  | here expression => simpa using after
  | node edge member nested ih => exact .node edge member (ih after)
  | union member nested ih => exact .union member (ih after)
  | binder nested ih => simpa only [Nat.add_right_comm] using (Site.binder (ih after))

/-- A completed enclosing trace prepares all closed source sites from their actual earlier executions. -/
theorem ready_from_trace [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard)
    (environment : List (Value Symbol Guard)) (before : State Symbol Guard)
    (value : Value Symbol Guard) (final after : State Symbol Guard)
    (valid : InternedConstructorTemplates.Valid before)
    (completed : build expression environment before = .done value final) (growth : Grows final after) : Ready expression after := by
  intro target crossed site closed
  obtain ⟨result, replay⟩ := site_replay site environment before value final valid completed
  refine ⟨result, replay [] after growth ?_⟩
  intro index member
  simp [closed] at member

/-- Restrict the earlier-trace certificate to any actual descendant source expression. -/
theorem Ready.descendant [DecidableEq (EdgeKey Symbol Guard)] {expression target : Syntax Symbol Guard} {crossed : Nat} {state : State Symbol Guard}
    (ready : Ready expression state) (site : Site expression target crossed) : Ready target state := by
  intro selected inner nested closed
  exact ready selected (crossed + inner) (Site.trans site nested) closed

/-- Complete prepared requests retain exact canonical payloads after every later source effect. -/
theorem Ready.grows [DecidableEq (EdgeKey Symbol Guard)] {expression : Syntax Symbol Guard}
    {before after : State Symbol Guard} (ready : Ready expression before)
    (valid : InternedConstructorTemplates.Valid before) (growth : Grows before after) : Ready expression after := by
  intro target crossed site closed
  obtain ⟨value, completed⟩ := ready target crossed site closed
  exact ⟨value, build_replay target [] before after value before valid completed growth⟩

/-- A prepared closed expression ignores every changed enclosing lexical input. -/
theorem Ready.complete [DecidableEq (EdgeKey Symbol Guard)] {expression : Syntax Symbol Guard} {state : State Symbol Guard}
    (ready : Ready expression state) (closed : inputs expression = []) (environment : List (Value Symbol Guard)) :
    ∃ value, build expression environment state = .done value state := by
  obtain ⟨value, completed⟩ := ready expression 0 (.here expression) closed
  refine ⟨value, ?_⟩
  rw [build_congr expression environment [] state (by intro index member; simp [closed] at member)]
  exact completed

/-- A closed independent or erased-body subprogram completes before any enclosing reservation exists. -/
theorem leaf_completes [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard)
    (leaf : Leaf expression) (environment : List (Value Symbol Guard)) (state : State Symbol Guard)
    (coherent : Coherent state) (covered : Covered [] state) :
    ∃ value final, build expression environment state = .done value final := by
  rcases leaf.2 with independent | ⟨smart, body, rfl, erased⟩
  · exact InternedIndependentCompletion.build_completes expression independent environment state coherent.valid covered
  · exact InternedErasedBodyResidual.binder_completes smart body erased environment state coherent covered

end MicroCFTA.InternedNestedPreparedSites
