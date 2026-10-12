import MicroCFTA.InternedOuterErasure
import MicroCFTA.InternedNestedCoherentSites
import MicroCFTA.InternedNestedPreparedSites
import MicroCFTA.InternedDeepErasureCompletion

/-!
# Actual depth traces prepare normalized erased source subprograms

A prepared subprogram can read enclosing inputs that normalization removes.
Its exact earlier source call supplies every later replay premise. Changed
inputs retain their discarded-edge effects before complete record readback.
-/
namespace MicroCFTA.InternedNormalizedPreparedSites
open InternedConstructorTemplates InternedNestedConstruction InternedRecordCoherence
open InternedNestedDependencies InternedNestedTraceSites InternedNestedCoherentSites
open InternedOuterErasure InternedErasureResidual

/-- A subprogram either has the earlier closed-source proof or recursively erases all enclosing inputs. -/
def Leaf (expression : Syntax Symbol Guard) : Prop := InternedNestedPreparedSites.Leaf expression ∨
  (OuterErased 0 expression ∧ InternedDeepErasureCompletion.Admitted expression)

/-- Each actual source site has its complete earlier trace and the corresponding coherent starting state. -/
def Ready [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard) (state : State Symbol Guard) : Prop :=
  ∀ target crossed, Site expression target crossed →
    ∃ environment before value final, Coherent before ∧ build target environment before = .done value final ∧ Grows final state

/-- Every complete source trace supplies all later preparation directly from its actual child executions. -/
theorem ready_from_trace [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard)
    (environment : List (Value Symbol Guard)) (before : State Symbol Guard)
    (value : Value Symbol Guard) (final after : State Symbol Guard) (coherent : Coherent before)
    (completed : build expression environment before = .done value final) (growth : Grows final after) : Ready expression after := by
  intro target crossed site
  obtain ⟨start, result, finish, returned, startCoherent, _, later⟩ :=
    completed_site_coherent site environment before value final coherent completed
  exact ⟨List.replicate crossed (.reference .depth) ++ environment, start, result, finish,
    startCoherent, returned, grows_trans later growth⟩

/-- Source descendants retain their actual earlier site and complete trace. -/
theorem Ready.descendant [DecidableEq (EdgeKey Symbol Guard)] {expression target : Syntax Symbol Guard}
    {crossed : Nat} {state : State Symbol Guard} (ready : Ready expression state)
    (site : Site expression target crossed) : Ready target state := by
  intro selected inner nested
  exact ready selected (crossed + inner) (InternedNestedPreparedSites.Site.trans site nested)

/-- Later constructor effects retain every prepared source trace. -/
theorem Ready.grows [DecidableEq (EdgeKey Symbol Guard)] {expression : Syntax Symbol Guard} {before after : State Symbol Guard}
    (ready : Ready expression before) (growth : Grows before after) : Ready expression after := by
  intro target crossed site
  obtain ⟨environment, initial, value, final, coherent, completed, earlier⟩ := ready target crossed site
  exact ⟨environment, initial, value, final, coherent, completed, grows_trans earlier growth⟩

/-- Earlier closed subprograms and normalized erased subprograms both ignore all changed enclosing values after normalization. -/
theorem Leaf.erased {expression : Syntax Symbol Guard} (leaf : Leaf expression) : OuterErased 0 expression := by
  rcases leaf with closed | normalized
  · exact .unused 0 expression (fun index member => by simp [closed.1] at member)
  · exact normalized.1

/-- A prepared source subprogram completes with its actual later discarded-edge effects while outer records are pending. -/
theorem Ready.complete [DecidableEq (EdgeKey Symbol Guard)] {expression : Syntax Symbol Guard} {state : State Symbol Guard}
    (ready : Ready expression state) (leaf : Leaf expression) (environment : List (Value Symbol Guard)) (coherent : Coherent state) :
    ∃ value final, build expression environment state = .done value final := by
  obtain ⟨oldEnvironment, before, value, final, beforeCoherent, completed, growth⟩ := ready expression 0 (.here expression)
  obtain ⟨code, _, _, replay⟩ := build_outer_erased leaf.erased oldEnvironment environment
    (fun index impossible => by omega) before value final beforeCoherent completed
  have repeated := (replay state coherent growth).1
  exact ⟨(run code state).1, (run code state).2, repeated⟩

/-- First encounter in complete tables obtains its initial source execution by the earlier proved grammar. -/
theorem leaf_completes [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard)
    (leaf : Leaf expression) (environment : List (Value Symbol Guard)) (state : State Symbol Guard)
    (coherent : Coherent state) (covered : Covered [] state) :
    ∃ value final, build expression environment state = .done value final := by
  rcases leaf with closed | normalized
  · exact InternedNestedPreparedSites.leaf_completes expression closed environment state coherent covered
  · cases environment with
    | nil =>
        obtain ⟨value, final, _, completed, _⟩ :=
          InternedDeepErasureCompletion.build_residual expression normalized.2 .empty [] state coherent covered
        have same := build_congr expression [] [.empty] state (by intro index member; cases index <;> rfl)
        exact ⟨value, final, same.trans completed⟩
    | cons first rest =>
        obtain ⟨value, final, _, completed, _⟩ :=
          InternedDeepErasureCompletion.build_residual expression normalized.2 first rest state coherent covered
        exact ⟨value, final, completed⟩

end MicroCFTA.InternedNormalizedPreparedSites
