import MicroCFTA.InternedNestedCoherentSites
import MicroCFTA.InternedNestedPreparedSites
import MicroCFTA.InternedErasureCorrespondence
import MicroCFTA.InternedRetainedCompletion

/-!
# Immediate-parent replay with older active references retained

Only the most recent pending parent's input changes at an ordinary source
site. Its actual earlier depth trace has the same older captures. Source
steps inside another binder protect a new local reference instead.
-/
namespace MicroCFTA.InternedSelectivePreparedSites
open InternedConstructorTemplates InternedNestedConstruction InternedRecordCoherence
open InternedNestedDependencies InternedNestedTraceSites InternedNestedCoherentSites
open InternedErasureSyntax InternedErasureCorrespondence InternedErasureResidual
open InternedRetainedConstruction (Frame)

/-- Every active frame uses an actual interned source reservation. -/
def NamesInterned (frames : List (Frame Symbol Guard)) : Prop :=
  ∀ frame ∈ frames, ∃ identity, frame.name = .interned identity

/-- The nearest lexical input is one of the active pending source frames. -/
def HeadActive (frames : List (Frame Symbol Guard)) (environment : List (Value Symbol Guard)) : Prop :=
  ∃ frame ∈ frames, environment.head? = some (.reference frame.name)

/-- A sentinel callback does not introduce an active pending reference at its local head. -/
theorem head_depth_inactive (frames : List (Frame Symbol Guard)) (environment : List (Value Symbol Guard))
    (names : NamesInterned frames) : ¬ HeadActive frames (.reference .depth :: environment) := by
  rintro ⟨frame, member, equal⟩
  obtain ⟨identity, same⟩ := names frame member
  simp [same] at equal

/-- The ordinary probe marker is also distinct from every active pending reservation. -/
theorem head_ordinary_inactive (frames : List (Frame Symbol Guard)) (environment : List (Value Symbol Guard))
    (names : NamesInterned frames) (depth : Nat) : ¬ HeadActive frames (.reference (.uninterned depth) :: environment) := by
  rintro ⟨frame, member, equal⟩
  obtain ⟨identity, same⟩ := names frame member
  simp [same] at equal

/-- Ordinary descendants retain their actual earlier depth call with exactly the same older captures. -/
def Ready [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard)
    (environment : List (Value Symbol Guard)) (state : State Symbol Guard) : Prop :=
  ∀ target, Site expression target 0 →
    ∃ before value final, Coherent before ∧ build target (.reference .depth :: environment.tail) before = .done value final ∧ Grows final state

/-- The completed parent depth body supplies each exact source site before its fresh reservation. -/
theorem ready_from_trace [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard)
    (captures : List (Value Symbol Guard)) (head : Value Symbol Guard) (before : State Symbol Guard)
    (value : Value Symbol Guard) (final after : State Symbol Guard) (coherent : Coherent before)
    (completed : build expression (.reference .depth :: captures) before = .done value final)
    (growth : Grows final after) : Ready expression (head :: captures) after := by
  intro target site
  obtain ⟨start, result, finish, returned, startCoherent, _, later⟩ :=
    completed_site_coherent site (.reference .depth :: captures) before value final coherent completed
  exact ⟨start, result, finish, startCoherent, by simpa using returned, grows_trans later growth⟩

/-- Ordinary source descendants retain the same depth call and older captures. -/
theorem Ready.descendant [DecidableEq (EdgeKey Symbol Guard)] {expression target : Syntax Symbol Guard}
    {environment : List (Value Symbol Guard)} {state : State Symbol Guard} (ready : Ready expression environment state)
    (site : Site expression target 0) : Ready target environment state := by
  intro selected nested
  exact ready selected (InternedNestedPreparedSites.Site.trans site nested)

/-- Later source effects preserve the earlier complete call used by immediate-parent replay. -/
theorem Ready.grows [DecidableEq (EdgeKey Symbol Guard)] {expression : Syntax Symbol Guard}
    {environment : List (Value Symbol Guard)} {before after : State Symbol Guard}
    (ready : Ready expression environment before) (growth : Grows before after) : Ready expression environment after := by
  intro target site
  obtain ⟨initial, value, final, coherent, completed, earlier⟩ := ready target site
  exact ⟨initial, value, final, coherent, completed, grows_trans earlier growth⟩

/-- A changed nearest parent can be erased while every older actual capture remains unchanged. -/
theorem Ready.complete [DecidableEq (EdgeKey Symbol Guard)] {expression : Syntax Symbol Guard}
    {environment : List (Value Symbol Guard)} {state : State Symbol Guard}
    (ready : Ready expression environment state) (erased : Erased 0 expression) (coherent : Coherent state) :
    ∃ value final, build expression environment state = .done value final := by
  obtain ⟨before, value, final, beforeCoherent, completed, growth⟩ := ready expression (.here expression)
  have agree : AgreeExcept 0 (.reference .depth :: environment.tail) environment := by
    intro index different
    cases index with
    | zero => exact False.elim (different rfl)
    | succ index => cases environment <;> rfl
  obtain ⟨code, _, _, replay⟩ := build_erased erased _ environment agree before value final beforeCoherent completed
  exact ⟨(run code state).1, (run code state).2, (replay state coherent growth).1⟩

end MicroCFTA.InternedSelectivePreparedSites
