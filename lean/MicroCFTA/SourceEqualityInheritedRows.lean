import MicroCFTA.SourceEqualityInheritedEdgeWorker

/-!
# Actual ordered rows of partial equality reduction

Each row runs local edge narrowing before inherited child traversal. The
next row uses the returned native state. Incomplete observations retain the
original edge stage. Completed row graphs have stable local stage bounds
for a fixed recursive node callback.
-/
namespace MicroCFTA.SourceEqualityInheritedRows
open InternedConstructorTemplates SourceObservations SourceSymbolicIndex
open SourceEqualityClassFoldGraph SourceEqualityNativeScoped
universe u
local notation "Symbol" => Label FullSyntax.Formula
local notation "Guard" => Constraint FullSyntax.Formula

/-- Ordered row observations keep the complete edge result or the exact unfinished row. -/
inductive Result (width : Nat) (Observation : Type u) : Type (max 1 u) where
  | done (answer : Except String (List (EdgeValue Symbol Guard))) (state : NativeState width Symbol Guard)
  | incomplete (observation : SourceEqualityInheritedEdgeWorker.Result width Observation)

/-- Source map executes each complete row before requesting the next row. -/
noncomputable def walk [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (call : SourceEqualityPrecheck.Constraint → Value Symbol Guard → NativeState width Symbol Guard →
      SourceEqualityInheritedChildren.Result width Symbol Guard (Value Symbol Guard) Observation)
    (g e p h c n : Nat) (inherited : SourceEqualityPrecheck.Constraint) :
    List (EdgeValue Symbol Guard) → NativeState width Symbol Guard → Result width Observation
  | [], before => .done (.ok []) before
  | edge :: edges, before =>
      match SourceEqualityInheritedEdgeWorker.run call g e p h c n edge inherited before with
      | .done (.ok result) middle => match walk call g e p h c n inherited edges middle with
        | .done (.ok results) after => .done (.ok (result :: results)) after
        | .done (.error message) after => .done (.error message) after
        | .incomplete observation => .incomplete observation
      | .done (.error message) middle => .done (.error message) middle
      | observation => .incomplete observation

/-- Every completed row keeps its concrete source edge execution and the actual next state. -/
inductive Graph [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (call : SourceEqualityPrecheck.Constraint → Value Symbol Guard → NativeState width Symbol Guard →
      SourceEqualityInheritedChildren.Result width Symbol Guard (Value Symbol Guard) Observation)
    (inherited : SourceEqualityPrecheck.Constraint) :
    List (EdgeValue Symbol Guard) → NativeState width Symbol Guard → List (EdgeValue Symbol Guard) → NativeState width Symbol Guard → Prop where
  | nil : Graph call inherited [] before [] before
  | cons (first : SourceEqualityInheritedEdge.Execution call edge inherited before result middle)
      (rest : Graph call inherited edges middle results after) : Graph call inherited (edge :: edges) before (result :: results) after

/-- A completed ordered traversal preserves the number of rows. -/
theorem Graph.length [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {call inherited edges before results after} (trace : Graph (Observation := Observation) (width := width) call inherited edges before results after) :
    results.length = edges.length := by
  induction trace with
  | nil => rfl
  | cons _ _ ih => exact congrArg Nat.succ ih

/-- Every completed graph has uniform stable stage bounds and identical full native state. -/
theorem Graph.stable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {call inherited edges before results after} (trace : Graph (Observation := Observation) (width := width) call inherited edges before results after) :
    ∃ g e p h c n, ∀ gg ee pp hh cc nn, g ≤ gg → e ≤ ee → p ≤ pp → h ≤ hh → c ≤ cc → n ≤ nn →
      walk call gg ee pp hh cc nn inherited edges before = .done (.ok results) after := by
  induction trace with
  | nil => exact ⟨0, 0, 0, 0, 0, 0, by intros; rfl⟩
  | cons first _ ih =>
      obtain ⟨g, e, p, h, c, n, head⟩ := SourceEqualityInheritedEdgeWorker.stable first
      obtain ⟨rg, re, rp, rh, rc, rn, tail⟩ := ih
      refine ⟨max g rg, max e re, max p rp, max h rh, max c rc, max n rn, ?_⟩
      intro gg ee pp hh cc nn enoughG enoughE enoughP enoughH enoughC enoughN
      have firstDone := head gg ee pp hh cc nn (Nat.le_trans (Nat.le_max_left _ _) enoughG)
        (Nat.le_trans (Nat.le_max_left _ _) enoughE) (Nat.le_trans (Nat.le_max_left _ _) enoughP)
        (Nat.le_trans (Nat.le_max_left _ _) enoughH) (Nat.le_trans (Nat.le_max_left _ _) enoughC) (Nat.le_trans (Nat.le_max_left _ _) enoughN)
      have restDone := tail gg ee pp hh cc nn (Nat.le_trans (Nat.le_max_right _ _) enoughG)
        (Nat.le_trans (Nat.le_max_right _ _) enoughE) (Nat.le_trans (Nat.le_max_right _ _) enoughP)
        (Nat.le_trans (Nat.le_max_right _ _) enoughH) (Nat.le_trans (Nat.le_max_right _ _) enoughC) (Nat.le_trans (Nat.le_max_right _ _) enoughN)
      simp only [walk, firstDone, restDone]

/-- Range checks apply at the actual row prefix and each actual returned warm state. -/
def Ranges [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (call : SourceEqualityPrecheck.Constraint → Value Symbol Guard → NativeState width Symbol Guard →
      SourceEqualityInheritedChildren.Result width Symbol Guard (Value Symbol Guard) Observation)
    (g e p h c n : Nat) (inherited : SourceEqualityPrecheck.Constraint) : List (EdgeValue Symbol Guard) → NativeState width Symbol Guard → Prop
  | [], _ => True
  | edge :: edges, before => SourceEqualityPCSNativeEdge.Ranges edge inherited before ∧
      ∀ result middle, SourceEqualityInheritedEdgeWorker.run call g e p h c n edge inherited before = .done (.ok result) middle →
        Ranges call g e p h c n inherited edges middle

/-- A successful bounded worker derives every concrete row receipt from its reached word checks. -/
theorem graph [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {call inherited edges before results after} (g e p h c n : Nat)
    (ranges : Ranges (Observation := Observation) (width := width) call g e p h c n inherited edges before)
    (done : walk call g e p h c n inherited edges before = .done (.ok results) after) :
    Graph call inherited edges before results after := by
  induction edges generalizing before results after with
  | nil => cases done; exact .nil
  | cons edge edges ih =>
      cases first : SourceEqualityInheritedEdgeWorker.run call g e p h c n edge inherited before with
      | guarded | children => simp only [walk, first] at done; cases done
      | done answer middle =>
          cases answer with
          | error => simp only [walk, first] at done; cases done
          | ok result =>
              cases rest : walk call g e p h c n inherited edges middle with
              | incomplete => simp only [walk, first, rest] at done; cases done
              | done answer final =>
                  cases answer with
                  | error => simp only [walk, first, rest] at done; cases done
                  | ok tail =>
                      simp only [walk, first, rest, Result.done.injEq, Except.ok.injEq] at done
                      rcases done with ⟨rfl, rfl⟩
                      exact .cons (SourceEqualityInheritedEdgeWorker.run_graph g e p h c n ranges.1 first)
                        (ih (ranges.2 result middle first) rest)

end MicroCFTA.SourceEqualityInheritedRows
