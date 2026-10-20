import MicroCFTA.SourceCurrentNativeMuPublication

/-!
# Mu publication histories with actual cache growth

Every retained effect preserves all four cache tables. Publication retains
its three callback paths. This evidence is stronger than NoNewMu alone.
-/
namespace MicroCFTA.SourceCurrentNativeMuGrowthHistory
open Cache InternedConstructorTemplates InternedRecordCoherence
open InternedShallowHeap (NoNewMu)
open SourceCurrentNativeMuPublication (Publication History)

/-- Reservation preserves every entry of both caches and both record tables. -/
theorem reserve_growth [DecidableEq (EdgeKey Symbol Guard)]
    (event : Publication (Symbol := Symbol) (Guard := Guard)) :
    Grows event.cut event.allocated :=
  ⟨extends_refl _, InternedBinderProtocol.intern_grows _ _, extends_refl _, extends_refl _⟩

/-- Publication preserves all earlier records, including an earlier winner. -/
theorem publication_growth [DecidableEq (EdgeKey Symbol Guard)]
    (event : Publication (Symbol := Symbol) (Guard := Guard)) :
    Grows event.afterBody event.after :=
  ⟨extends_refl _, extends_refl _, extends_refl _, keepFirst_extends _ _ _⟩

/-- Each actual effect retains cache growth as well as its causal publication order. -/
inductive Path [DecidableEq (EdgeKey Symbol Guard)] : State Symbol Guard → State Symbol Guard → Type where
  /-- No effect changes the state. -/
  | refl (state) : Path state state
  /-- An effect preserves old entries and adds no completed Mu. -/
  | retain (before after) (old : NoNewMu before after) (growth : Grows before after) : Path before after
  /-- The next path starts at the first path's final state. -/
  | trans {before middle after} (first : Path before middle) (next : Path middle after) : Path before after
  /-- Publication follows its three completed callback paths. -/
  | publication (event : Publication (Symbol := Symbol) (Guard := Guard))
      (depth : Path event.before event.afterDepth)
      (ordinary : Path event.afterDepth event.cut)
      (body : Path event.allocated event.afterBody) : Path event.before event.after

/-- A path retains the complete earlier publication history. -/
def Path.history [DecidableEq (EdgeKey Symbol Guard)] {before after : State Symbol Guard}
    (path : Path before after) : History before after :=
  match path with
  | .refl state => .refl state
  | .retain before after old _ => .retain before after old
  | .trans first next => .trans first.history next.history
  | .publication event depth ordinary body => .publication event depth.history ordinary.history body.history

/-- All cache tables grow along the entire actual path. -/
theorem Path.growth [DecidableEq (EdgeKey Symbol Guard)] {before after : State Symbol Guard}
    (path : Path before after) : Grows before after := by
  induction path with
  | refl state => exact grows_refl state
  | retain _ _ _ growth => exact growth
  | trans _ _ first next => exact grows_trans first next
  | publication event _ _ _ depth ordinary body =>
      exact grows_trans depth (grows_trans ordinary
        (grows_trans (reserve_growth event) (grows_trans body (publication_growth event))))

end MicroCFTA.SourceCurrentNativeMuGrowthHistory
