import MicroCFTA.InternedNestedConstruction

/-!
# Repaired constructor model with a fresh ordinary placeholder

This repaired executor chooses the ordinary name from the actual Depth result.
It retains the original executor and its closed pending counterexample.
Freshness of one chosen name does not prove general constructor completion.
-/
namespace MicroCFTA.InternedFreshOrdinaryConstruction
open InternedConstructorTemplates InternedNestedConstruction
open InternedBinderProtocol (Reference)

/-- One above every free ordinary level; other reference kinds contribute zero. -/
def freeBound : List Reference → Nat
  | [] => 0
  | .uninterned level :: rest => max (level + 1) (freeBound rest)
  | _ :: rest => freeBound rest

/-- Keep the stored Depth bound unless a free ordinary name requires a larger choice. -/
def ordinaryLevel (depth : Value Symbol Guard) : Nat := max depth.depth (freeBound depth.free)

/-- Every free ordinary level is strictly below the selected free-name bound. -/
theorem freeBound_lt (names : List Reference) (level : Nat) (member : .uninterned level ∈ names) :
    level < freeBound names := by
  induction names with
  | nil => cases member
  | cons name rest ih =>
      rcases List.mem_cons.mp member with own | later
      · subst name
        exact Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_max_left _ _)
      · have below := ih later
        cases name <;> simp only [freeBound]
        case uninterned other => exact Nat.lt_of_lt_of_le below (Nat.le_max_right _ _)
        all_goals exact below

/-- The chosen ordinary name is absent from the actual Depth result's free names. -/
theorem ordinary_fresh (depth : Value Symbol Guard) : .uninterned (ordinaryLevel depth) ∉ depth.free := by
  intro member
  have small := freeBound_lt depth.free (ordinaryLevel depth) member
  have bound : freeBound depth.free ≤ ordinaryLevel depth := Nat.le_max_right _ _
  omega

/-- If all free ordinary names are below a bound, their combined bound is no larger. -/
theorem freeBound_le (names : List Reference) (bound : Nat)
    (below : ∀ level, .uninterned level ∈ names → level < bound) : freeBound names ≤ bound := by
  induction names with
  | nil => simp [freeBound]
  | cons name rest ih =>
      have tail := ih (fun level member => below level (List.mem_cons_of_mem _ member))
      cases name <;> simp only [freeBound]
      case uninterned level =>
        have own := below level List.mem_cons_self
        omega
      all_goals exact tail

/-- A choice with no ordinary-name conflict preserves the original computed depth. -/
theorem ordinary_unchanged (depth : Value Symbol Guard)
    (below : ∀ level, .uninterned level ∈ depth.free → level < depth.depth) : ordinaryLevel depth = depth.depth := by
  exact Nat.max_eq_left (freeBound_le depth.free depth.depth below)

/-- The selected level retains the original depth bound. -/
theorem ordinary_depth_bound (depth : Value Symbol Guard) : depth.depth ≤ ordinaryLevel depth :=
  Nat.le_max_left _ _

/-- Every free ordinary name has a smaller level than the selected placeholder. -/
theorem ordinary_free_bound (depth : Value Symbol Guard) (level : Nat)
    (member : .uninterned level ∈ depth.free) : level < ordinaryLevel depth :=
  Nat.lt_of_lt_of_le (freeBound_lt depth.free level member) (Nat.le_max_right _ _)

/-- The policy picks the least level that retains the depth bound and exceeds all free ordinary names. -/
theorem ordinary_minimal (depth : Value Symbol Guard) (bound : Nat) :
    ordinaryLevel depth ≤ bound ↔ depth.depth ≤ bound ∧
      ∀ level, .uninterned level ∈ depth.free → level < bound := by
  constructor
  · intro upper
    exact ⟨Nat.le_trans (ordinary_depth_bound depth) upper,
      fun level member => Nat.lt_of_lt_of_le (ordinary_free_bound depth level member) upper⟩
  · rintro ⟨deep, free⟩
    have allFree := freeBound_le depth.free bound free
    unfold ordinaryLevel
    omega

/-- The readback fast path uses the chosen level from the stored Depth probe. -/
def probeReadback (depth ordinary : Value Symbol Guard) (name : Reference) : Option (Value Symbol Guard) :=
  if name = .depth then some depth
  else if name = .uninterned (ordinaryLevel depth) then some ordinary else none

/-- The repaired matcher returns the exact stored Depth component. -/
theorem probeReadback_depth (depth ordinary : Value Symbol Guard) : probeReadback depth ordinary .depth = some depth := by
  simp [probeReadback]

/-- The repaired matcher uses exactly the ordinary name used by construction. -/
theorem probeReadback_ordinary (depth ordinary : Value Symbol Guard) :
    probeReadback depth ordinary (.uninterned (ordinaryLevel depth)) = some ordinary := by
  simp [probeReadback]

mutual
/-- Execute the full nested constructor schedule directly from source expression. -/
def build [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard) (environment : List (Value Symbol Guard))
    (state : InternedConstructorTemplates.State Symbol Guard) : Outcome Symbol Guard (Value Symbol Guard) :=
  match expression with
  | .empty => .done .empty state
  | .var index => .done (environment[index]?.getD .empty) state
  | .node edges => (buildEdges edges environment state).bind fun values next => work (makeNode values) next
  | .union members => (buildMany members environment state).bind fun values next => work (makeUnion values) next
  | .binder smart body =>
      let callback := fun name current => (build body (.reference name :: environment) current).bind
        fun value next => work (withoutSelfReference name value) next
      (callback .depth state).bind fun depth afterDepth =>
      (callback (.uninterned (ordinaryLevel depth)) afterDepth).bind fun ordinary afterOrdinary =>
        request smart depth ordinary callback afterOrdinary
termination_by sizeOf expression

/-- Child expression executes in source order and retains every completed value. -/
def buildMany [DecidableEq (EdgeKey Symbol Guard)] (expression : List (Syntax Symbol Guard))
    (environment : List (Value Symbol Guard)) (state : InternedConstructorTemplates.State Symbol Guard) :
    Outcome Symbol Guard (List (Value Symbol Guard)) :=
  match expression with
  | [] => .done [] state
  | first :: rest => (build first environment state).bind fun value next =>
      (buildMany rest environment next).bind fun values final => .done (value :: values) final
termination_by sizeOf expression

/-- Edge construction occurs after its actual nested child computations complete. -/
def buildEdges [DecidableEq (EdgeKey Symbol Guard)] (expression : List (EdgeSyntax Symbol Guard))
    (environment : List (Value Symbol Guard)) (state : InternedConstructorTemplates.State Symbol Guard) :
    Outcome Symbol Guard (List (EdgeValue Symbol Guard)) :=
  match expression with
  | [] => .done [] state
  | .mk symbol constraint children :: rest =>
      (buildMany children environment state).bind fun values next =>
      (work (makeEdge symbol constraint values) next).bind fun edge afterEdge =>
      (buildEdges rest environment afterEdge).bind fun edges final => .done (edge :: edges) final
termination_by sizeOf expression
end

end MicroCFTA.InternedFreshOrdinaryConstruction
