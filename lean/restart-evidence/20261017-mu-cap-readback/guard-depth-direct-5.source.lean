import MicroCFTA.SourceCurrentConstrainedCap

/-!
# Exact finite guard-depth profiles of stored values

A missing profile means that a nonhereditary Mu occurs in the value.
A present natural number is the least finite constraint-depth bound.
The observer reads actual guards and stored Mu bodies. It does not use
languages, probe metadata, cache history, or a supplied cap witness.
-/
namespace MicroCFTA.SourceCurrentConstrainedCapGuardDepth
open Cache InternedConstructorTemplates InternedProbeProvenance InternedRecordCoherence InternedNestedFacts
open SourceEqualityAnnotationLanguage
open SourceCurrentConstrainedCap (Cap)
variable {Symbol Guard : Type}

/-- Both finite profiles must be present; their larger depth is retained. -/
def join : Option Nat → Option Nat → Option Nat
  | some first, some second => some (max first second)
  | _, _ => none

/-- A hereditary child costs zero; a constrained child consumes an ordinary layer. -/
def raise : Option Nat → Option Nat
  | some 0 => some 0
  | some (depth + 1) => some (depth + 2)
  | none => none

/-- A guard outside the supplied predicate consumes one finite ordinary layer. -/
noncomputable def guardCost (valid : Guard → Prop) (guard : Guard) : Nat := by
  classical
  exact if valid guard then 0 else 1

/-- A finite observed depth must not exceed the supplied upper bound. -/
def Within (depth : Nat) : Option Nat → Prop
  | some actual => actual ≤ depth
  | none => False

mutual
/-- Literal stored guards determine the finite constraint depth or an obstructing Mu. -/
noncomputable def profile (valid : Guard → Prop) : Value Symbol Guard → Option Nat
  | .empty | .reference _ => some 0
  | .node _ edges _ _ => rows valid edges
  | .union _ members _ _ => children valid members
  | .mu _ body _ _ => if profile valid body = some 0 then some 0 else none
termination_by value => sizeOf value

/-- Ordered alternatives retain the greatest finite depth and every Mu obstruction. -/
noncomputable def children (valid : Guard → Prop) : List (Value Symbol Guard) → Option Nat
  | [] => some 0
  | first :: rest => join (profile valid first) (children valid rest)
termination_by values => sizeOf values

/-- A row retains its guard cost and the ordinary-layer cost of its actual children. -/
noncomputable def rows (valid : Guard → Prop) : List (EdgeValue Symbol Guard) → Option Nat
  | [] => some 0
  | .mk entry values :: rest => join (join (some (guardCost valid entry.key.constraint)) (raise (children valid values))) (rows valid rest)
termination_by edges => sizeOf edges
end

/-- Both observed operands fit exactly when their joined profile fits. -/
theorem within_join (depth : Nat) (first second : Option Nat) :
    Within depth (join first second) ↔ Within depth first ∧ Within depth second := by
  cases first <;> cases second <;> simp [join, Within, Nat.max_le]

/-- A zero ordinary layer admits only a hereditary child profile. -/
theorem within_raise_zero (value : Option Nat) : Within 0 (raise value) ↔ Within 0 value := by
  cases value with
  | none => rfl
  | some value => cases value <;> simp [raise, Within]

/-- A positive ordinary layer removes exactly one finite constraint depth. -/
theorem within_raise_succ (depth : Nat) (value : Option Nat) : Within (depth + 1) (raise value) ↔ Within depth value := by
  cases value with
  | none => rfl
  | some value => cases value <;> simp [raise, Within]

/-- The zero guard cost is the exact original guard predicate. -/
theorem guardCost_zero (valid : Guard → Prop) (guard : Guard) : Within 0 (some (guardCost valid guard)) ↔ valid guard := by
  classical
  by_cases allowed : valid guard <;> simp [guardCost, allowed, Within]

/-- Every raw guard fits a positive finite layer. -/
theorem guardCost_succ (valid : Guard → Prop) (guard : Guard) (depth : Nat) : Within (depth + 1) (some (guardCost valid guard)) := by
  classical
  by_cases allowed : valid guard <;> simp [guardCost, allowed, Within]

/-- Ordered observed child bounds are exactly the bounds of all actual members. -/
theorem children_within (valid : Guard → Prop) (depth : Nat) (values : List (Value Symbol Guard)) :
    Within depth (children valid values) ↔ ∀ value ∈ values, Within depth (profile valid value) := by
  induction values with
  | nil => simp [children, Within]
  | cons first rest ih => simp [children, within_join, ih]

/-- A zero row profile records both its guard and all hereditary child profiles. -/
theorem rows_within_zero (valid : Guard → Prop) (edges : List (EdgeValue Symbol Guard)) :
    Within 0 (rows valid edges) ↔
      (∀ edge ∈ edges, valid edge.entry.key.constraint) ∧
      ∀ child ∈ edges.flatMap EdgeValue.children, Within 0 (profile valid child) := by
  induction edges with
  | nil => simp [rows, Within]
  | cons edge rest ih =>
      cases edge with
      | mk entry values =>
          simp only [rows, within_join, guardCost_zero, within_raise_zero, children_within, ih]
          simp only [List.mem_cons, List.flatMap_cons, List.mem_append, EdgeValue.children]
          constructor
          · rintro ⟨⟨guard, first⟩, guards, last⟩
            exact ⟨by intro edge member; rcases member with rfl | later; exact guard; exact guards edge later,
              by intro child member; rcases member with early | later; exact first child early; exact last child later⟩
          · rintro ⟨guards, children⟩
            exact ⟨⟨guards _ (Or.inl rfl), fun child member => children child (Or.inl member)⟩,
              (fun edge member => guards edge (Or.inr member)), fun child member => children child (Or.inr member)⟩

/-- A positive row profile records the smaller bound of every actual child. -/
theorem rows_within_succ (valid : Guard → Prop) (depth : Nat) (edges : List (EdgeValue Symbol Guard)) :
    Within (depth + 1) (rows valid edges) ↔ ∀ child ∈ edges.flatMap EdgeValue.children, Within depth (profile valid child) := by
  induction edges with
  | nil => simp [rows, Within]
  | cons edge rest ih =>
      cases edge with
      | mk entry values =>
          simp only [rows, within_join, guardCost_succ, true_and, within_raise_succ, children_within, ih]
          simp only [List.flatMap_cons, EdgeValue.children, List.mem_append]
          constructor
          · rintro ⟨first, last⟩ child member
            rcases member with early | later
            · exact first child early
            · exact last child later
          · intro all
            exact ⟨fun child member => all child (Or.inl member), fun child member => all child (Or.inr member)⟩

private theorem child_size (entry) (edges : List (EdgeValue Symbol Guard)) (level free) (child : Value Symbol Guard)
    (member : child ∈ edges.flatMap EdgeValue.children) : sizeOf child < sizeOf (Value.node entry edges level free) := by
  obtain ⟨edge, present, inside⟩ := List.mem_flatMap.mp member
  have outer := List.sizeOf_lt_of_mem present
  cases edge with
  | mk own values =>
      have inner := List.sizeOf_lt_of_mem inside
      simp only [Value.node.sizeOf_spec, EdgeValue.mk.sizeOf_spec, EdgeValue.children] at *
      omega

/-- Increasing the numeric bound retains the same literal observed profile. -/
theorem within_mono {first last : Nat} {value : Option Nat} (bounded : Within first value) (increase : first ≤ last) :
    Within last value := by
  cases value with
  | none => exact bounded.elim
  | some actual => exact Nat.le_trans bounded increase

/-- A zero profile is exactly an annotated stored value, including its actual Mu body. -/
theorem zero_iff_annotated (valid : Guard → Prop) (value : Value Symbol Guard) :
    Within 0 (profile valid value) ↔ Annotated valid value := by
  cases value with
  | empty => exact ⟨fun _ => .empty, fun _ => by simp only [profile, Within, Nat.le_refl]⟩
  | reference name => exact ⟨fun _ => .reference name, fun _ => by simp only [profile, Within, Nat.le_refl]⟩
  | node entry edges level free =>
      rw [profile, rows_within_zero]
      constructor
      · rintro ⟨guards, children⟩
        exact .node entry edges level free guards (fun child member => (zero_iff_annotated valid child).mp (children child member))
      · intro annotated
        cases annotated with
        | node _ _ _ _ guards children =>
            exact ⟨guards, fun child member => (zero_iff_annotated valid child).mpr (children child member)⟩
  | union entry members level free =>
      rw [profile, children_within]
      constructor
      · intro children
        exact .union entry members level free (fun child member => (zero_iff_annotated valid child).mp (children child member))
      · intro annotated
        cases annotated with
        | union _ _ _ _ children => exact fun child member => (zero_iff_annotated valid child).mpr (children child member)
  | mu entry body depth ordinary =>
      rw [profile]
      constructor
      · split
        · rename_i zero
          exact fun _ => .mu entry body depth ordinary ((zero_iff_annotated valid body).mp (by simp [zero, Within]))
        · exact False.elim
      · intro annotated
        cases annotated with
        | mu _ _ _ _ bodyAnnotated =>
            have bounded := (zero_iff_annotated valid body).mpr bodyAnnotated
            have zero : profile valid body = some 0 := by
              cases computed : profile valid body with
              | none => simp [computed, Within] at bounded
              | some depth => have same : depth = 0 := by simpa [computed, Within] using bounded
                              simp [same]
            simp [zero, Within]
termination_by sizeOf value
decreasing_by
  all_goals
    subst_vars
    first | exact child_size _ _ _ _ _ member | decreasing_trivial

/-- Every supplied finite cap bounds the independently computed structural profile. -/
theorem profile_of_cap {valid : Guard → Prop} {depth : Nat} {value : Value Symbol Guard}
    (bounded : Cap valid depth value) : Within depth (profile valid value) := by
  induction bounded with
  | plain depth annotated =>
      have zero := (zero_iff_annotated valid _).mpr annotated
      exact within_mono zero (Nat.zero_le _)
  | node depth entry edges level free children ih => simpa only [profile] using (rows_within_succ valid depth edges).mpr ih
  | union depth entry members level free children ih => simpa only [profile] using (children_within valid depth members).mpr ih

/-- A finite structural profile constructs the exact existing finite-cap predicate. -/
theorem cap_of_profile (valid : Guard → Prop) (depth : Nat) (value : Value Symbol Guard)
    (bounded : Within depth (profile valid value)) : Cap valid depth value := by
  cases depth with
  | zero => exact .plain 0 ((zero_iff_annotated valid value).mp bounded)
  | succ depth =>
      cases value with
      | empty => exact .plain _ .empty
      | reference name => exact .plain _ (.reference name)
      | node entry edges level free =>
          exact .node depth entry edges level free (fun child member => cap_of_profile valid depth child
            ((rows_within_succ valid depth edges).mp (by simpa only [profile] using bounded) child member))
      | union entry members level free =>
          exact .union (depth + 1) entry members level free (fun child member => cap_of_profile valid (depth + 1) child
            ((children_within valid (depth + 1) members).mp (by simpa only [profile] using bounded) child member))
      | mu entry body level ordinary =>
          have zero : Within 0 (profile valid (.mu entry body level ordinary)) := by
            by_cases same : profile valid body = some 0 <;> simp_all only [profile, ite_true, ite_false, Within, Nat.zero_le]
          exact .plain _ ((zero_iff_annotated valid _).mp zero)
termination_by sizeOf value
decreasing_by
  all_goals
    subst_vars
    first | exact child_size _ _ _ _ _ member | decreasing_trivial

/-- The computed literal profile is the exact least finite constraint-depth bound. -/
theorem within_iff_cap (valid : Guard → Prop) (depth : Nat) (value : Value Symbol Guard) :
    Within depth (profile valid value) ↔ Cap valid depth value :=
  ⟨cap_of_profile valid depth value, profile_of_cap⟩

/-- A zero observed profile is the exact original hereditary annotation predicate. -/
theorem profile_zero_iff (valid : Guard → Prop) (value : Value Symbol Guard) :
    profile valid value = some 0 ↔ Annotated valid value := by
  rw [← zero_iff_annotated valid value]
  cases computed : profile valid value <;> simp [Within]

/-- A missing profile excludes every finite cap, without a language assumption. -/
theorem profile_none_iff (valid : Guard → Prop) (value : Value Symbol Guard) :
    profile valid value = none ↔ ∀ depth, ¬Cap valid depth value := by
  constructor
  · intro missing depth bounded
    have within := profile_of_cap bounded
    simp only [missing, Within] at within
  · intro absent
    cases computed : profile valid value with
    | none => rfl
    | some depth => exact False.elim (absent depth (cap_of_profile valid depth value (by simp [computed, Within])))

/-- An observed finite number is the least original cap bound at that value. -/
theorem profile_minimal (valid : Guard → Prop) (value : Value Symbol Guard) (actual : Nat)
    (computed : profile valid value = some actual) (depth : Nat) : Cap valid depth value ↔ actual ≤ depth := by
  rw [← within_iff_cap valid depth value, computed, Within]

/-- Complete actual child profiles are exactly the finite caps of the ordered values. -/
theorem children_iff_caps (valid : Guard → Prop) (depth : Nat) (values : List (Value Symbol Guard)) :
    Within depth (children valid values) ↔ ∀ value ∈ values, Cap valid depth value := by
  simp only [children_within, within_iff_cap]

/-- Complete actual row profiles are exactly the original finite row caps. -/
theorem rows_iff_caps (valid : Guard → Prop) (depth : Nat) (edges : List (EdgeValue Symbol Guard)) :
    Within depth (rows valid edges) ↔ ∀ edge ∈ edges, SourceCurrentConstrainedCap.Edge valid depth edge := by
  cases depth with
  | zero =>
      rw [rows_within_zero]
      constructor
      · rintro ⟨guards, children⟩ edge member
        exact ⟨guards edge member, fun child present => (zero_iff_annotated valid child).mp
          (children child (List.mem_flatMap.mpr ⟨edge, member, present⟩))⟩
      · intro bounded
        refine ⟨fun edge member => (bounded edge member).1, ?_⟩
        intro child member
        obtain ⟨edge, present, inside⟩ := List.mem_flatMap.mp member
        exact (zero_iff_annotated valid child).mpr ((bounded edge present).2 child inside)
  | succ depth =>
      rw [rows_within_succ]
      constructor
      · intro children edge member child present
        exact cap_of_profile valid depth child (children child (List.mem_flatMap.mpr ⟨edge, member, present⟩))
      · intro bounded child member
        obtain ⟨edge, present, inside⟩ := List.mem_flatMap.mp member
        exact profile_of_cap (bounded edge present child inside)

/-- Actual ordinary node work derives its returned guard-depth bound from its original row profiles. -/
theorem makeNode [DecidableEq (EdgeKey Symbol Guard)] (valid : Guard → Prop) (depth : Nat)
    (edges : List (EdgeValue Symbol Guard)) (state : State Symbol Guard) (coherent : Coherent state)
    (linked : Linked state) (resident : ∀ edge ∈ edges, EdgeResident state edge)
    (profiles : Within depth (rows valid edges)) :
    Within depth (profile valid (run (InternedConstructorTemplates.makeNode edges) state).1) :=
  profile_of_cap (SourceCurrentConstrainedCap.makeNode valid depth edges state coherent linked resident
    ((rows_iff_caps valid depth edges).mp profiles))

/-- Actual ordinary edge work derives its returned row profile from literal guards and child profiles. -/
theorem makeEdge [DecidableEq (EdgeKey Symbol Guard)] (valid : Guard → Prop) (depth : Nat)
    (symbol : Symbol) (guard : Guard) (values : List (Value Symbol Guard)) (state : State Symbol Guard)
    (coherent : Coherent state) (cached : Cached state) (available : ∀ value ∈ values, Available state value)
    (guardValid : depth = 0 → valid guard) (profiles : Within (depth - 1) (children valid values)) :
    Within depth (rows valid [(run (InternedConstructorTemplates.makeEdge symbol guard values) state).1]) := by
  apply (rows_iff_caps valid depth _).mpr
  intro edge member
  cases List.mem_singleton.mp member
  exact SourceCurrentConstrainedCap.makeEdge valid depth symbol guard values state coherent cached available guardValid
    ((children_iff_caps valid (depth - 1) values).mp profiles)

/-- Actual union work derives its returned profile from the original ordered member profiles. -/
theorem makeUnion [DecidableEq (EdgeKey Symbol Guard)] (valid : Guard → Prop) (depth : Nat)
    (values : List (Value Symbol Guard)) (state : State Symbol Guard) (facts : Facts state)
    (available : ∀ value ∈ values, Available state value) (profiles : Within depth (children valid values)) :
    Within depth (profile valid (run (InternedConstructorTemplates.makeUnion values) state).1) :=
  profile_of_cap (SourceCurrentConstrainedCap.makeUnion valid depth values state facts available
    ((children_iff_caps valid depth values).mp profiles))

end MicroCFTA.SourceCurrentConstrainedCapGuardDepth
