import MicroCFTA.IntersectSchedule

/-!
# Extensional domains in the recursive schedule

Canonical source maps and overwrite lists can have different storage orders.
The schedule observes only lookup, free-map emptiness, and cutoff membership.
These observations determine exact execution at every finite bound.
-/
namespace MicroCFTA.IntersectSchedule
open Language Binding BinderLanguage

/-- Equal domain observations retain every semantic branch and recursive lookup. -/
structure DomainEquivalent (before after : Domain) : Prop where
  lookup : ∀ name, IntersectSchedule.lookup before name = IntersectSchedule.lookup after name
  seen : ∀ key, key ∈ before.seen ↔ key ∈ after.seen

/-- A source free map is empty exactly when every lookup is absent. -/
theorem lookup_empty_iff (domain : Domain) : domain.free.isEmpty = true ↔ ∀ name, lookup domain name = none := by
  constructor
  · intro empty name
    have empty := List.isEmpty_iff.mp empty
    simp [lookup, empty]
  · intro absent
    cases found : domain.free with
    | nil => rfl
    | cons first rest =>
        have impossible := absent first.1
        simp [lookup, found] at impossible

/-- Lookup equivalence also determines the source reset emptiness test. -/
theorem DomainEquivalent.empty (before after : Domain) (same : DomainEquivalent before after) :
    before.free.isEmpty = after.free.isEmpty := by
  apply Bool.eq_iff_iff.mpr
  rw [lookup_empty_iff, lookup_empty_iff]
  constructor
  · intro absent name; rw [← same.lookup name]; exact absent name
  · intro absent name; rw [same.lookup name]; exact absent name

/-- Prefixing the same actual entries retains equivalent underlying lookups. -/
theorem lookup_prefix_congr (entries : List (Nat × Input)) (before after : Domain)
    (same : ∀ name, lookup before name = lookup after name) (name : Nat) :
    lookup ⟨entries ++ before.free, before.seen⟩ name = lookup ⟨entries ++ after.free, after.seen⟩ name := by
  induction entries with
  | nil => exact same name
  | cons entry rest ih =>
      simp only [lookup] at ih
      simp only [List.cons_append, lookup, List.find?_cons]
      cases (entry.1 == name) <;> simp_all

/-- The same source extension retains all equivalent domain observations. -/
theorem DomainEquivalent.extend (before after : Domain) (same : DomainEquivalent before after)
    (entries : List (Nat × Input)) (key : Pair) : DomainEquivalent (extend before entries key) (extend after entries key) := by
  constructor
  · exact lookup_prefix_congr entries.reverse before after same.lookup
  · intro next
    simp only [IntersectSchedule.extend, List.mem_cons, same.seen]

/-- Equal recursive callbacks give exactly equal ordered source traversals. -/
theorem walk_congr (before after : A → Except Error B) (inputs : List A) (same : ∀ input, before input = after input) :
    walk before inputs = walk after inputs := congrArg (fun action => walk action inputs) (funext same)

/-- Equivalent domain observations determine both source workers at each finite bound. -/
theorem domain_equivalent_workers [DecidableEq Symbol] (view : View Symbol) (fuel : Nat) :
    (∀ before after, DomainEquivalent before after → ∀ left right,
      run view fuel before left right = run view fuel after left right) ∧
    (∀ before after, DomainEquivalent before after → ∀ left right,
      edge view fuel before left right = edge view fuel after left right) := by
  induction fuel with
  | zero => exact ⟨by intros; rfl, by intros; rfl⟩
  | succ fuel ih =>
      constructor
      · intro before after same left right
        rw [run.eq_def view (fuel + 1) before left right, run.eq_def view (fuel + 1) after left right]
        simp only [same.empty before after, same.seen]
        split
        · rfl
        · split
          · rfl
          · split
            · rfl
            · split
              · exact ih.1 before after same right left
              · split
                · rfl
                · cases left <;> cases right <;> dsimp only <;> first
                  | rfl
                  | exact congrArg _ (ih.1 _ _ (same.extend before after _ _) _ _)
                  | exact congrArg _ (walk_congr _ _ _ (fun member => ih.1 before after same _ _))
                  | exact congrArg _ (walk_congr _ _ _ (fun rows => ih.2 before after same rows.1 rows.2))
                  | rw [same.lookup]; split <;> first | rfl | exact ih.1 before after same _ _
      · intro before after same left right
        rw [edge.eq_2 view before left right fuel, edge.eq_2 view after left right fuel]
        split
        · rfl
        · exact congrArg _ (walk_congr _ _ _ (fun children => ih.1 before after same children.1 children.2))

/-- Canonical and list-based domains have identical exact node execution. -/
theorem run_domain_equivalent [DecidableEq Symbol] (view : View Symbol) (fuel : Nat) (before after : Domain)
    (same : DomainEquivalent before after) (left right : Input) :
    run view fuel before left right = run view fuel after left right :=
  (domain_equivalent_workers view fuel).1 before after same left right

end MicroCFTA.IntersectSchedule
