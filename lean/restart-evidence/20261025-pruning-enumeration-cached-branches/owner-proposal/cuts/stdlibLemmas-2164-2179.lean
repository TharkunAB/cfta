theorem flatMap_assoc {l : List α} {f : α → List β} {g : β → List γ} :
    (l.flatMap f).flatMap g = l.flatMap fun x => (f x).flatMap g := by
  induction l <;> simp [*]

theorem map_flatMap {f : β → γ} {g : α → List β} :
    ∀ {l : List α}, (l.flatMap g).map f = l.flatMap fun a => (g a).map f
  | [] => rfl
  | a::l => by simp only [flatMap_cons, map_append, map_flatMap]

theorem flatMap_map (f : α → β) (g : β → List γ) (l : List α) :
    (map f l).flatMap g = l.flatMap (fun a => g (f a)) := by
  induction l <;> simp [flatMap_cons, *]

theorem map_eq_flatMap {f : α → β} {l : List α} : map f l = l.flatMap fun x => [f x] := by
  simp only [← map_singleton]
  rw [← flatMap_singleton' l, map_flatMap, flatMap_singleton']
