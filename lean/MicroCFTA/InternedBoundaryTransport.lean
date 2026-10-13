import MicroCFTA.InternedUnionAlternativeClear

/-!
# Forbidden-boundary transport through root unions

A target sentinel can equal an unchanged captured reference. The target
filter can then delete an additional alternative. This cannot introduce
a forbidden boundary. Only forward mapping of the selected local is
required; reflection in the reverse direction is unnecessary.
-/
namespace MicroCFTA.InternedBoundaryTransport
open InternedConstructorTemplates InternedProbeProvenance InternedNestedFacts InternedNestedProvenance
open InternedObservedAbsence InternedOccurrenceObservations InternedBoundaryAtoms InternedLiveEdges
open InternedUnionNormalForm InternedUnionAlternativeClear
open InternedBinderProtocol (Reference NodeRef)

/-- Clear flattened inputs give a clear actual union result through every normalization branch. -/
theorem makeUnion_clear [DecidableEq (EdgeKey Symbol Guard)] (forbidden : NodeRef → Prop)
    (values : List (Value Symbol Guard)) (state : State Symbol Guard) (facts : Facts state) (live : Live state)
    (inputs : Values state values) (clear : ∀ value ∈ values.flatMap unionMembers, Clear forbidden value) :
    Clear forbidden (run (makeUnion values) state).1 := by
  intro atom present
  obtain ⟨source, included, boundary⟩ := (makeUnion_atom_iff values state facts.coherent facts.cached facts.linked live inputs atom).mp present
  obtain ⟨value, member, boundary⟩ := (flatten_atom source atom).mp boundary
  exact clear value (List.mem_flatMap.mpr ⟨source, included, member⟩) atom boundary

/-- Actual root filtering cannot introduce a boundary that was absent in its original available value. -/
theorem filter_clear [DecidableEq (EdgeKey Symbol Guard)] (forbidden : NodeRef → Prop) (name : Reference)
    (value : Value Symbol Guard) (state : State Symbol Guard) (facts : Facts state) (live : Live state)
    (available : Available state value) (clear : Clear forbidden value) :
    Clear forbidden (run (withoutSelfReference name value) state).1 := by
  cases value <;> simp only [withoutSelfReference, run] <;> try exact clear
  case union entry members depth free =>
    split
    · intro atom present
      obtain ⟨value, included, boundary⟩ := (makeUnion_atom_iff _ state facts.coherent facts.cached facts.linked live
        (fun child member => available.children child (List.mem_filter.mp member).1) atom).mp present
      exact clear atom (by simpa only [atoms] using
        (many_member members atom).mpr ⟨value, (List.mem_filter.mp included).1, boundary⟩)
    · exact clear

/-- Clear retained alternatives map to clear target alternatives, including aliases of the target sentinel. -/
theorem alternatives_clear (forbidden : NodeRef → Prop) (firstName secondName : Reference)
    (allowed : ¬ forbidden (.ref secondName)) (first second : List (Value Symbol Guard))
    (paired : Paired (fun a b => Related forbidden a b ∧ (a = .reference firstName → b = .reference secondName)) first second)
    (clear : ∀ value ∈ first, value ≠ .reference firstName → Clear forbidden value) :
    ∀ value ∈ second, Clear forbidden value := by
  induction paired with
  | nil => intro value impossible; cases impossible
  | @cons a b first second related paired ih =>
      intro value member
      rcases List.mem_cons.mp member with same | member
      · subst value
        by_cases selected : a = .reference firstName
        · rw [related.2 selected]
          intro atom included
          have same : atom = .ref secondName := by simpa only [atoms, List.mem_singleton] using included
          exact same ▸ allowed
        · have absent := clear a List.mem_cons_self selected
          exact related.1.2 absent ▸ absent
      · exact ih (fun child included => clear child (List.mem_cons_of_mem _ included)) value member

/-- Actual union construction and self filtering transport boundary absence to an allowed sentinel despite capture aliases. -/
theorem union_filter_clear [DecidableEq (EdgeKey Symbol Guard)] (forbidden : NodeRef → Prop)
    (firstName secondName : Reference) (allowed : ¬ forbidden (.ref secondName))
    (first second : List (Value Symbol Guard)) (left right : State Symbol Guard)
    (lf : Facts left) (rf : Facts right) (lflat : Flat left) (ll : Live left) (rl : Live right)
    (li : Values left first) (ri : Values right second)
    (paired : Paired (fun a b => Related forbidden a b ∧ (a = .reference firstName → b = .reference secondName))
      (first.flatMap unionMembers) (second.flatMap unionMembers))
    (clear : Clear forbidden (run (withoutSelfReference firstName (run (makeUnion first) left).1)
      (run (makeUnion first) left).2).1) :
    Clear forbidden (run (withoutSelfReference secondName (run (makeUnion second) right).1)
      (run (makeUnion second) right).2).1 := by
  have firstAlternatives := clear_alternative forbidden firstName first left lf lflat ll li clear
  have target := alternatives_clear forbidden firstName secondName allowed _ _ paired firstAlternatives
  have original := makeUnion_clear forbidden second right rf rl ri target
  have checked := union_verified second right rf ri
  exact filter_clear forbidden secondName _ _ checked.facts (makeUnion_live second right rl)
    (checked.result _ _ rfl) original

end MicroCFTA.InternedBoundaryTransport
