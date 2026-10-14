import MicroCFTA.InternedGuardedLanguage
import MicroCFTA.InternedNormalizationFree

/-!
# Actual free-name metadata bounds independent guarded meaning

Coherent available records have exact free-name metadata. The independent
guarded interpretation therefore reads only those names. Closed captures
retain the same language under every ambient reference environment.
-/
namespace MicroCFTA.InternedGuardedLanguage
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedBinderProtocol Language

/-- A stored child is structurally smaller than its complete source edge. -/
theorem edge_child_size (edge : EdgeValue Symbol Guard) (child : Value Symbol Guard) (member : child ∈ edge.children) :
    sizeOf child < sizeOf edge := by
  cases edge with
  | mk entry children =>
      have smaller := List.sizeOf_lt_of_mem member
      simp only [EdgeValue.children] at smaller
      simp_wf
      omega

/-- Equal child languages retain exactly the same ordered accepting forest. -/
theorem forest_congr (holds : Guard → Term Symbol → Bool) (before after : Env Symbol)
    (children : List (Value Symbol Guard)) (same : ∀ child ∈ children, meaning holds before child = meaning holds after child)
    (terms : List (Term Symbol)) : forest holds before children terms ↔ forest holds after children terms := by
  induction children generalizing terms with
  | nil => cases terms <;> simp only [forest]
  | cons child rest ih =>
      cases terms with
      | nil => simp only [forest]
      | cons term terms =>
          simp only [forest]
          exact and_congr (iff_of_eq (congrFun (same child List.mem_cons_self) term))
            (ih (fun child member => same child (List.mem_cons_of_mem _ member)) terms)

/-- Equal child languages retain the edge's complete guard and source symbol. -/
theorem edgeMeaning_congr (holds : Guard → Term Symbol → Bool) (before after : Env Symbol)
    (edge : EdgeValue Symbol Guard) (same : ∀ child ∈ edge.children, meaning holds before child = meaning holds after child) :
    edgeMeaning holds before edge = edgeMeaning holds after edge := by
  cases edge with
  | mk entry children =>
      funext term
      simp only [edgeMeaning]
      apply propext
      exact exists_congr (fun terms => and_congr Iff.rfl (and_congr (forest_congr holds before after children same terms) Iff.rfl))

/-- Actual coherent free-name metadata contains every ambient name that the guarded language can read. -/
theorem meaning_free (holds : Guard → Term Symbol → Bool) (value : Value Symbol Guard)
    (state : State Symbol Guard) (coherent : Coherent state) (available : Available state value) (before after : Env Symbol)
    (agree : ∀ name ∈ value.free, before name = after name) : meaning holds before value = meaning holds after value := by
  cases value with
  | empty => simp only [meaning]
  | reference name => simpa only [meaning] using agree name (by simp [Value.free])
  | node entry edges depth free =>
      rw [meaning, meaning]
      funext term
      apply propext
      apply exists_congr
      intro edge
      have each (child : Value Symbol Guard) (childIn : child ∈ edge.val.children) :
          meaning holds before child = meaning holds after child := by
        have edgeSmall := List.sizeOf_lt_of_mem edge.property
        have childSmall := edge_child_size edge.val child childIn
        apply meaning_free holds child state coherent (available.children child (List.mem_flatMap.mpr ⟨edge.val, edge.property, childIn⟩)) before after
        intro name present
        apply agree name
        change name ∈ free
        rw [InternedNormalizationFree.node_free state coherent entry edges depth free available.resident]
        exact (childFree_member _ name).mpr ⟨child, List.mem_flatMap.mpr ⟨edge.val, edge.property, childIn⟩, present⟩
      exact iff_of_eq (congrFun (edgeMeaning_congr holds before after edge.val each) term)
  | union entry members depth free =>
      rw [meaning, meaning]
      funext term
      apply propext
      apply exists_congr
      intro member
      have smaller := List.sizeOf_lt_of_mem member.property
      apply iff_of_eq
      apply congrFun
      apply meaning_free holds member.val state coherent (available.children member.val member.property) before after
      intro name present
      apply agree name
      change name ∈ free
      rw [InternedNormalizationFree.union_free state coherent entry members depth free available.resident]
      exact (childFree_member _ name).mpr ⟨member.val, member.property, present⟩
  | mu entry body depth ordinary =>
      rw [meaning, meaning]
      apply BinderLanguage.least_congr
      intro language term
      apply iff_of_eq
      apply congrFun
      apply meaning_free holds body state coherent (available.children body (by simp [children]))
      intro name present
      by_cases same : name = .interned entry.identity
      · simp only [bind, same, ↓reduceIte]
      · have parent : name ∈ (Value.mu entry body depth ordinary).free := by simp [Value.free, present, same]
        simpa only [bind, same, ↓reduceIte] using agree name parent
termination_by sizeOf value
decreasing_by all_goals simp_wf; all_goals simp_all only; all_goals simp_wf; all_goals omega

/-- A closed coherent stored value has the same guarded language in every ambient environment. -/
theorem closed_meaning (holds : Guard → Term Symbol → Bool) (value : Value Symbol Guard)
    (state : State Symbol Guard) (coherent : Coherent state) (available : Available state value) (closed : value.free = [])
    (before after : Env Symbol) : meaning holds before value = meaning holds after value :=
  meaning_free holds value state coherent available before after (by intro name member; simp [closed] at member)

end MicroCFTA.InternedGuardedLanguage
