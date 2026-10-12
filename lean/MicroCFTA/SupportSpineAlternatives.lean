import MicroCFTA.SupportSpine
import MicroCFTA.SupportClosing

/-!
# Alternative-preserving application-spine closing

A retained group can contain several private Apply roots. The source must
keep one child sequence per alternative. Concatenating those sequences into
one product would add crossed terms. Stopping at the group would keep Apply
nodes that the term callback removes.
-/
namespace MicroCFTA.SupportSpineAlternatives
open Language GeneratorCombinators BinderLanguage SupportGraph SupportTerms

/-- A left application spine can branch at an ordinary support node. -/
inductive Spine (Symbol : Type) where
  | pure
  | base (payload : Payload (Label Symbol)) (children : List (Support Symbol))
  | apply (functions : Spine Symbol) (argument : Support Symbol)
  | alternatives (spines : List (Spine Symbol))

/-- Bases exclude the private roots handled by the spine recognizer. -/
def Valid : Spine Symbol → Prop
  | .pure => True
  | .base payload _ => payload.label ≠ .pure ∧ payload.label ≠ .apply
  | .apply functions _ => Valid functions
  | .alternatives spines => ∀ spine ∈ spines, Valid spine

/-- Read the original support language, before any flattening. -/
def graph : Spine Symbol → Support Symbol
  | .pure => edge .pure []
  | .base payload children => .branch payload children
  | .apply functions argument => edge .apply [graph functions, argument]
  | .alternatives spines => .alternatives (spines.map graph)

/-- Preserve one complete ordered child sequence for each recognized alternative. -/
def prefixes : Spine Symbol → List (List (Support Symbol))
  | .pure => [[]]
  | .base payload children => [[.branch payload children]]
  | .apply functions argument => (prefixes functions).map (fun children => children ++ [argument])
  | .alternatives spines => spines.flatMap prefixes

/-- The alternate child sequences have exactly the term-side flattened forest language. -/
theorem prefixes_exact (environment : Env (Label Symbol)) (spine : Spine Symbol)
    (valid : Valid spine) (terms : List (Term (Label Symbol))) :
    (∃ children ∈ prefixes spine, forest environment children terms) ↔
      ∃ original, meaning environment (graph spine) original ∧ terms = applicationLeftChildren original := by
  induction spine using Spine.rec
    (motive_2 := fun spines => ∀ spine ∈ spines, Valid spine → ∀ terms,
      (∃ children ∈ prefixes spine, forest environment children terms) ↔
        ∃ original, meaning environment (graph spine) original ∧ terms = applicationLeftChildren original)
    generalizing terms with
  | pure =>
    simpa only [prefixes, List.mem_singleton, exists_eq_left, graph, SupportSpine.flatten, SupportSpine.graph]
      using SupportSpine.flatten_exact environment .pure trivial terms
  | base payload children =>
    simpa only [prefixes, List.mem_singleton, exists_eq_left, graph, SupportSpine.flatten, SupportSpine.graph]
      using SupportSpine.flatten_exact environment (.base payload children) (by simpa only [Valid, SupportSpine.Valid] using valid) terms
  | apply functions argument ih =>
    simp only [Valid] at valid
    simp only [prefixes, graph]
    constructor
    · rintro ⟨children, member, accepted⟩
      obtain ⟨initial, prefixMember, rfl⟩ := List.mem_map.mp member
      obtain ⟨first, second, firstAccepted, secondAccepted, rfl⟩ := (SupportSpine.forest_append environment initial [argument] terms).mp accepted
      obtain ⟨function, functionAccepted, rfl⟩ := (ih valid first).mp ⟨initial, prefixMember, firstAccepted⟩
      cases second with
      | nil => simp [forest] at secondAccepted
      | cons value rest =>
        simp only [forest] at secondAccepted
        have empty : rest = [] := by cases rest <;> simp_all [forest]
        subst rest
        refine ⟨.node .apply [function, value], ?_, ?_⟩
        · exact (SupportSpine.apply_exact environment _ _ _).mpr ⟨function, value, functionAccepted, secondAccepted.1, rfl⟩
        · simp [applicationLeftChildren, applicationTermChildren]
    · rintro ⟨original, accepted, rfl⟩
      obtain ⟨function, value, functionAccepted, valueAccepted, rfl⟩ := (SupportSpine.apply_exact environment _ _ original).mp accepted
      obtain ⟨initial, prefixMember, firstAccepted⟩ := (ih valid _).mpr ⟨function, functionAccepted, rfl⟩
      refine ⟨initial ++ [argument], List.mem_map.mpr ⟨initial, prefixMember, rfl⟩, ?_⟩
      apply (SupportSpine.forest_append environment initial [argument] _).mpr
      exact ⟨applicationLeftChildren function, [value], firstAccepted, by simp only [forest]; exact ⟨valueAccepted, trivial⟩,
        by simp [applicationLeftChildren, applicationTermChildren]⟩
  | alternatives spines ih =>
    simp only [Valid] at valid
    simp only [prefixes, graph]
    constructor
    · rintro ⟨children, member, accepted⟩
      obtain ⟨spine, spineMember, prefixMember⟩ := List.mem_flatMap.mp member
      obtain ⟨original, originalAccepted, same⟩ := (ih spine spineMember (valid spine spineMember) terms).mp ⟨children, prefixMember, accepted⟩
      refine ⟨original, ?_, same⟩
      apply (SupportClosing.alternatives_exact environment _ _).mpr
      exact ⟨_, List.mem_map.mpr ⟨spine, spineMember, rfl⟩, originalAccepted⟩
    · rintro ⟨original, accepted, same⟩
      obtain ⟨shape, member, originalAccepted⟩ := (SupportClosing.alternatives_exact environment _ original).mp accepted
      obtain ⟨spine, spineMember, rfl⟩ := List.mem_map.mp member
      obtain ⟨children, prefixMember, accepted⟩ := (ih spine spineMember (valid spine spineMember) terms).mpr ⟨original, originalAccepted, same⟩
      exact ⟨children, List.mem_flatMap.mpr ⟨spine, spineMember, prefixMember⟩, accepted⟩
  | nil => rename_i spine member valid terms; simp at member
  | cons first rest ih ir =>
    rename_i spine member valid terms
    rcases List.mem_cons.mp member with rfl | member
    · exact ih valid terms
    · exact ir spine member valid terms

/-- Emit one labelled root per correlated argument sequence. -/
def close (symbol : Symbol) (functions : Spine Symbol) (argument : Support Symbol) : Support Symbol :=
  .alternatives ((prefixes functions).map (fun children => edge (.user symbol) (children ++ [argument])))

/-- The repaired multi-spine graph accepts exactly the source callback's closed terms. -/
theorem close_exact (environment : Env (Label Symbol)) (symbol : Symbol)
    (functions : Spine Symbol) (argument : Support Symbol) (valid : Valid functions)
    (term : Term (Label Symbol)) :
    meaning environment (close symbol functions argument) term ↔
      ∃ original, meaning environment (graph (.apply functions argument)) original ∧ term = labelTerm symbol original := by
  simp only [close, SupportClosing.alternatives_exact]
  constructor
  · rintro ⟨shape, member, accepted⟩
    obtain ⟨initial, prefixMember, rfl⟩ := List.mem_map.mp member
    simp only [edge, meaning] at accepted
    obtain ⟨children, rfl, childrenAccepted, _⟩ := accepted
    have member : initial ++ [argument] ∈ prefixes (.apply functions argument) := by
      simp only [prefixes]
      exact List.mem_map.mpr ⟨initial, prefixMember, rfl⟩
    obtain ⟨original, originalAccepted, same⟩ := (prefixes_exact environment (.apply functions argument) (by simpa only [Valid] using valid) children).mp ⟨_, member, childrenAccepted⟩
    have parsed := originalAccepted
    simp only [graph] at parsed
    obtain ⟨function, value, _, _, shape⟩ := (SupportSpine.apply_exact environment _ _ original).mp parsed
    refine ⟨original, originalAccepted, ?_⟩
    subst original
    simp_all [labelTerm, applicationLeftChildren, applicationTermChildren]
  · rintro ⟨original, accepted, rfl⟩
    have flattened := (prefixes_exact environment (.apply functions argument) (by simpa only [Valid] using valid) _).mpr ⟨original, accepted, rfl⟩
    obtain ⟨children, member, childrenAccepted⟩ := flattened
    simp only [prefixes] at member
    obtain ⟨initial, prefixMember, rfl⟩ := List.mem_map.mp member
    simp only [graph] at accepted
    obtain ⟨function, value, _, _, rfl⟩ := (SupportSpine.apply_exact environment _ _ original).mp accepted
    refine ⟨_, List.mem_map.mpr ⟨initial, prefixMember, rfl⟩, ?_⟩
    simp only [edge, meaning, labelTerm, applicationTermChildren, Option.getD_some]
    refine ⟨_, rfl, ?_, trivial⟩
    simpa [applicationLeftChildren, applicationTermChildren] using childrenAccepted

/-- A concrete indexed leaf used by retained grouped applications. -/
def atom (index : Nat) : Support Nat := singleton (.node (.index index) [])

/-- Each alternative retains two equal children as one sequence. -/
def correlated : Spine Nat := .alternatives
  [.apply (.apply .pure (atom 0)) (atom 0), .apply (.apply .pure (atom 1)) (atom 1)]

/-- The repaired graph contains an original pair followed by the new argument. -/
theorem repaired_pair (environment : Env (Label Nat)) :
    meaning environment (close 7 correlated (atom 2))
      (.node (.user 7) [.node (.index 0) [], .node (.index 0) [], .node (.index 2) []]) := by
  simp [close, prefixes, correlated, atom, SupportClosing.alternatives_exact,
    edge, meaning, forest, singleton_exact]

/-- Keeping each child sequence intact prevents crossed pairs. -/
theorem no_crossed_pair (environment : Env (Label Nat)) :
    ¬meaning environment (close 7 correlated (atom 2))
      (.node (.user 7) [.node (.index 0) [], .node (.index 1) [], .node (.index 2) []]) := by
  simp [close, prefixes, correlated, atom, SupportClosing.alternatives_exact,
    edge, meaning, forest, singleton_exact]

/-- The former opaque-left fallback drops the same valid pair. -/
theorem old_spine_loses_pair (environment : Env (Label Nat)) :
    ¬meaning environment (edge (.user 7) [graph correlated, atom 2])
      (.node (.user 7) [.node (.index 0) [], .node (.index 0) [], .node (.index 2) []]) := by
  simp [edge, meaning, forest]

end MicroCFTA.SupportSpineAlternatives
