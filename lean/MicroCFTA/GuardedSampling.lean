import MicroCFTA.ObservationMass
import MicroCFTA.ObservationGraph

/-!
# Refinement observations, unknown errors, and sampling

Concrete guard observation keys determine the evaluator verdict. Compilation
partitions weighted terms by these keys, queries once per group, rejects
unknown results, and constructs the final decoder and sampler record.
-/

namespace MicroCFTA.GuardedSampling
open Language Probability SizeMass MassRetention Observation ObservationMass

abbrev AnnotatedTerm (Symbol Refinement : Type) := Term (Observation.Label Symbol Refinement)

/-- Read exactly the complete finite observation key required by the guard. -/
def parts [DecidableEq Symbol] [DecidableEq Refinement]
    (guard : Guards.Guard (Atom Refinement)) (members : Distribution (AnnotatedTerm Symbol Refinement)) :
    List (Group (AnnotatedTerm Symbol Refinement)) := splitClass (fun entry => key guard entry.2) members

/-- One exact representative decision is sufficient for a key-homogeneous bucket. -/
def decision (queries : Queries Refinement) (guard : Guards.Guard (Atom Refinement))
    (group : Group (AnnotatedTerm Symbol Refinement)) : Guards.Verdict :=
  match group.weights with
  | [] => .no
  | first :: _ => verdict queries guard first.2

/-- The member-level admission predicate retains only proved guard results. -/
def proved (queries : Queries Refinement) (guard : Guards.Guard (Atom Refinement))
    (term : AnnotatedTerm Symbol Refinement) : Bool := decide (verdict queries guard term = .yes)

/-- The group-level decision uses exactly the same Boolean test as weighted filtering. -/
theorem decision_proved (queries : Queries Refinement) (guard : Guards.Guard (Atom Refinement))
    (group : Group (AnnotatedTerm Symbol Refinement)) :
    decide (decision queries guard group = .yes) = accepted (proved queries guard) group := by
  cases shape : group.weights <;> simp [decision, accepted, proved, shape]

/-- A group's concrete key proves that every member has its representative's verdict. -/
theorem decision_exact [DecidableEq Symbol] [DecidableEq Refinement]
    (queries : Queries Refinement) (guard : Guards.Guard (Atom Refinement))
    (members : Distribution (AnnotatedTerm Symbol Refinement)) (group : Group (AnnotatedTerm Symbol Refinement))
    (present : group ∈ parts guard members) (entry : Rat × AnnotatedTerm Symbol Refinement)
    (member : entry ∈ group.weights) : decision queries guard group = verdict queries guard entry.2 := by
  obtain ⟨observed, same⟩ := split_uniform (key guard) members group present
  cases shape : group.weights with
  | nil => simp [shape] at member
  | cons first rest =>
      have firstMember : first ∈ group.weights := by simp [shape]
      have keys := (same first firstMember).trans (same entry member).symm
      exact (by simpa [decision, shape] using key_homogeneous queries guard first.2 entry.2 keys true)

/-- The compiler returns an explicit error on unknown, otherwise a complete merged record. -/
def compile [DecidableEq Symbol] [DecidableEq Refinement]
    (queries : Queries Refinement) (guard : Guards.Guard (Atom Refinement))
    (members : Distribution (AnnotatedTerm Symbol Refinement)) :
    Option (SamplerReplay.Record (AnnotatedTerm Symbol Refinement)) :=
  (ObservationGraph.selectDecided (decision queries guard) (parts guard members)).map mergeRecord

/-- Every successful selection retains the exact weighted multiset of proved original members. -/
theorem selected_expansion [DecidableEq Symbol] [DecidableEq Refinement]
    (queries : Queries Refinement) (guard : Guards.Guard (Atom Refinement))
    (members : Distribution (AnnotatedTerm Symbol Refinement))
    (positive : ∀ entry ∈ members, 0 < entry.1) (kept : List (Group (AnnotatedTerm Symbol Refinement)))
    (success : ObservationGraph.selectDecided (decision queries guard) (parts guard members) = some kept) :
    (kept.flatMap expand).Perm (restrict (proved queries guard) members) := by
  rw [ObservationGraph.selectDecided_eq_filter _ _ _ success]
  simp only [decision_proved]
  rw [filter_expansion]
  · exact (split_expansion (key guard) members positive).filter _
  · intro group present
    exact (splitClass_valid _ members positive group present).2.1
  · intro group present
    refine ⟨decide (decision queries guard group = .yes), ?_⟩
    intro entry member
    simp only [proved, ← decision_exact queries guard members group present entry member]

/-- Selected buckets retain all required positive mass and count invariants. -/
theorem selected_live [DecidableEq Symbol] [DecidableEq Refinement]
    (queries : Queries Refinement) (guard : Guards.Guard (Atom Refinement))
    (members : Distribution (AnnotatedTerm Symbol Refinement))
    (positive : ∀ entry ∈ members, 0 < entry.1) (kept : List (Group (AnnotatedTerm Symbol Refinement)))
    (success : ObservationGraph.selectDecided (decision queries guard) (parts guard members) = some kept) :
    SamplerReplay.LiveValid (mergeRecord kept) := by
  apply mergeRecord_live
  · intro group present
    have original := ((ObservationGraph.mem_selectDecided _ _ _ success group).mp present).1
    exact splitClass_valid _ members positive group original
  · intro group present
    have original := ((ObservationGraph.mem_selectDecided _ _ _ success group).mp present).1
    exact split_positive (key guard) members positive group original

/-- Successful compiler sampling is the original distribution conditioned on the complete-term guard verdict. -/
theorem selected_distribution [DecidableEq Symbol] [DecidableEq Refinement]
    (queries : Queries Refinement) (guard : Guards.Guard (Atom Refinement))
    (members : Distribution (AnnotatedTerm Symbol Refinement))
    (positive : ∀ entry ∈ members, 0 < entry.1) (kept : List (Group (AnnotatedTerm Symbol Refinement)))
    (success : ObservationGraph.selectDecided (decision queries guard) (parts guard members) = some kept)
    (event : AnnotatedTerm Symbol Refinement → Bool) :
    eventMass event (mergeRecord kept).sampling.values = eventMass event (condition (proved queries guard) members) := by
  have valid : ∀ group ∈ kept, ValidGroup group := by
    intro group present
    exact splitClass_valid _ members positive group
      (((ObservationGraph.mem_selectDecided _ _ _ success group).mp present).1)
  rw [mergeRecord_distribution kept valid, sampler_expansion kept valid]
  exact normalized_perm_event event (selected_expansion queries guard members positive kept success)

/-- Successful compiler ranks cover precisely every occurrence admitted by the complete-term guard. -/
theorem selected_members [DecidableEq Symbol] [DecidableEq Refinement]
    (queries : Queries Refinement) (guard : Guards.Guard (Atom Refinement))
    (members : Distribution (AnnotatedTerm Symbol Refinement))
    (positive : ∀ entry ∈ members, 0 < entry.1) (kept : List (Group (AnnotatedTerm Symbol Refinement)))
    (success : ObservationGraph.selectDecided (decision queries guard) (parts guard members) = some kept) :
    (Decoder.values (mergeRecord kept).plan).Perm ((restrict (proved queries guard) members).map Prod.snd) := by
  have projection := (selected_expansion queries guard members positive kept success).map Prod.snd
  simpa [mergeRecord, SamplerReplay.manyRecord, SamplerReplay.manyPlan_values,
    SamplerReplay.source, Decoder.values, List.flatMap_map, List.map_flatMap,
    expand, scale, List.map_map, Function.comp_def] using projection

/-- All output records of the compiler satisfy its probability, decoder replay, and positive coverage invariants. -/
theorem compile_live [DecidableEq Symbol] [DecidableEq Refinement]
    (queries : Queries Refinement) (guard : Guards.Guard (Atom Refinement))
    (members : Distribution (AnnotatedTerm Symbol Refinement)) (positive : ∀ entry ∈ members, 0 < entry.1)
    (record : SamplerReplay.Record (AnnotatedTerm Symbol Refinement))
    (success : compile queries guard members = some record) : SamplerReplay.LiveValid record := by
  obtain ⟨kept, selected, same⟩ := Option.map_eq_some_iff.mp success
  subst record
  exact selected_live queries guard members positive kept selected

/-- The actual decision loop fails exactly when any candidate group remains unknown. -/
theorem select_unknown (query : α → Guards.Verdict) (members : List α) :
    ObservationGraph.selectDecided query members = none ↔ ∃ member ∈ members, query member = .unknown := by
  induction members with
  | nil => simp [ObservationGraph.selectDecided]
  | cons first rest ih =>
      cases answer : query first <;> simp [ObservationGraph.selectDecided, answer, ih]

/-- A source term whose guard is unknown makes compilation fail instead of removing the term. -/
theorem unknown_is_error [DecidableEq Symbol] [DecidableEq Refinement]
    (queries : Queries Refinement) (guard : Guards.Guard (Atom Refinement))
    (members : Distribution (AnnotatedTerm Symbol Refinement)) (positive : ∀ entry ∈ members, 0 < entry.1)
    (entry : Rat × AnnotatedTerm Symbol Refinement) (present : entry ∈ members)
    (unknown : verdict queries guard entry.2 = .unknown) : compile queries guard members = none := by
  have expanded := (split_expansion (key guard) members positive).mem_iff.mpr present
  obtain ⟨group, member, belongs⟩ := List.mem_flatMap.mp expanded
  obtain ⟨original, originalMember, same⟩ := List.mem_map.mp belongs
  have sameTerm : original.2 = entry.2 := by
    have projected := congrArg (fun pair : Rat × AnnotatedTerm Symbol Refinement => pair.2) same
    simpa only using projected
  have decisionUnknown : decision queries guard group = .unknown := by
    rw [decision_exact queries guard members group member original originalMember, sameTerm, unknown]
  have failure := (select_unknown (decision queries guard) (parts guard members)).mpr
    ⟨group, member, decisionUnknown⟩
  simp [compile, failure]

/-- A proved source term occurs in the original weighted language and has a `Yes` guard verdict. -/
def Admitted (queries : Queries Refinement) (guard : Guards.Guard (Atom Refinement))
    (members : Distribution (AnnotatedTerm Symbol Refinement)) (term : AnnotatedTerm Symbol Refinement) : Prop :=
  term ∈ members.map Prod.snd ∧ verdict queries guard term = .yes

/-- Filtering term observations preserves uniqueness when the input rank domain consists of distinct terms. -/
theorem selected_nodup [DecidableEq Symbol] [DecidableEq Refinement]
    (queries : Queries Refinement) (guard : Guards.Guard (Atom Refinement))
    (members : Distribution (AnnotatedTerm Symbol Refinement)) (positive : ∀ entry ∈ members, 0 < entry.1)
    (distinct : (members.map Prod.snd).Nodup) (kept : List (Group (AnnotatedTerm Symbol Refinement)))
    (success : ObservationGraph.selectDecided (decision queries guard) (parts guard members) = some kept) :
    (Decoder.values (mergeRecord kept).plan).Nodup := by
  have perm := selected_members queries guard members positive kept success
  apply perm.nodup_iff.mpr
  have same : (restrict (proved queries guard) members).map Prod.snd =
      (members.map Prod.snd).filter (proved queries guard) := by simp [restrict, List.filter_map, Function.comp_def]
  rw [same]
  exact distinct.filter _

/-- Successful compilation builds a distinct-term index from its own decoder member list. -/
def selectedIndex [DecidableEq Symbol] [DecidableEq Refinement]
    (queries : Queries Refinement) (guard : Guards.Guard (Atom Refinement))
    (members : Distribution (AnnotatedTerm Symbol Refinement)) (positive : ∀ entry ∈ members, 0 < entry.1)
    (distinct : (members.map Prod.snd).Nodup) (kept : List (Group (AnnotatedTerm Symbol Refinement)))
    (success : ObservationGraph.selectDecided (decision queries guard) (parts guard members) = some kept) :
    DistinctRank.Index (Admitted queries guard members) where
  members := Decoder.values (mergeRecord kept).plan
  nodup := selected_nodup queries guard members positive distinct kept success
  exact := by
    intro term
    rw [(selected_members queries guard members positive kept success).mem_iff]
    have same : (restrict (proved queries guard) members).map Prod.snd =
        (members.map Prod.snd).filter (proved queries guard) := by simp [restrict, List.filter_map, Function.comp_def]
    rw [same]
    simp [Admitted, proved]

/-- The compiled decoder is exactly the distinct-language decoder on every valid index. -/
theorem decoder_selectedIndex [DecidableEq Symbol] [DecidableEq Refinement]
    (queries : Queries Refinement) (guard : Guards.Guard (Atom Refinement))
    (members : Distribution (AnnotatedTerm Symbol Refinement)) (positive : ∀ entry ∈ members, 0 < entry.1)
    (distinct : (members.map Prod.snd).Nodup) (kept : List (Group (AnnotatedTerm Symbol Refinement)))
    (success : ObservationGraph.selectDecided (decision queries guard) (parts guard members) = some kept)
    (rank : Fin (selectedIndex queries guard members positive distinct kept success).count) :
    Decoder.decode (mergeRecord kept).plan rank.val =
      some ((selectedIndex queries guard members positive distinct kept success).decode rank).val := by
  rw [Decoder.decode_correct]
  exact List.getElem?_eq_getElem rank.isLt

/-- The compiler's cardinality is exactly the size of the constructed distinct-term rank interval. -/
theorem count_selectedIndex [DecidableEq Symbol] [DecidableEq Refinement]
    (queries : Queries Refinement) (guard : Guards.Guard (Atom Refinement))
    (members : Distribution (AnnotatedTerm Symbol Refinement)) (positive : ∀ entry ∈ members, 0 < entry.1)
    (distinct : (members.map Prod.snd).Nodup) (kept : List (Group (AnnotatedTerm Symbol Refinement)))
    (success : ObservationGraph.selectDecided (decision queries guard) (parts guard members) = some kept) :
    Decoder.count (mergeRecord kept).plan = (selectedIndex queries guard members positive distinct kept success).count :=
  Decoder.count_correct _

end MicroCFTA.GuardedSampling
