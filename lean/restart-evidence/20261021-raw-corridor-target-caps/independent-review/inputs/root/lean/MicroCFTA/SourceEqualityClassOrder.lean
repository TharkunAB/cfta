import MicroCFTA.SourceListSort
import MicroCFTA.EqualitySource

/-!
# Physical source class ordering

Each class retains its trie and ascending path-set enumeration. The source
comparator checks strict trie subsumption in both directions, then compares
the path sets in reverse order. Raw class lists need no comparator law.
-/
namespace MicroCFTA.SourceEqualityClassOrder
open EqualityNormalize

/-- The source class payload retains both its trie and ascending set enumeration. -/
structure Record where
  trie : EqualityTrie.Trie
  paths : Class

/-- A physical class has a valid trie and the same canonical path set in both fields. -/
def Coherent (record : Record) : Prop := EqualityTrie.Valid record.trie ∧
  canonicalClass record.paths = record.paths ∧
  ∀ path, path ∈ EqualityTrie.fromPathTrie record.trie ↔ path ∈ record.paths

/-- The source comparator gives strict subsumption priority, then uses reverse structural order. -/
def completedCompare (first second : Record) : Ordering :=
  if EqualityTrie.hasSubsumingMember first.trie second.trie then .lt
  else if EqualityTrie.hasSubsumingMember second.trie first.trie then .gt
  else compare second.paths first.paths

/-- The independent finite path-list test detects exactly one strict prefix pair. -/
def subsumes (first second : Class) : Bool :=
  first.any (fun left => second.any (fun right => decide (left.IsPrefix right ∧ left ≠ right)))

/-- The independent list test has exactly the existing class-subsumption meaning. -/
theorem subsumes_exact (first second : Class) : subsumes first second = true ↔ Subsumes first second := by
  simp only [subsumes, List.any_eq_true, decide_eq_true_eq, Subsumes]

/-- Coherent physical trie subsumption equals the independent path-list test. -/
theorem trie_subsumes (first second : Record) (firstCoherent : Coherent first) (secondCoherent : Coherent second) :
    EqualityTrie.hasSubsumingMember first.trie second.trie = subsumes first.paths second.paths := by
  apply Bool.eq_iff_iff.mpr
  rw [EqualityTrie.hasSubsumingMember_exact _ _ firstCoherent.1 secondCoherent.1, subsumes_exact]
  simp only [firstCoherent.2.2, secondCoherent.2.2, EqualityTrie.StrictPrefix, Subsumes]

/-- The source comparison has exact logical strict-subsumption and reverse-fallback readback. -/
theorem completedCompare_exact (first second : Record) (firstCoherent : Coherent first) (secondCoherent : Coherent second) :
    completedCompare first second =
      if subsumes first.paths second.paths then .lt
      else if subsumes second.paths first.paths then .gt else compare second.paths first.paths := by
  rw [completedCompare, trie_subsumes first second firstCoherent secondCoherent,
    trie_subsumes second first secondCoherent firstCoherent]

/-- Run the actual installed source sortBy schedule on complete physical class records. -/
def ordered (records : List Record) : List Record := SourceListSort.sortBy completedCompare records

/-- Read the source's sorted classes as their ascending path lists for gate evaluation. -/
def orderedPaths (records : List Record) : Constraints := (ordered records).map Record.paths

/-- Physical ordering preserves all original record occurrences without a comparator-law premise. -/
theorem ordered_perm (records : List Record) : (ordered records).Perm records := SourceListSort.sortBy_perm _ records

/-- The exact path-list input preserves every original class occurrence, including repeats. -/
theorem orderedPaths_perm (records : List Record) : (orderedPaths records).Perm (records.map Record.paths) :=
  (ordered_perm records).map Record.paths

/-- Physical sorting retains every class representation invariant. -/
theorem ordered_coherent (records : List Record) (coherent : ∀ record ∈ records, Coherent record) :
    ∀ record ∈ ordered records, Coherent record :=
  fun record member => coherent record ((ordered_perm records).mem_iff.mp member)

/-- Build both source class fields from the original path set. Malformed trie input stays explicit. -/
def recordOf (paths : Class) : Option Record :=
  (EqualityTrie.toPathTrie paths.eraseDups).map (fun trie => ⟨trie, canonicalClass paths⟩)

/-- Source class construction succeeds for every supported path set and derives both field invariants. -/
theorem recordOf_complete (paths : Class) (supported : EqualityTrie.Supported paths.eraseDups) :
    ∃ record, recordOf paths = some record ∧ Coherent record ∧ record.paths = canonicalClass paths := by
  obtain ⟨trie, built, valid, _, members⟩ := EqualityTrie.toPathTrie_correct paths.eraseDups supported
  refine ⟨⟨trie, canonicalClass paths⟩, by simp only [recordOf, built, Option.map_some], ?_, rfl⟩
  refine ⟨valid, canonicalClass_idempotent paths, ?_⟩
  intro path
  exact (members path).trans (by simp [mem_canonicalClass])

/-- Construct physical source class records in the original constraint payload order. -/
def recordsOf : Constraints → Option (List Record)
  | [] => some []
  | first :: rest => do
      let record ← recordOf first
      let records ← recordsOf rest
      pure (record :: records)

/-- Supported raw class payloads derive complete coherent records without assuming normalization. -/
theorem recordsOf_complete (classes : Constraints)
    (supported : ∀ paths ∈ classes, EqualityTrie.Supported paths.eraseDups) :
    ∃ records, recordsOf classes = some records ∧ (∀ record ∈ records, Coherent record) ∧
      records.map Record.paths = classes.map canonicalClass := by
  induction classes with
  | nil => exact ⟨[], rfl, by simp, rfl⟩
  | cons first rest ih =>
      obtain ⟨record, built, coherent, paths⟩ := recordOf_complete first (supported first List.mem_cons_self)
      obtain ⟨records, restBuilt, restCoherent, restPaths⟩ := ih
        (fun paths member => supported paths (List.mem_cons_of_mem first member))
      refine ⟨record :: records, by simp only [recordsOf, built, restBuilt]; rfl, ?_, ?_⟩
      · intro other member
        rcases List.mem_cons.mp member with rfl | member
        · exact coherent
        · exact restCoherent other member
      · simp only [List.map_cons, paths, restPaths]

/-- Total successful normalization derives coherent physical source records and exact original path-list readback. -/
theorem normalized_records (input output : Constraints)
    (done : mkEqConstraints (EqualityTermination.normalizationBound input) input = .normalized output) :
    ∃ records, recordsOf output = some records ∧ (∀ record ∈ records, Coherent record) ∧ records.map Record.paths = output := by
  obtain ⟨active, consistent, disjoint, fixed⟩ := mkEqConstraints_invariants _ _ _ done
  obtain ⟨records, built, coherent, paths⟩ := recordsOf_complete output (consistent_supported output consistent)
  have normal := EqualitySaturation.step_normal output output active fixed
  refine ⟨records, built, coherent, paths.trans ?_⟩
  exact (List.map_congr_left (fun paths member => normal.2.2.2 paths member)).trans (List.map_id output)

/-- Normalized source payloads retain the existing transitive strict-subsumption theorem. -/
theorem normalized_subsumption_transitive (classes : Constraints) (fixed : congruenceStep classes = some classes)
    (first middle last : Class) (middleMember : middle ∈ classes) (lastMember : last ∈ classes)
    (before : Subsumes first middle) (after : Subsumes middle last) : Subsumes first last :=
  fixedPoint_subsumption_transitive classes fixed first middle last middleMember lastMember before after

/-- Consistent source payloads retain the existing irreflexive strict-subsumption theorem. -/
theorem normalized_subsumption_irreflexive (classes : Constraints) (consistent : isContradicting classes = false)
    (paths : Class) (member : paths ∈ classes) : ¬Subsumes paths paths :=
  consistent_subsumption_irreflexive classes consistent paths member

end MicroCFTA.SourceEqualityClassOrder
