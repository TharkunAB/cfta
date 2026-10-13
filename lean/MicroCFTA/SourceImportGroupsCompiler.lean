import MicroCFTA.SourceImportGroupsRanks
import MicroCFTA.SourceFiniteRebuildDriver

/-!
# Compact compilation of finite imported parts

Each observation part has a derived finite language. Rebuilding those
members instantiates the actual compact edge, cache, and choice primitives.
Their correctness does not need assumed counts or symbolic backend laws.
This composition does not identify native interned nodes or custom ordering.
-/

namespace MicroCFTA.SourceImportGroupsCompiler

open Language Observation ObservationGraph FTAValidation SourceImportGroups
open CompactEdgeRanks FiniteAutomatonDriver

variable [DecidableEq Symbol] [DecidableEq Refinement]
  [Ord (Term (Label Symbol Refinement))] [Ord (Option (Term (Label Symbol Refinement)))]
  (input : List (Term (Label Symbol Refinement)))
  (table : Rows (Option (Term (Label Symbol Refinement))) (Label Symbol Refinement))
  (success : SourceFromTerms.build input = .ok table)
  (requested : List Path)
  (part : Variant (Option (Term (Label Symbol Refinement))) Symbol Refinement)
  (present : part ∈ ImportObservations.split (rowFor table) requested none)

/-- Run the constructive compact primitive compiler on one part's derived finite members. -/
def compile : Option (Index (Term (Label Symbol Refinement))) :=
  SourceFiniteRebuildDriver.compile (members input requested part)

include success present

/-- The compact primitive result accepts exactly the concrete split part's language. -/
theorem compile_exact :
    ResultExact (AcceptsNode (rowFor table) part.node) (compile input requested part) := by
  have precise := SourceFiniteRebuildDriver.compile_exact (members input requested part)
  exact (result_ext _ _ (fun term =>
    SourceImportGroupsFallback.part_exact input table success requested part present term) _).mp precise

/-- The primitive path produces an empty result precisely when the concrete part accepts nothing. -/
theorem compile_empty : compile input requested part = none ↔
    ∀ term, ¬AcceptsNode (rowFor table) part.node term := by
  constructor
  · intro empty
    have precise := compile_exact input table success requested part present
    rwa [empty] at precise
  · intro empty
    rw [compile, SourceFiniteRebuildDriver.compile_empty_iff]
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro term member
    exact empty term ((SourceImportGroupsFallback.part_exact input table success requested part present term).mp member)

/-- Each nonempty actual part has a finite completed compact index. -/
theorem compile_nonempty (term : Term (Label Symbol Refinement)) (accepted : AcceptsNode (rowFor table) part.node term) :
    ∃ result, compile input requested part = some result := by
  cases result : compile input requested part with
  | none => exact False.elim ((compile_empty input table success requested part present).mp result term accepted)
  | some index => exact ⟨index, rfl⟩

/-- A successful part index has derived inverse laws and rejects exactly its nonmembers. -/
theorem compile_inverse (result : Index (Term (Label Symbol Refinement)))
    (compiled : compile input requested part = some result) :
    Correct result ∧ (∀ term, result.rank term = none ↔ ¬AcceptsNode (rowFor table) part.node term) := by
  have precise := compile_exact input table success requested part present
  rw [compiled] at precise
  exact ⟨precise.2.1, (exact_index_api _ result precise).2.1⟩

omit [Ord (Option (Term (Label Symbol Refinement)))] success present in
/-- Canonical local sorting preserves the derived part count and fixes every primitive selection. -/
theorem compile_fields (result : Index (Term (Label Symbol Refinement)))
    (compiled : compile input requested part = some result) :
    result.count = (members input requested part).length ∧
      ∀ rank, result.select rank = (SourceFromTerms.ordered (members input requested part))[rank]? := by
  have fields := SourceFiniteRebuildDriver.compile_fields (members input requested part) result compiled
  have permutation : (SourceFromTerms.ordered (members input requested part)).Perm (members input requested part) :=
    (List.perm_ext_iff_of_nodup (SourceFromTerms.ordered_nodup _) (members_nodup input requested part)).mpr
      (SourceFromTerms.mem_ordered _)
  exact ⟨fields.1.trans permutation.length_eq, fields.2⟩

omit [Ord (Option (Term (Label Symbol Refinement)))] success present in
/-- The termStatic user-label selector uses the same derived compact rank positions. -/
theorem compiled_query_record (result : Index (Term (Label Symbol Refinement)))
    (compiled : compile input requested part = some result) :
    let record := SourceImportGroupsRanks.partIndex (SourceFromTerms.ordered (members input requested part))
    record.count = result.count ∧
      (∀ rank, record.select rank = (result.select rank).map SourceImportGroupsRanks.userTerm) ∧
      FinalObservationRanks.Exact record := by
  have fields := SourceFiniteRebuildDriver.compile_fields (members input requested part) result compiled
  refine ⟨?_, ?_, SourceImportGroupsRanks.finiteIndex_exact _⟩
  · simpa [SourceImportGroupsRanks.partIndex, SourceImportGroupsRanks.finiteIndex] using fields.1.symm
  · intro rank
    simp [SourceImportGroupsRanks.partIndex, SourceImportGroupsRanks.finiteIndex, fields.2 rank]

end MicroCFTA.SourceImportGroupsCompiler
