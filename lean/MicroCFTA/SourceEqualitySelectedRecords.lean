import MicroCFTA.SourceEqualitySelectedRequired

/-!
# Physical class records retained by actual source selection

The original query order aligns each Boolean with its original physical
record. Selection preserves those records rather than constructing new
tries from their paths. It retains every repeated clear occurrence.
-/
namespace MicroCFTA.SourceEqualitySelectedRecords
open SourceEqualityClassOrder InternedSourceClassSelection

/-- Keep the original physical record at each clear query position. -/
def keep : List Record → List (Query Symbol Guard) → List Record
  | record :: records, query :: queries => if query.blocked then keep records queries else record :: keep records queries
  | _, _ => []

/-- Positional record selection always retains an ordered original sublist. -/
theorem sublist (records : List Record) (queries : List (Query Symbol Guard)) : (keep records queries).Sublist records := by
  induction records generalizing queries with
  | nil => exact .slnil
  | cons record records ih =>
      cases queries with
      | nil => exact List.nil_sublist _
      | cons query queries =>
          unfold keep
          split
          · exact (ih queries).cons _
          · exact (ih queries).cons_cons _

/-- Aligned actual query paths derive exactly the original selected physical-record path list. -/
theorem paths (records : List Record) (queries : List (Query Symbol Guard))
    (aligned : queries.map Query.paths = records.map Record.paths) :
    (keep records queries).map Record.paths = selected queries := by
  induction records generalizing queries with
  | nil =>
      have empty : queries = [] := List.map_eq_nil_iff.mp aligned
      cases empty
      rfl
  | cons record records ih =>
      cases queries with
      | nil => cases aligned
      | cons query queries =>
          have same := List.cons.inj aligned
          rw [keep, selected_cons]
          split
          · exact ih queries same.2
          · simpa only [List.map_cons, same.1] using congrArg (List.cons record.paths) (ih queries same.2)

/-- Actual source gate traces align every retained physical record with its original path set. -/
theorem trace_paths [DecidableEq (InternedConstructorTemplates.EdgeKey Symbol Guard)]
    {unconstrained : InternedConstructorTemplates.Value Symbol Guard → Bool} {records : List Record} {values before queries after}
    (trace : Trace unconstrained values (records.map Record.paths) before queries after) :
    (keep records queries).map Record.paths = selected queries := paths records queries trace.original

/-- Selection retains every physical record representation invariant. -/
theorem coherent (records : List Record) (queries : List (Query Symbol Guard)) (valid : ∀ record ∈ records, Coherent record) :
    ∀ record ∈ keep records queries, Coherent record := fun record member => valid record ((sublist records queries).subset member)

/-- Selection retains nontriviality of each original active class. -/
theorem active (records : List Record) (queries : List (Query Symbol Guard))
    (nontrivial : ∀ record ∈ records, EqualityNormalize.Nontrivial record.paths) :
    ∀ record ∈ keep records queries, EqualityNormalize.Nontrivial record.paths := fun record member => nontrivial record ((sublist records queries).subset member)

end MicroCFTA.SourceEqualitySelectedRecords
