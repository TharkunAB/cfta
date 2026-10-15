import MicroCFTA.SourceEqualitySelectedRecords

/-!
# Executable selection of original physical class records

Each class queries the original forest at the actual returned cache.
Query receipts retain its Boolean and both heaps. The selected physical
records come from those exact original occurrences, including repeats.
-/
namespace MicroCFTA.SourceEqualityRecordSelectionWorker
open InternedConstructorTemplates InternedNestedConstruction SourceEqualityClassOrder
open InternedSourceClassSelection (Query)

/-- Execute actual class queries in source order and retain their complete positional receipts. -/
def queries [DecidableEq (EdgeKey Symbol Guard)] (unconstrained : Value Symbol Guard → Bool)
    (fuel : Nat) (values : List (Value Symbol Guard)) : List Record → State Symbol Guard → Outcome Symbol Guard (Option (List (Query Symbol Guard)))
  | [], state => .done (some []) state
  | record :: records, state =>
      (InternedFreshOrdinaryStatefulGate.classMeets unconstrained fuel values record.paths state).bind fun answer middle =>
        match answer with
        | none => .done none middle
        | some blocked => (queries unconstrained fuel values records middle).bind fun rest after =>
            .done (rest.map (fun tail => ⟨record.paths, state, blocked, middle⟩ :: tail)) after

/-- Read the selected original physical records from the exact completed source query receipts. -/
def select [DecidableEq (EdgeKey Symbol Guard)] (unconstrained : Value Symbol Guard → Bool)
    (fuel : Nat) (values : List (Value Symbol Guard)) (records : List Record) (state : State Symbol Guard) : Outcome Symbol Guard (Option (List Record)) :=
  (queries unconstrained fuel values records state).bind fun actual after => .done (actual.map (SourceEqualitySelectedRecords.keep records)) after

end MicroCFTA.SourceEqualityRecordSelectionWorker
