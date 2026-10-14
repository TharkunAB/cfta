import MicroCFTA.SourceFreshOrdinaryColdCyclicInput

/-!
# Actual source root checks before cold traversal

The compiler checks EmptyNode before it inspects free recursion references.
An open root returns its error before reachable rows or native callbacks.
The cold-table encoding of closed roots has the same empty-root decision.
-/
namespace MicroCFTA.SourceFreshOrdinaryNativeEntryPrecheck
open InternedConstructorTemplates

/-- The actual compiler's root-only control decision before it reads any row. -/
inductive Decision where
  | empty
  | openRoot
  | rows
  deriving DecidableEq

/-- Inspect the actual EmptyNode constructor, then the source root's free-reference cache. -/
def check (value : Value Symbol Guard) : Decision :=
  match value with
  | .empty => .empty
  | value => if value.free.isEmpty then .rows else .openRoot

/-- The literal EmptyNode case returns before row traversal. -/
theorem check_empty : check (.empty : Value Symbol Guard) = .empty := rfl

/-- An actual recursion reference is open and does not enter cold traversal. -/
theorem check_reference (name : InternedBinderProtocol.Reference) :
    check (.reference name : Value Symbol Guard) = .openRoot := rfl

/-- Only the literal EmptyNode constructor takes the compiler's empty branch. -/
theorem check_empty_iff (value : Value Symbol Guard) : check value = .empty ↔ value = .empty := by
  cases value <;> simp [check] <;> split <;> simp_all

/-- The row phase starts exactly for nonempty roots with no free recursion reference. -/
theorem check_rows_iff (value : Value Symbol Guard) : check value = .rows ↔ value ≠ .empty ∧ value.free = [] := by
  cases value <;> simp [check, Value.free]

/-- The actual open-root error is determined entirely before any row or callback is read. -/
theorem check_open_iff (value : Value Symbol Guard) : check value = .openRoot ↔ value.free ≠ [] := by
  cases value <;> simp [check, Value.free]

/-- The cold-table empty-root flag is the source constructor check on its closed-root domain. -/
theorem closed_empty_exact (value : Value Symbol Guard) (closed : value.free = []) :
    (SourcePreparedSharedRows.reference value).isNone = true ↔ check value = .empty := by
  rw [check_empty_iff]
  cases value <;> simp_all [SourcePreparedSharedRows.reference, Value.free]

/-- Open references show why the closed cold-table adapter cannot define the public root precheck. -/
theorem reference_boundary (name : InternedBinderProtocol.Reference) :
    (SourcePreparedSharedRows.reference (.reference name : Value Symbol Guard)).isNone = true ∧
      check (.reference name : Value Symbol Guard) = .openRoot := ⟨rfl, rfl⟩

end MicroCFTA.SourceFreshOrdinaryNativeEntryPrecheck
