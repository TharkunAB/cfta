import MicroCFTA.SourceEqualityPartialInheritedPlainPrefix

/-!
# Finite structural children under arbitrary inherited payloads

Every child receives the actual descended payload and returned warm state.
Literal erased forests need no recursive input premise. Contradiction
skips the walk, and live payloads retain the source zero-based traversal.
-/
namespace MicroCFTA.SourceEqualityPartialInheritedPlainChildren
open InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open MergedColdReaderClosedInputs (ClosedValues)
open SourceObservations SourceSymbolicIndex SourceEqualityClassFoldGraph SourceEqualityNativeScoped
open SourceEqualityPartialScope SourceEqualityPartialGraph
local notation "Symbol" => Label FullSyntax.Formula
local notation "Guard" => Constraint FullSyntax.Formula
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}

/-- A node completes at every actual inherited payload and closed available warm scope. -/
def NodeComplete (value : Value Symbol Guard) : Prop :=
  ∀ inherited (before : NativeState width Symbol Guard), Scope before → Available before.machine.heap value → value.free = [] →
    ∃ result after, ReduceNode inherited value before result after

/-- An indexed child walk completes for any actual descended payload and initial child index. -/
def ChildrenComplete (values : List (Value Symbol Guard)) : Prop :=
  ∀ payload index (before : NativeState width Symbol Guard), Scope before → Values before.machine.heap values → ClosedValues values →
    ∃ results after, WalkChildren payload index values before results after

/-- Every literal erased child is EmptyNode, so its actual recursive graph leaves the native state unchanged. -/
theorem erased_walk (payload : SourceEqualityPrecheck.Constraint) (index : Nat) (values : List (Value Symbol Guard))
    (before : NativeState width Symbol Guard) :
    WalkChildren payload index (EqualityLeafProjectionRuntimeEmpty.erase values) before
      (EqualityLeafProjectionRuntimeEmpty.erase values) before := by
  induction values generalizing index with
  | nil => exact .nil
  | cons value values ih => exact .cons .empty (ih (index + 1))

/-- An actual completed smaller node derives the next indexed child scope under its real descended payload. -/
theorem cons (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (ambient : InternedGuardedLanguage.Env Symbol) (value : Value Symbol Guard) (values : List (Value Symbol Guard))
    (headIH : NodeComplete (width := width) value) (tailIH : ChildrenComplete (width := width) values) :
    ChildrenComplete (width := width) (value :: values) := by
  intro payload index before scope available closed
  obtain ⟨result, middle, head⟩ := headIH (SourceEqualityDescend.descend payload index) before scope
    (available _ List.mem_cons_self) (closed _ List.mem_cons_self)
  have checked := SourceEqualityPartialGraphProofs.node formulas solver ambient head scope
    (available _ List.mem_cons_self) (closed _ List.mem_cons_self)
  obtain ⟨results, after, tail⟩ := tailIH payload (index + 1) middle checked.1
    (fun value member => checked.2.1.available value (available value (List.mem_cons_of_mem _ member)))
    (fun value member => closed value (List.mem_cons_of_mem _ member))
  exact ⟨result :: results, after, .cons head tail⟩

/-- Prefix children complete through actual contradiction, original structural recursion, or literal erased recursion. -/
theorem complete {original values : List (Value Symbol Guard)}
    (ih : ChildrenComplete (width := width) original)
    (shape : values = original ∨ values = EqualityLeafProjectionRuntimeEmpty.erase original)
    (payload : SourceEqualityPrecheck.Constraint) (before : NativeState width Symbol Guard)
    (scope : Scope before) (available : Values before.machine.heap values) (closed : ClosedValues values) :
    ∃ results after, ReduceChildren payload values before results after := by
  cases payload with
  | none => exact ⟨_, _, .contradiction⟩
  | some records =>
      rcases shape with same | erased
      · cases same
        obtain ⟨results, after, trace⟩ := ih (some records) 0 before scope available closed
        exact ⟨results, after, .live trace⟩
      · cases erased
        exact ⟨_, before, .live (erased_walk (some records) 0 original before)⟩

end MicroCFTA.SourceEqualityPartialInheritedPlainChildren
