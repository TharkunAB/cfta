import MicroCFTA.SourceEqualityPartialScope

/-!
# Local semantic conclusions for actual recursive source graphs

Each conclusion uses the actual input scope. Child conclusions carry their
own descended obligations. These definitions are induction motives, not
assumed whole-caller laws.
-/
namespace MicroCFTA.SourceEqualityPartialGraphLaws
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values Edges)
open MergedColdReaderClosedInputs (ClosedValues ClosedEdges)
open SourceObservations SourceSymbolicIndex SourceEqualityClassFoldGraph SourceEqualityNativeScoped SourceEqualityRequiredCache
open SourceEqualityPartialScope
local notation "Symbol" => Label FullSyntax.Formula
local notation "Guard" => Constraint FullSyntax.Formula
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
variable (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
variable (ambient : InternedGuardedLanguage.Env Symbol)
local notation "meaning" => InternedGuardedLanguage.meaning (acceptsConstraint formulas solver) ambient
local notation "rowMeaning" => SourceEqualityInheritedRowsProofs.meaning (acceptsConstraint formulas solver) ambient

/-- A node conclusion retains physical scope and exact contextual public meaning. -/
def NodeLaw (inherited : SourceEqualityPrecheck.Constraint) (value : Value Symbol Guard) (before : NativeState width Symbol Guard)
    (result : Value Symbol Guard) (after : NativeState width Symbol Guard) : Prop :=
  Scope before → Available before.machine.heap value → value.free = [] →
    Scope after ∧ Keeps before.machine.heap after.machine.heap ∧ Available after.machine.heap result ∧ result.free = [] ∧ ∀ term,
      (meaning result term → meaning value term) ∧
      (SourceEqualityPrecheck.Sat term inherited → (meaning result term ↔ meaning value term))

/-- Ordered rows retain both physical heaps and exact contextual union meaning. -/
def RowsLaw (inherited : SourceEqualityPrecheck.Constraint) (edges : List (EdgeValue Symbol Guard)) (before : NativeState width Symbol Guard)
    (results : List (EdgeValue Symbol Guard)) (after : NativeState width Symbol Guard) : Prop :=
  Scope before → Edges before.machine.heap edges → ClosedEdges edges →
    Scope after ∧ Keeps before.machine.heap after.machine.heap ∧ Edges after.machine.heap results ∧ ClosedEdges results ∧ ∀ term,
      (rowMeaning results term → rowMeaning edges term) ∧
      (SourceEqualityPrecheck.Sat term inherited → (rowMeaning results term ↔ rowMeaning edges term))

/-- Child conclusions use satisfaction of the actual combined parent payload. -/
def ChildrenLaw (payload : SourceEqualityPrecheck.Constraint) (values : List (Value Symbol Guard)) (before : NativeState width Symbol Guard)
    (results : List (Value Symbol Guard)) (after : NativeState width Symbol Guard) : Prop :=
  Scope before → Values before.machine.heap values → ClosedValues values → SourceEqualityDescend.WellFormed payload →
    Scope after ∧ Keeps before.machine.heap after.machine.heap ∧ Values after.machine.heap results ∧ ClosedValues results ∧ ∀ symbol terms,
      (All₂ meaning results terms → All₂ meaning values terms) ∧
      (SourceEqualityPrecheck.Sat (.node symbol terms) payload → (All₂ meaning results terms ↔ All₂ meaning values terms))

/-- Indexed walks retain each actual descended child obligation before parent specialization. -/
def WalkLaw (payload : SourceEqualityPrecheck.Constraint) (index : Nat) (values : List (Value Symbol Guard)) (before : NativeState width Symbol Guard)
    (results : List (Value Symbol Guard)) (after : NativeState width Symbol Guard) : Prop :=
  Scope before → Values before.machine.heap values → ClosedValues values →
    Scope after ∧ Keeps before.machine.heap after.machine.heap ∧ Values after.machine.heap results ∧ ClosedValues results ∧ ∀ terms,
      (All₂ meaning results terms → All₂ meaning values terms) ∧
      ((∀ offset term, terms[offset]? = some term → SourceEqualityPrecheck.Sat term (SourceEqualityDescend.descend payload (index + offset))) →
        (All₂ meaning results terms ↔ All₂ meaning values terms))

/-- A real recursive node conclusion and a real tail conclusion derive the complete indexed forest conclusion. -/
theorem walk_cons {payload index value result values results} {before middle after : NativeState width Symbol Guard}
    (headIH : NodeLaw formulas solver ambient (SourceEqualityDescend.descend payload index) value before result middle)
    (tailIH : WalkLaw formulas solver ambient payload (index + 1) values middle results after) :
    WalkLaw formulas solver ambient payload index (value :: values) before (result :: results) after := by
  intro scope available closed
  have head := headIH scope (available _ List.mem_cons_self) (closed _ List.mem_cons_self)
  have tail := tailIH head.1 (fun child member => head.2.1.available child (available child (List.mem_cons_of_mem _ member)))
    (fun child member => closed child (List.mem_cons_of_mem _ member))
  refine ⟨tail.1, head.2.1.trans tail.2.1, ?_, ?_, ?_⟩
  · intro child member
    rcases List.mem_cons.mp member with rfl | member
    · exact tail.2.1.available _ head.2.2.1
    · exact tail.2.2.1 child member
  · intro child member
    rcases List.mem_cons.mp member with rfl | member
    · exact head.2.2.2.1
    · exact tail.2.2.2.1 child member
  · intro terms
    cases terms with
    | nil =>
        constructor
        · intro accepted; cases accepted
        · intro _; constructor <;> intro accepted <;> cases accepted
    | cons term terms =>
        have firstLaw := head.2.2.2.2 term
        have restLaw := tail.2.2.2.2 terms
        constructor
        · intro accepted
          cases accepted with
          | cons first rest => exact .cons (firstLaw.1 first) (restLaw.1 rest)
        · intro satisfied
          have firstSat : SourceEqualityPrecheck.Sat term (SourceEqualityDescend.descend payload index) := by simpa using satisfied 0 term (by simp)
          have restSat : ∀ offset child, terms[offset]? = some child →
              SourceEqualityPrecheck.Sat child (SourceEqualityDescend.descend payload (index + 1 + offset)) := by
            intro offset child found
            have selected := satisfied (offset + 1) child (by simpa using found)
            simpa only [Nat.add_assoc, Nat.add_comm 1 offset] using selected
          constructor
          · intro accepted
            cases accepted with
            | cons first rest => exact .cons ((firstLaw.2 firstSat).mp first) ((restLaw.2 restSat).mp rest)
          · intro accepted
            cases accepted with
            | cons first rest => exact .cons ((firstLaw.2 firstSat).mpr first) ((restLaw.2 restSat).mpr rest)

/-- Actual parent satisfaction supplies the indexed walk obligations without another node-law premise. -/
theorem live_children {records values results} {before after : NativeState width Symbol Guard}
    (ih : WalkLaw formulas solver ambient (some records) 0 values before results after) :
    ChildrenLaw formulas solver ambient (some records) values before results after := by
  intro scope available closed wellFormed
  have checked := ih scope available closed
  refine ⟨checked.1, checked.2.1, checked.2.2.1, checked.2.2.2.1, ?_⟩
  intro symbol terms
  exact ⟨(checked.2.2.2.2 terms).1, fun satisfied =>
    (checked.2.2.2.2 terms).2 (SourceEqualityInheritedChildrenProofs.parent_obligations _ wellFormed symbol terms satisfied)⟩

end MicroCFTA.SourceEqualityPartialGraphLaws
