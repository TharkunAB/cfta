import MicroCFTA.SourceCurrentAllocatedPartialWalkLanguage

/-!
# Language composition for current rows and descendants

Each lemma composes laws for the literal smaller calls of an actual trace.
The descendant prefix reads the full returned guard and combines inherited
constraints first. Raw rebuilding retains that guard and the returned child
list. These lemmas do not prove completion or a whole-caller invariant.
-/
namespace MicroCFTA.SourceCurrentAllocatedPartialForestLanguage
open Cache Language InternedConstructorTemplates InternedGuardedLanguage
open SourceCurrentAllocatedPartialState
open SourceCurrentAllocatedPartialGraph (Rows EdgeCall Descendants Children prefixState)
open SourceCurrentAllocatedPartialMemoSound (NodeLaw EdgeLaw)
open SourceCurrentAllocatedPartialWalkLanguage (ChildrenLaw)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "EqValue" => SourceEqualityConstraintAllocation.Value
local notation "holds" => SourceEqualityPCSGuard.holds
variable {width : Nat}

/-- A row list denotes its ordered union of complete guarded edge languages. -/
def RowsMeaning (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (ambient : Env Symbol)
    (rows : List (EdgeValue Symbol Guard)) (term : Term Symbol) : Prop :=
  ∃ row ∈ rows, edgeMeaning (holds formulas solver) ambient row term

variable (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)

/-- Returning the input unchanged satisfies the inherited-conditioned node law. -/
theorem node_unchanged (inherited : EqValue) (value : Value Symbol Guard) :
    NodeLaw formulas solver ⟨inherited, value⟩ value :=
  fun _ _ => ⟨id, fun _ => Iff.rfl⟩

/-- The actual empty-node branch needs no inherited satisfaction assumption. -/
theorem node_empty (inherited : EqValue) : NodeLaw formulas solver ⟨inherited, .empty⟩ .empty :=
  node_unchanged formulas solver inherited .empty

/-- The unchanged union branch has the same complete union language. -/
theorem node_union (inherited : EqValue) (entry : Interned InternedBinderProtocol.NodeKey)
    (members : List (Value Symbol Guard)) (depth : Nat) (free : List InternedBinderProtocol.Reference) :
    NodeLaw formulas solver ⟨inherited, .union entry members depth free⟩ (.union entry members depth free) :=
  node_unchanged formulas solver inherited _

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq (Value Symbol Guard)]

/-- Actual rows narrow their input union and preserve inherited-satisfying terms. -/
structure RowsLaw {budget : Nat} {inherited : EqValue}
    {values results : List (EdgeValue Symbol Guard)} {before after : Caller width}
    (_actual : Rows budget inherited values before results after) : Prop where
  narrows : ∀ ambient term, RowsMeaning formulas solver ambient results term →
    RowsMeaning formulas solver ambient values term
  preserves : ∀ ambient term, SourceEqualityPrecheck.Sat term inherited.payload →
    RowsMeaning formulas solver ambient values term → RowsMeaning formulas solver ambient results term

/-- The empty source row list has no accepted term. -/
theorem rows_nil (budget : Nat) (inherited : EqValue) (before : Caller width) :
    RowsLaw formulas solver (Rows.nil (budget := budget) (inherited := inherited) (before := before)) :=
  ⟨fun _ _ accepted => accepted, fun _ _ _ accepted => accepted⟩

/-- A reduced edge, its returned-edge descendants, and the row tail compose in source order. -/
theorem rows_cons {budget : Nat} {inherited : EqValue}
    {original narrowed result : EdgeValue Symbol Guard} {originals results : List (EdgeValue Symbol Guard)}
    {before middle afterChildren after : Caller width}
    (edge : EdgeCall budget ⟨inherited, original⟩ before narrowed middle)
    (children : Descendants budget inherited narrowed middle result afterChildren)
    (tail : Rows budget inherited originals afterChildren results after)
    (edgeLaw : EdgeLaw formulas solver ⟨inherited, original⟩ narrowed)
    (childrenLaw : EdgeLaw formulas solver ⟨inherited, narrowed⟩ result)
    (tailLaw : RowsLaw formulas solver tail) : RowsLaw formulas solver (.cons edge children tail) := by
  refine ⟨?_, ?_⟩
  · intro ambient term accepted
    obtain ⟨row, member, accepted⟩ := accepted
    rcases List.mem_cons.mp member with same | member
    · subst row
      exact ⟨original, List.mem_cons_self,
        (edgeLaw ambient term).1 ((childrenLaw ambient term).1 accepted)⟩
    · obtain ⟨originalRow, member, accepted⟩ := tailLaw.narrows ambient term ⟨row, member, accepted⟩
      exact ⟨originalRow, List.mem_cons_of_mem _ member, accepted⟩
  · intro ambient term satisfied accepted
    obtain ⟨row, member, accepted⟩ := accepted
    rcases List.mem_cons.mp member with same | member
    · subst row
      exact ⟨result, List.mem_cons_self,
        ((childrenLaw ambient term).2 satisfied).mpr (((edgeLaw ambient term).2 satisfied).mpr accepted)⟩
    · obtain ⟨resultRow, member, accepted⟩ := tailLaw.preserves ambient term satisfied ⟨row, member, accepted⟩
      exact ⟨resultRow, List.mem_cons_of_mem _ member, accepted⟩

/-- Inherited satisfaction makes the actual ordered row union exact. -/
theorem RowsLaw.exact {budget : Nat} {inherited : EqValue}
    {values results : List (EdgeValue Symbol Guard)} {before after : Caller width}
    {actual : Rows budget inherited values before results after} (law : RowsLaw formulas solver actual)
    (ambient : Env Symbol) (term : Term Symbol) (satisfied : SourceEqualityPrecheck.Sat term inherited.payload) :
    RowsMeaning formulas solver ambient results term ↔ RowsMeaning formulas solver ambient values term :=
  ⟨law.narrows ambient term, law.preserves ambient term satisfied⟩

/-- The actual prefix, child law, and raw rebuild derive the returned edge law. -/
theorem descendants {budget : Nat} {inherited combined : EqValue}
    {edge result : EdgeValue Symbol Guard} {values : List (Value Symbol Guard)}
    {before middle : Caller width} {after : SourceEqualityNativeDemand.State width}
    {prefixInventory rebuildInventory : SourceCurrentAllocatedNativeInventoryState.Inventory}
    (prefixReceipt : SourceCurrentAllocatedInheritedPrefix.Receipt formulas solver prefixInventory
      edge.entry.key.constraint inherited before.checked combined)
    (children : Children budget combined edge.children (prefixState before edge inherited) values middle)
    (childrenLaw : ChildrenLaw formulas solver children)
    (rebuilt : SourceCurrentAllocatedRawRebuild.EdgeReceipt formulas solver rebuildInventory edge values
      middle.checked result after) : EdgeLaw formulas solver ⟨inherited, edge⟩ result := by
  intro ambient term
  have input := InternedGuardedLanguage.edgeMeaning_all (holds formulas solver) ambient edge term
  refine ⟨?_, ?_⟩
  · intro accepted
    obtain ⟨terms, same, accepted, guarded⟩ := (rebuilt.language (holds formulas solver) ambient term).mp accepted
    apply input.mpr
    exact ⟨terms, same, childrenLaw.narrows ambient terms accepted, guarded⟩
  · intro satisfied
    refine ⟨fun accepted => ?_, fun accepted => ?_⟩
    · obtain ⟨terms, same, accepted, guarded⟩ := (rebuilt.language (holds formulas solver) ambient term).mp accepted
      exact input.mpr ⟨terms, same, childrenLaw.narrows ambient terms accepted, guarded⟩
    · obtain ⟨terms, same, accepted, guarded⟩ := input.mp accepted
      have combinedSat := prefixReceipt.guard_satisfied term guarded satisfied
      rw [same] at combinedSat
      exact (rebuilt.language (holds formulas solver) ambient term).mpr
        ⟨terms, same, childrenLaw.preserves ambient edge.entry.key.symbol terms combinedSat accepted, guarded⟩

/-- Actual row laws and literal modifyNode readback derive the ordinary parent law. -/
theorem ordinary {budget : Nat} {inherited : EqValue}
    {entry : Interned InternedBinderProtocol.NodeKey} {edges results : List (EdgeValue Symbol Guard)}
    {depth : Nat} {free : List InternedBinderProtocol.Reference} {before middle : Caller width}
    {result : Value Symbol Guard} {after : SourceEqualityNativeDemand.State width}
    {inventory : SourceCurrentAllocatedNativeInventoryState.Inventory}
    (rows : Rows budget inherited edges before results middle)
    (law : RowsLaw formulas solver rows)
    (rebuilt : SourceCurrentAllocatedRawRebuild.NodeReceipt formulas solver inventory
      (.node entry edges depth free) edges results middle.checked result after) :
    NodeLaw formulas solver ⟨inherited, .node entry edges depth free⟩ result := by
  intro ambient term
  have output := rebuilt.language (holds formulas solver) ambient term
  have input := SourceEqualityPartialNodeRebuild.node_meaning (holds formulas solver) ambient entry edges depth free term
  exact ⟨fun accepted => input.mpr (law.narrows ambient term (output.mp accepted)),
    fun satisfied => output.trans ((law.exact formulas solver ambient term satisfied).trans input.symm)⟩

end MicroCFTA.SourceCurrentAllocatedPartialForestLanguage
