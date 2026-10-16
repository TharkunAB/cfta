import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryOuterPrefixUnique

set_option linter.all true
set_option pp.explicit true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 1000000
set_option pp.fullNames true

namespace MicroCFTA.OuterPrefixUniqueChecks
open InternedConstructorTemplates SourceCurrentAllocatedPartialState SourceCurrentAllocatedPartialGraph
open SourceCurrentAllocatedFiniteOrdinaryOuterPrefixUnique
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Edge" => EdgeValue Symbol Guard
local notation "Caller" => SourceCurrentAllocatedPartialState.State
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node]

-- The second row starts at the actual first descendant return.
-- Equality of raw prefixes aligns every exact intermediate caller state.
theorem two_ordered_rows_align
    {width budget : Nat} {inherited : SourceEqualityConstraintAllocation.Value}
    {original1 original2 narrowed1 otherNarrowed1 child1 otherChild1 narrowed2 otherNarrowed2 child2 otherChild2 : Edge}
    {before mid1 otherMid1 after1 otherAfter1 mid2 otherMid2 after2 otherAfter2 : Caller width}
    (first : EdgeCall budget ⟨inherited, original1⟩ before narrowed1 mid1)
    (otherFirst : EdgeCall budget ⟨inherited, original1⟩ before otherNarrowed1 otherMid1)
    (firstChildren : Descendants budget inherited narrowed1 mid1 child1 after1)
    (otherFirstChildren : Descendants budget inherited otherNarrowed1 otherMid1 otherChild1 otherAfter1)
    (second : EdgeCall budget ⟨inherited, original2⟩ after1 narrowed2 mid2)
    (otherSecond : EdgeCall budget ⟨inherited, original2⟩ otherAfter1 otherNarrowed2 otherMid2)
    (secondChildren : Descendants budget inherited narrowed2 mid2 child2 after2)
    (otherSecondChildren : Descendants budget inherited otherNarrowed2 otherMid2 otherChild2 otherAfter2) :
    narrowed1 = otherNarrowed1 ∧ mid1 = otherMid1 ∧ child1 = otherChild1 ∧ after1 = otherAfter1 ∧
      narrowed2 = otherNarrowed2 ∧ mid2 = otherMid2 ∧ child2 = otherChild2 ∧ after2 = otherAfter2 := by
  obtain ⟨firstValue, firstState⟩ := edge_call first otherFirst
  subst otherNarrowed1
  subst otherMid1
  obtain ⟨firstChild, firstReturned⟩ := descendants firstChildren otherFirstChildren
  subst otherChild1
  subst otherAfter1
  obtain ⟨secondValue, secondState⟩ := edge_call second otherSecond
  subst otherNarrowed2
  subst otherMid2
  obtain ⟨lastValue, lastState⟩ := descendants secondChildren otherSecondChildren
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, lastValue, lastState⟩

#print axioms two_ordered_rows_align
#check @two_ordered_rows_align
end MicroCFTA.OuterPrefixUniqueChecks
