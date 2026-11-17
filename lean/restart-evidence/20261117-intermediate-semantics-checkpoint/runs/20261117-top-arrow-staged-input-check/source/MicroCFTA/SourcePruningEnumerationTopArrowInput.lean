import MicroCFTA.SourcePruningEnumerationOwnInputShape
import MicroCFTA.SourceSynthesisGeneralizeSyntax

namespace MicroCFTA.SourcePruningEnumerationTopArrowInput
open EnumerationState InternedConstructorTemplates
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Edge" => EdgeValue Symbol Constraint
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Input" => Node × List Suspended × Option (EnumerateM Symbol Constraint (Fragments.Fragment Symbol))
set_option autoImplicit false

/- Note [Actual Top arrow preparation]
The own Top guard allocates no suspended class.
The actual cache endpoint is the original input cache.
The first staged child keeps the inherited marker bucket exactly.
This law does not exclude a terminal inherited marker demand.
It does not assert that the marker is traversed or is a Type operand.
-/

theorem top_arrow_preparation_first
    (heap : InternedConstructorTemplates.State Symbol Constraint)
    (scs : List Suspended) (edge : Edge) (marker argument result : Node)
    (before middle : Cached) (symbol : Symbol) (staged : List Input)
    (residual : Option Constraint)
    (top : edge.entry.key.constraint = SourceSynthesisGeneralizeSyntax.top)
    (children : edge.children = [marker, argument, result])
    (actual : SourcePruningEnumerationCachedOwn.prepare heap scs edge before =
      some [((symbol, staged, residual), middle)]) :
    middle = before ∧ symbol = edge.entry.key.symbol ∧ residual = none ∧
      staged[0]? = some (marker, descendScs 0 scs,
        SourcePruningEnumerationShallowChild.prepareChild (EnumGuard := Constraint)
          (descendScs 0 scs) marker)
 := by
  have projected : SourcePruningEnumerationConstraint.project edge.entry.key.constraint =
      some ([], none) := by
    rw [top]
    rfl
  have observed := actual
  unfold SourcePruningEnumerationCachedOwn.prepare at observed
  split at observed
  next admitted =>
    rw [projected] at observed
    dsimp only [SourcePruningEnumerationCachedOwn.suspendMany, Option.map] at observed
    have rowSame := (List.cons.inj (Option.some.inj observed)).1
    have cacheSame := congrArg (fun row : (Symbol × List Input × Option Constraint) × Cached => row.2) rowSame
    have symbolSame := congrArg (fun row : (Symbol × List Input × Option Constraint) × Cached => row.1.1) rowSame
    have stagedSame := congrArg (fun row : (Symbol × List Input × Option Constraint) × Cached => row.1.2.1) rowSame
    have residualSame := congrArg (fun row : (Symbol × List Input × Option Constraint) × Cached => row.1.2.2) rowSame
    refine ⟨cacheSame.symm, symbolSame.symm, residualSame.symm, ?_⟩
    rw [← stagedSame, children]
    rfl
  next rejected => cases observed

end MicroCFTA.SourcePruningEnumerationTopArrowInput

#check MicroCFTA.SourcePruningEnumerationTopArrowInput.top_arrow_preparation_first
#print axioms MicroCFTA.SourcePruningEnumerationTopArrowInput.top_arrow_preparation_first
