import MicroCFTA.SourceCurrentGatePlainRegion
import MicroCFTA.SourceEqualityRequiredGraph

/-!
# Initial local domains for Required guard origins

Empty requirements leave arbitrary values unchanged. Ordinary requests
check only selected existing child slots. A recursive exposure uses the
actual source gate predicate. Unselected subtrees need no annotation.
-/
namespace MicroCFTA.SourceCurrentRequiredRowOrigins
open InternedConstructorTemplates SourceEqualityNeeded
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula

/-- The initial requirement permits only accepted recursive exposures at selected positions. -/
inductive ExposureSafe : Needed → Value Symbol Guard → Prop where
  /-- Empty requirements do not inspect their supplied value. -/
  | identity (value : Value Symbol Guard) : ExposureSafe (.node []) value
  /-- An empty value introduces no row or recursive exposure. -/
  | empty (needed : Needed) : ExposureSafe needed .empty
  /-- An ordinary request checks each selected existing child at its stored requirement. -/
  | ordinary (entries : List (Int × Needed)) (entry) (rows : List (EdgeValue Symbol Guard)) (level free)
      (children : ∀ row ∈ rows, ∀ index childNeeded,
        SourceEqualityNeededMap.lookup (Int.ofNat index) entries = some childNeeded →
        ∀ child, row.children[index]? = some child → ExposureSafe childNeeded child) :
      ExposureSafe (.node entries) (.node entry rows level free)
  /-- The literal source predicate certifies every recursive region that this rule exposes. -/
  | accepted (needed : Needed) (value : Value Symbol Guard)
      (plain : SourceMemoGate.unconstrained value = true) : ExposureSafe needed value

end MicroCFTA.SourceCurrentRequiredRowOrigins
