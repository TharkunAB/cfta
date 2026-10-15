import MicroCFTA.SourceEqualityPartialMemoSource

/-!
# Equality-free ordinary regions above actual opaque source branches

Only ordinary node children are traversed. Mu and interned unions stop
the traversal, as the source caller does. Each ordinary edge reads the
actual empty physical equality payload. Full guards remain unchanged.
-/
namespace MicroCFTA.SourceEqualityPartialPlainRegion
open InternedConstructorTemplates SourceObservations SourceSymbolicIndex
local notation "Symbol" => Label FullSyntax.Formula
local notation "Guard" => Constraint FullSyntax.Formula

mutual
/-- An equality-free caller region stops at the actual Mu and union branches. -/
inductive Region : Value Symbol Guard → Prop where
  | empty : Region .empty
  | binder : Region (.mu entry body depth ordinary)
  | union : Region (.union entry members depth free)
  | ordinary (rows : Rows edges) : Region (.node entry edges depth free)

/-- Every traversed edge has the actual empty physical payload and smaller equality-free children. -/
inductive Rows : List (EdgeValue Symbol Guard) → Prop where
  | nil : Rows []
  | cons (physical : SourceEqualityPhysicalPayload.own edge.entry.key.constraint = .ok (some []))
      (children : Children edge.children) (rest : Rows edges) : Rows (edge :: edges)

/-- A source child list contains only equality-free regions at its actual positions. -/
inductive Children : List (Value Symbol Guard) → Prop where
  | nil : Children []
  | cons (first : Region value) (rest : Children values) : Children (value :: values)
end

end MicroCFTA.SourceEqualityPartialPlainRegion
