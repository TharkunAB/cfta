import MicroCFTA.InternedUnionReferences
import MicroCFTA.InternedSelectivePreparedSites

/-!
# Nested construction with retained references below root unions

Every binder body declares a source path for each enclosing input.
The path can use bare variables and union alternatives. The body itself
can be a nested binder when no enclosing input needs retention.
-/
namespace MicroCFTA.InternedUnionConstruction
open InternedNestedConstruction InternedUnionReferences

/-- Every enclosing lexical slot has a source path that preserves its free name. -/
def Declared (depth : Nat) (body : Syntax Symbol Guard) : Prop :=
  ∀ index < depth, Retains (index + 1) body

mutual
/-- Each nested binder retains all enclosing inputs through its declared source paths. -/
def Retentive (depth : Nat) : Syntax Symbol Guard → Prop
  | .empty | .var _ => True
  | .node edges => EdgesRetentive depth edges
  | .union members => ManyRetentive depth members
  | .binder _ body => Declared depth body ∧ Retentive (depth + 1) body
termination_by expression => sizeOf expression

/-- Source siblings share the same enclosing input requirements. -/
def ManyRetentive (depth : Nat) : List (Syntax Symbol Guard) → Prop
  | [] => True
  | first :: rest => Retentive depth first ∧ ManyRetentive depth rest
termination_by expressions => sizeOf expressions

/-- Source edge children use the same lexical input environment. -/
def EdgesRetentive (depth : Nat) : List (EdgeSyntax Symbol Guard) → Prop
  | [] => True
  | .mk _ _ children :: rest => ManyRetentive depth children ∧ EdgesRetentive depth rest
termination_by expressions => sizeOf expressions
end

end MicroCFTA.InternedUnionConstruction
