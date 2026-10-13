import MicroCFTA.EqualityReduction

/-!
# Equality reduction with merged peer projections

The current source merges each peer projection before the target intersection.
A merge can add terms. The original edge constraints remain attached, and every
edit still intersects the original node. Thus a language-superset merge suffices
for the complete constrained-language preservation theorem. This module does
not assume that repeated passes terminate.
-/
namespace MicroCFTA.MergedEqualityReduction
open Language EqualityNormalize EqualityReduction

/-- Insert the current source merge call after each peer projection. -/
def merged (ops : Operations Node Symbol) (merge : Node → Node) : Operations Node Symbol :=
  {ops with project := fun nodes path => merge (ops.project nodes path)}

/-- Language-superset merging preserves every local reduction law. -/
theorem merged_laws (ops : Operations Node Symbol) (laws : Laws ops) (merge : Node → Node)
    (superset : ∀ node term, ops.meaning node term → ops.meaning (merge node) term) :
    Laws (merged ops merge) where
  empty := laws.empty
  intersect := laws.intersect
  project := fun nodes term path subtree proper accepted found =>
    superset _ subtree (laws.project nodes term path subtree proper accepted found)
  require_narrow := laws.require_narrow
  require_keep := laws.require_keep
  edit_narrow := laws.edit_narrow
  edit_keep := laws.edit_keep
  contradiction := laws.contradiction

/-- The transformed operation produces exactly the new source target schedule. -/
theorem classEdits_eq (ops : Operations Node Symbol) (merge : Node → Node)
    (paths : Class) (nodes : List Node) :
    classEdits (merged ops merge) paths nodes =
      paths.map (fun path => (path, intersectList ops
        ((EqualityNarrowing.others paths path).map (fun other => merge (ops.project nodes other))))) := by
  rfl

/-- Merging peer targets cannot add a forest term through an intersecting edit. -/
theorem class_narrow (ops : Operations Node Symbol) (laws : Laws ops) (merge : Node → Node)
    (paths : Class) (nodes : List Node) (term : Term Symbol) :
    Forest ops (reduceClass (merged ops merge) paths nodes) term → Forest ops nodes term :=
  laws.edit_narrow _ nodes term

/-- The new single-pass schedule preserves the complete original constrained language. -/
theorem constrained_pass_exact [DecidableEq Node]
    (ops : Operations Node Symbol) (laws : Laws ops) (merge : Node → Node)
    (superset : ∀ node term, ops.meaning node term → ops.meaning (merge node) term)
    (localClasses inherited : Constraints) (active : Active localClasses)
    (before : List Node) (term : Term Symbol) :
    (Forest ops (pass (merged ops merge) localClasses inherited before) term ∧
      Satisfies term localClasses ∧ Satisfies term inherited) ↔
    Forest ops before term ∧ Satisfies term localClasses ∧ Satisfies term inherited :=
  EqualityReduction.constrained_pass_exact (merged ops merge) (merged_laws ops laws merge superset)
    localClasses inherited active before term

/-- Every completed repetition of the new schedule preserves the same constrained language. -/
theorem constrained_reduce_exact [DecidableEq Node]
    (ops : Operations Node Symbol) (laws : Laws ops) (merge : Node → Node)
    (superset : ∀ node term, ops.meaning node term → ops.meaning (merge node) term)
    (localClasses inherited : Constraints) (active : Active localClasses)
    (fuel : Nat) (before after : List Node)
    (completed : reduce (merged ops merge) localClasses inherited fuel before = some after)
    (term : Term Symbol) :
    (Forest ops after term ∧ Satisfies term localClasses ∧ Satisfies term inherited) ↔
      Forest ops before term ∧ Satisfies term localClasses ∧ Satisfies term inherited :=
  EqualityReduction.constrained_reduce_exact (merged ops merge) (merged_laws ops laws merge superset)
    localClasses inherited active fuel before after completed term

end MicroCFTA.MergedEqualityReduction
