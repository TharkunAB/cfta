import MicroCFTA.MergedRawLeafSource

/-!
# Language coverage of the actual merged leaf worker

For a nullary term, a guard interpreter decides acceptance at an outgoing
row with the term's symbol. The physical merge preserves every such
acceptance when the interpreter accepts Top. This does not assume that
the merge preserves rejected terms.
-/
namespace MicroCFTA.MergedRawLeafLanguage
open SourceGuards FullSyntax InternedConstructorTemplates
open EqualityLeafProjectionCompileAvailability EqualityLeafProjectionRepresentation
open EqualityRawLeafInventory (Leaf)
open EqualityRawLeafConstruction (ConstraintKey)
open EqualityRawLeafCompiler (build)

noncomputable local instance : DecidableEq ConstraintKey := by classical exact inferInstance

/-- Accept a nullary term through its symbol and the residual guard on an actual row. -/
def AcceptsAt (holds : Guard Formula → Prop) (symbol : Fin symbols)
    (value : Value (Fin symbols) ConstraintKey) : Prop :=
  ∃ guard, (symbol, guard) ∈ MergedRawLeafSource.rows value ∧ holds guard

/-- Every accepted actual input leaf remains accepted after physical grouping and construction. -/
theorem worker_covers (leaf : Leaf initial symbols) (value : Value (Fin symbols) ConstraintKey)
    (state : State (Fin symbols) ConstraintKey) (facts : Facts state)
    (represented : Represents build (.leaf leaf) state value)
    (order : List (Fin symbols)) (complete : MergedRawLeafSource.Complete order value)
    (holds : Guard Formula → Prop) (top : holds .top) (symbol : Fin symbols)
    (accepted : AcceptsAt holds symbol value) :
    AcceptsAt holds symbol (run (MergedRawLeafSource.worker order value) state).1 := by
  obtain ⟨guard, member, accepted⟩ := accepted
  obtain ⟨row, selected, same⟩ :=
    (MergedRawLeafSource.represented_rows leaf value state facts represented symbol guard).mp member
  have original : ∃ row, leaf symbol row ∧ holds row.val.val :=
    ⟨row, selected, same.symm ▸ accepted⟩
  obtain ⟨merged, selected, accepted⟩ :=
    MergedRawLeaves.covers leaf symbol (fun row => holds row.val.val) top original
  obtain ⟨edge, included, key⟩ :=
    (MergedRawLeafSource.worker_keys leaf value state facts represented order complete
      (EqualityRawLeafConstruction.key (symbol, merged.val.val))).mpr ⟨symbol, merged, selected, rfl⟩
  refine ⟨merged.val.val, List.mem_map.mpr ⟨edge, included, ?_⟩, accepted⟩
  exact Prod.ext (congrArg EdgeKey.symbol key) (congrArg (fun key => key.constraint.2) key)

end MicroCFTA.MergedRawLeafLanguage
