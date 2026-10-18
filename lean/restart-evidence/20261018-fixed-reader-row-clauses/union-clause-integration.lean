import MicroCFTA.SourceCurrentFixedReaderUnionClauses

set_option maxRecDepth 30000
set_option maxHeartbeats 5000000
set_option cbv.maxSteps 100000000

namespace MicroCFTA.FixedReaderUnionClauseIntegration
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedConstruction (Syntax Outcome)
open InternedFreshOrdinaryConstruction (build buildMany)
open InternedFreshOrdinaryStoredSubstitution (execute)
open InternedStoredSubstitution (Environment)
open InternedBinderProtocol (Reference)
open SourceCurrentConstrainedCapSourceHistory (Context)
open SourceEqualityRequiredCache (Ready)
open SourceCurrentLiteralRootParts (Literal Row)
open SourceCurrentLiteralLocalSimulation (Clauses)
open SourceCurrentLiteralNormalizationSimulation (Relation)
open SourceCurrentSourceDirectedCases (Below)
open SourceCurrentOpenPreorderSimulation (Mutual)

private def val (outcome : Outcome Nat Bool (Value Nat Bool)) : Value Nat Bool :=
  match outcome with | .done value _ => value | .pending .. => .empty
private def leaf : Syntax Nat Bool := .node [.mk 3 false []]
private def members : List (Syntax Nat Bool) := [.var 0,leaf]
private def body : Syntax Nat Bool := .union members
private def source : Syntax Nat Bool := .binder false body
private def built := build source [] empty
private def root := val built
private def reader := built.state
private def raw := val (build body [.reference .depth] reader)
private def values := [.reference .depth,val (build leaf [.reference .depth] reader)]
private def nullMap : Environment Nat Bool := fun _ => none
private def unrelated : Reference := .uninterned 99
private def noSource : Value Nat Bool → Value Nat Bool → Prop := fun _ _ => False

private theorem actual : build source [] empty = .done root reader := by cbv
private theorem ready : Ready reader := SourceEqualityRequiredCache.constructed source root reader actual
private theorem context : Context reader [.reference .depth] :=
  ⟨SourceRecursiveIntersectionSemanticHeap.context reader ready.semantic _ (by
      intro value member
      obtain rfl := List.mem_singleton.mp member
      exact InternedNestedProvenance.depth_available reader),ready.semantic.2⟩
private theorem raw_call : build body [.reference .depth] reader = .done raw reader := by cbv
private theorem available : Available reader raw :=
  (InternedFreshOrdinaryFacts.build_verified body _ reader context.base.normal.facts context.base.inputs).result
    raw reader raw_call
private theorem filtered : run (withoutSelfReference unrelated raw) reader = (raw,reader) := by cbv
private theorem stored : execute raw nullMap reader = .done raw reader := by cbv
private theorem many : buildMany members [.reference .depth] reader = .done values reader := by cbv

private theorem children_refl (children : List (Value Nat Bool)) :
    All₂ (Mutual (Relation noSource)) children children := by
  induction children with
  | nil => exact .nil
  | cons child rest ih => exact .cons ⟨.inl (Below.refl child),.inl (Below.refl child)⟩ ih

private theorem assembled : Clauses reader (Relation noSource) raw raw := by
  apply SourceCurrentFixedReaderUnionClauses.union members [.reference .depth] [.reference .depth]
    reader reader reader reader reader context context raw raw raw_call raw_call ready
    (grows_refl reader) (grows_refl reader) available available unrelated unrelated nullMap nullMap
    (by intro name value impossible; cases impossible) (by intro name value impossible; cases impossible)
    raw raw raw raw filtered filtered stored stored values values many many noSource
  · intro index expression firstMember secondMember _ firstSelected secondSelected _ _ atom output part retained called
    have same : firstMember = secondMember := Option.some.inj (firstSelected.symm.trans secondSelected)
    subst secondMember
    exact ⟨atom,output,part,retained,called,
      SourceCurrentLiteralLocalSimulation.below reader (Relation noSource)
        (fun value => .inl (Below.refl value)) output output (Below.refl output)⟩
  · intro index expression firstMember secondMember _ firstSelected secondSelected _ _ original output part called alive
    have same : firstMember = secondMember := Option.some.inj (firstSelected.symm.trans secondSelected)
    subst secondMember
    exact ⟨original,output,part,called,alive,rfl,rfl,children_refl output.children⟩

private theorem actual_witness :
    build source [] empty = .done root reader ∧ Ready reader ∧
    run (withoutSelfReference unrelated raw) reader = (raw,reader) ∧
    execute raw nullMap reader = .done raw reader ∧
    Literal raw (.reference .depth) ∧
    (∃ row, Row raw row ∧ row.entry.key.symbol = 3 ∧ row.entry.key.constraint = false) ∧
    Clauses reader (Relation noSource) raw raw := by
  refine ⟨actual,ready,filtered,stored,?_,?_,assembled⟩
  · cbv
    exact .union List.mem_cons_self (.reference .depth)
  · refine ⟨(run (makeEdge 3 false []) reader).1,?_,by cbv,by cbv⟩
    cbv
    exact .union (List.mem_cons_of_mem _ List.mem_cons_self) (.node List.mem_cons_self)

/-- Actual atom and full-row fragments instantiate the union theorem at one original reader. -/
theorem actual_atom_and_row :
    build source [] empty = .done root reader ∧ Ready reader ∧
    run (withoutSelfReference unrelated raw) reader = (raw,reader) ∧
    execute raw nullMap reader = .done raw reader ∧
    Literal raw (.reference .depth) ∧
    (∃ row, Row raw row ∧ row.entry.key.symbol = 3 ∧ row.entry.key.constraint = false) ∧
    Clauses reader (Relation noSource) raw raw := actual_witness

end MicroCFTA.FixedReaderUnionClauseIntegration
