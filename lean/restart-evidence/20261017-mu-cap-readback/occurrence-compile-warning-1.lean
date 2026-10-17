import MicroCFTA.SourceCurrentConstrainedCapNativeOccurrenceCode

/-!
# Joint cap and occurrence laws through actual native compilation

Literal row and child walks retain their complete source requests. Row
budgets use only actual zipped children. Ordinary construction places each
positive maximal occurrence outside its children. These local certificates
retain recursive request laws as premises. They do not assert completion.
-/
namespace MicroCFTA.SourceCurrentConstrainedCapNativeOccurrenceCompile
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency InternedNestedFacts
open InternedBinderProtocol IntersectionFlatMemoKeyDomain
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceCurrentConstrainedCapNativeOccurrenceCode
open SourceCurrentConstrainedCapNativeOccurrenceCache
open SourceCurrentConstrainedCapPairOccurrences (Classified FreeLE FreeBelow sourceWeight)
open SourceCurrentConstrainedCapNonplainRank (pairRank rank)
open SourceCurrentConstrainedCap (Cap Edge)
open SourceEqualityAnnotationLanguage (Annotated)
variable {Symbol Guard : Type}
variable (annotation : Guard → Prop) (source : InternedConstructorTemplates.State Symbol Guard)
  (representation : InternedConstructorTemplates.State Symbol Guard → Prop)
variable [DecidableEq (EdgeKey Symbol Guard)]

/-- Every joined row budget is nonincreasing and is strict at a positive enclosing rank. -/
theorem row_budget (domain : Interned DomainKey) (left right : Value Symbol Guard)
    (first second : EdgeValue Symbol Guard) (leftMember : first ∈ nodeEdges left)
    (rightMember : second ∈ nodeEdges right) :
    edgeBudget annotation ⟨domain, first, second⟩ ≤ pairRank annotation left right ∧
      (edgeBudget annotation ⟨domain, first, second⟩ < pairRank annotation left right ∨ pairRank annotation left right = 0) := by
  have inclusive : edgeBudget annotation ⟨domain, first, second⟩ ≤ pairRank annotation left right := by
    apply edgeBudget_le
    intro children member
    have inside := List.of_mem_zip member
    exact Nat.add_le_add
      (SourceCurrentConstrainedCapNonplainRank.child_le annotation left first leftMember children.1 inside.1)
      (SourceCurrentConstrainedCapNonplainRank.child_le annotation right second rightMember children.2 inside.2)
  refine ⟨inclusive, ?_⟩
  by_cases zero : pairRank annotation left right = 0
  · exact .inr zero
  · left
    have nonplain : ¬ Annotated annotation left ∨ ¬ Annotated annotation right := by
      classical
      by_cases firstPlain : Annotated annotation left
      · right
        intro secondPlain
        apply zero
        simp only [pairRank, SourceCurrentConstrainedCapNonplainRank.rank_zero annotation left firstPlain,
          SourceCurrentConstrainedCapNonplainRank.rank_zero annotation right secondPlain, Nat.add_zero]
      · exact .inl firstPlain
    exact edgeBudget_lt annotation _ _ (by omega) (fun children member =>
      SourceCurrentConstrainedCapNonplainRank.zip_pair_lt annotation left right nonplain
        first second leftMember rightMember children member)

/-- Actual joined row compilation derives the same parent cap and ranked classifier. -/
theorem rows_certified [DecidableEq Symbol] (depth : Nat) (domain : Interned DomainKey)
    (left right : Value Symbol Guard) (facts : Facts source)
    (bindings : OriginalBindings annotation source domain.key) (inputs : NodeInputs source ⟨domain, left, right⟩)
    (leftCap : Cap annotation depth left) (rightCap : Cap annotation depth right)
    (state : Machine Symbol Guard) (valid : SourceRecursiveIntersectionKernel.Valid state)
    (represented : representation state.heap) :
    Certified annotation source representation (compileRows domain (nodeEdges left) (nodeEdges right)) state
      (fun after value => Available after.heap value ∧ Cap annotation depth value ∧
        Classified (sourceWeight annotation source) (pairRank annotation left right) value) := by
  let input := fun (_ : Machine Symbol Guard) (pair : EdgeValue Symbol Guard × EdgeValue Symbol Guard) =>
    Edge annotation depth pair.1 ∧ Edge annotation depth pair.2 ∧ EdgeInputs source ⟨domain, pair.1, pair.2⟩
  let output := fun (after : Machine Symbol Guard) (edge : EdgeValue Symbol Guard) =>
    EdgeResident after.heap edge ∧ Edge annotation depth edge ∧
      ∀ child ∈ edge.children, FreeLE (sourceWeight annotation source) (pairRank annotation left right) child ∧
        FreeBelow (sourceWeight annotation source) (pairRank annotation left right) child
  have walked := certified_walk annotation source representation
    (fun pair : EdgeValue Symbol Guard × EdgeValue Symbol Guard => requestEdge domain pair.1 pair.2)
    (pairs (nodeEdges left) (nodeEdges right)) input output
    (by intro _ _ _ _ known; exact known)
    (by intro before after growth edge known; exact ⟨edge_stable before after growth edge known.1, known.2⟩)
    (by
      intro pair member current currentValid currentRepresented known
      have inside := (pairs_member _ _ pair).mp member
      have bounds := row_budget annotation domain left right pair.1 pair.2 inside.1 inside.2.1
      apply certified_bind annotation source representation _ _ current currentValid currentRepresented _ _
        (request_edge annotation source representation depth ⟨domain, pair.1, pair.2⟩ current bindings known.2.2 known.1 known.2.1)
      intro result after _ _ _ returned
      refine ⟨returned.1, returned.2.1, ?_⟩
      intro child childMember
      have free := returned.2.2 child childMember
      refine ⟨fun name named => Nat.le_trans (free name named) bounds.1, ?_⟩
      intro name named
      rcases bounds.2 with smaller | zero
      · exact .inl (Nat.lt_of_le_of_lt (free name named) smaller)
      · exact .inr zero)
    state valid represented (by
      intro pair member
      have inside := (pairs_member _ _ pair).mp member
      exact ⟨SourceCurrentConstrainedCap.node_edge leftCap pair.1 inside.1,
        SourceCurrentConstrainedCap.node_edge rightCap pair.2 inside.2.1,
        SourceCurrentConstrainedCapOriginalSupport.rows_input source facts domain left right inputs
          pair.1 pair.2 inside.1 inside.2.1⟩)
  unfold compileRows
  apply certified_bind annotation source representation _ _ state valid represented _ _ walked
  intro values after afterValid _ _ returned
  exact node_work annotation source representation depth (pairRank annotation left right) values after afterValid
    (fun edge member => (returned edge member).1) (fun edge member => (returned edge member).2.1)
    (fun edge member => (returned edge member).2.2)

/-- Literal child compilation derives the row cap and exact zip budget from both node laws. -/
theorem children_certified (depth : Nat) (request : EdgeRequest Symbol Guard) (guard : Guard)
    (bindings : OriginalBindings annotation source request.domain.key) (inputs : EdgeInputs source request)
    (leftCap : Edge annotation depth request.left) (rightCap : Edge annotation depth request.right)
    (guardValid : depth = 0 → annotation guard) (state : Machine Symbol Guard)
    (valid : SourceRecursiveIntersectionKernel.Valid state) (represented : representation state.heap) :
    Certified annotation source representation
      ((walk (fun pair => requestNode request.domain pair.1 pair.2)
        (request.left.children.zip request.right.children)).bind fun values =>
          .work (makeEdge request.left.entry.key.symbol guard values) .pure) state
      (fun after value => EdgeResident after.heap value ∧ Edge annotation depth value ∧
        ∀ child ∈ value.children, FreeLE (sourceWeight annotation source) (edgeBudget annotation request) child) := by
  let input := fun (_ : Machine Symbol Guard) (pair : Value Symbol Guard × Value Symbol Guard) =>
    Cap annotation (depth - 1) pair.1 ∧ Cap annotation (depth - 1) pair.2 ∧
      NodeInputs source ⟨request.domain, pair.1, pair.2⟩
  let output := fun (after : Machine Symbol Guard) (value : Value Symbol Guard) =>
    Available after.heap value ∧ Cap annotation (depth - 1) value ∧
      FreeLE (sourceWeight annotation source) (edgeBudget annotation request) value
  have walked := certified_walk annotation source representation
    (fun pair : Value Symbol Guard × Value Symbol Guard => requestNode request.domain pair.1 pair.2)
    (request.left.children.zip request.right.children) input output
    (by intro _ _ _ _ known; exact known)
    (by intro before after growth value known; exact ⟨growth.available value known.1, known.2⟩)
    (by
      intro pair member current currentValid currentRepresented known
      have bound := childBudget_member annotation _ pair member
      apply certified_bind annotation source representation _ _ current currentValid currentRepresented _ _
        (request_node annotation source representation (depth - 1) ⟨request.domain, pair.1, pair.2⟩
          current bindings known.2.2 known.1 known.2.1)
      intro result after _ _ _ returned
      exact ⟨returned.1, returned.2.1, fun name named => Nat.le_trans (returned.2.2.free name named) bound⟩)
    state valid represented (by
      intro pair member
      have inside := List.of_mem_zip member
      have first := inputs.1 pair.1 inside.1
      have second := inputs.2 pair.2 inside.2
      have capped : Cap annotation (depth - 1) pair.1 ∧ Cap annotation (depth - 1) pair.2 := by
        cases depth with
        | zero => exact ⟨.plain 0 (leftCap.2 pair.1 inside.1), .plain 0 (rightCap.2 pair.2 inside.2)⟩
        | succ depth => exact ⟨leftCap pair.1 inside.1, rightCap pair.2 inside.2⟩
      exact ⟨capped.1, capped.2, first.1, second.1, first.2.1, second.2.1, first.2.2, second.2.2⟩)
  apply certified_bind annotation source representation _ _ state valid represented _ _ walked
  intro values after afterValid _ _ returned
  exact edge_work annotation source representation depth (edgeBudget annotation request)
    request.left.entry.key.symbol guard values after afterValid
    (fun value member => (returned value member).1) guardValid
    (fun value member => (returned value member).2.1) (fun value member => (returned value member).2.2)

end MicroCFTA.SourceCurrentConstrainedCapNativeOccurrenceCompile
