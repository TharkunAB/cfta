import MicroCFTA.SourceCurrentConstrainedCapNativeOccurrenceCompile
import MicroCFTA.SourceCurrentConstrainedCapConstruction
import MicroCFTA.SourceRecursiveIntersectionSemanticHeap

set_option linter.all true
set_option pp.explicit true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
set_option format.width 200
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000

namespace MicroCFTA.OccurrenceIndependentKernels
open Cache InternedConstructorTemplates InternedProbeProvenance InternedNestedFacts InternedRecordCoherence InternedEdgeResidency
open InternedBinderProtocol (NodeKey Reference)
open InternedNestedConstruction (Syntax EdgeSyntax Outcome)
open SourceRecursiveIntersectionKernel (Machine Valid)
open SourceRecursiveIntersectionCode
open SourceCurrentConstrainedCap (Cap)
open SourceCurrentConstrainedCapNativeOccurrenceCache (OriginalBindings NodeInputs edgeBudget)
open SourceCurrentConstrainedCapNativeOccurrenceCode (Certified)
open SourceCurrentConstrainedCapNonplainRank (pairRank)
open SourceCurrentConstrainedCapPairOccurrences (Classified sourceWeight)
open SourceCurrentConstrainedCapConstruction (Typed ManyTyped EdgesTyped)
private def annotation (guard : Bool) : Prop := guard = true
private def plainExpression : Syntax Nat Bool := .node [.mk 1 true []]
private def badExpression : Syntax Nat Bool := .node [.mk 0 false [plainExpression]]
private def recursiveExpression : Syntax Nat Bool := .binder false (.node [.mk 2 true [.var 0]])
private def expression : Syntax Nat Bool := .union [badExpression, recursiveExpression]
private def leafRun := InternedFreshOrdinaryConstruction.build plainExpression [] (empty : State Nat Bool)
private def badRun := InternedFreshOrdinaryConstruction.build badExpression [] (empty : State Nat Bool)
private def actual := InternedFreshOrdinaryConstruction.build expression [] (empty : State Nat Bool)
private def result (outcome : Outcome Nat Bool (Value Nat Bool)) : Value Nat Bool :=
  match outcome with | .done value _ => value | .pending .. => .empty
private def root := result actual
private def bad := result badRun
private def leaf := result leafRun
private def source := actual.state
private def rootEntry : Interned NodeKey := match root with
  | .union entry _ _ _ => entry
  | _ => ⟨0, .node []⟩
private def fallback : EdgeValue Nat Bool := .mk ⟨0, ⟨0, [], false⟩⟩ []
private def badRow := (nodeEdges bad).headD fallback
private def leafRow := (nodeEdges leaf).headD fallback
private def machine : Machine Nat Bool := ⟨source, Cache.emptyState⟩
private def domain := IntersectionEmptyDomain.emptyDomain

set_option cbv.maxSteps 100000000 in
private theorem done : actual = .done root source := by cbv

set_option cbv.maxSteps 100000000 in
private theorem bad_done : badRun = .done bad badRun.state := by cbv

private theorem union_shape : ∃ entry level free members,
    root = .union entry members level free ∧ bad ∈ members := by
  refine ⟨rootEntry, root.depth, root.free, unionMembers root, ?_, ?_⟩ <;> cbv

private theorem root_closed : root.free = [] := by cbv
private theorem bad_closed : bad.free = [] := by cbv
private theorem bad_member : badRow ∈ nodeEdges bad := by cbv
private theorem leaf_member : leaf ∈ badRow.children := by cbv
private theorem leaf_row_member : leafRow ∈ nodeEdges leaf := by cbv
private theorem bad_guard : badRow.entry.key.constraint = false := by cbv

private theorem typed : Typed annotation 1 expression [] := by
  simp only [expression, badExpression, plainExpression, recursiveExpression, Typed, ManyTyped, EdgesTyped]
  refine ⟨⟨(by omega), ⟨⟨(by intro _; rfl), trivial, trivial⟩, trivial⟩, trivial⟩, ?_, trivial⟩
  intro name
  exact ⟨(by intro _; rfl), ⟨Cap.plain 0 (.reference name), trivial⟩, trivial⟩

/-- Closed constrained source construction produces its own support, positive and zero zip budgets, and local row and union certificates. -/
theorem constructed_source_support_and_certificates :
    ∃ entry members level free,
      InternedFreshOrdinaryConstruction.build expression [] (empty : State Nat Bool) = .done root source ∧
      root = .union entry members level free ∧ bad ∈ members ∧
      OriginalBindings annotation source domain.key ∧ NodeInputs source ⟨domain, bad, bad⟩ ∧
      NodeInputs source ⟨domain, root, bad⟩ ∧ Cap annotation 1 root ∧ Cap annotation 1 bad ∧
      0 < pairRank annotation bad bad ∧ pairRank annotation leaf leaf = 0 ∧
      edgeBudget annotation ⟨domain, badRow, badRow⟩ < pairRank annotation bad bad ∧
      edgeBudget annotation ⟨domain, leafRow, leafRow⟩ = 0 ∧
      Certified annotation source InternedStoredMuOrigins.Normal
        (compileRows domain (nodeEdges bad) (nodeEdges bad)) machine
        (fun after value => Available after.heap value ∧ Cap annotation 1 value ∧
          Classified (sourceWeight annotation source) (pairRank annotation bad bad) value) ∧
      Certified annotation source InternedStoredMuOrigins.Normal
        ((walk (fun member => requestNode domain member bad) members).bind fun values =>
          .work (makeUnion values) .pure) machine
        (fun after value => Available after.heap value ∧ Cap annotation 1 value ∧
          Classified (sourceWeight annotation source) (pairRank annotation root bad) value) := by
  have built := done
  have physical := (InternedFreshOrdinaryFacts.build_verified expression [] (empty : State Nat Bool) empty_facts
    (by intro value member; cases member)).result root source built
  have semantic := SourceRecursiveIntersectionSemanticHeap.constructed expression root source built
  have facts := semantic.1.normal.facts
  have rootCap := (SourceCurrentConstrainedCapConstruction.build annotation 1 expression [] (empty : State Nat Bool)
    empty_facts (by intro value member; cases member) typed (SourceCurrentHereditaryConstruction.MuStored.empty annotation)).result
      root source built
  obtain ⟨entry, level, free, members, same, member⟩ := union_shape
  have badAvailable : Available source bad := by
    rw [same] at physical
    exact physical.children bad member
  have badCap : Cap annotation 1 bad := by
    rw [same] at rootCap
    exact SourceCurrentConstrainedCap.union_member rootCap bad member
  have leafCap : Cap annotation 0 leaf := SourceCurrentConstrainedCap.node_edge badCap badRow bad_member leaf leaf_member
  have leafAnnotated := leafCap.annotated rfl
  have leafRank := SourceCurrentConstrainedCapNonplainRank.rank_zero annotation leaf leafAnnotated
  have zero : pairRank annotation leaf leaf = 0 := by simp only [pairRank, leafRank, Nat.add_zero]
  have badNonplain : ¬SourceEqualityAnnotationLanguage.Annotated annotation bad := by
    intro annotated
    have guard := (SourceCurrentHereditaryConstructors.node_edge annotated badRow bad_member).1
    change badRow.entry.key.constraint = true at guard
    rw [bad_guard] at guard
    cases guard
  have positive : 0 < pairRank annotation bad bad := by
    have rankPositive := (SourceCurrentConstrainedCapNonplainRank.rank_pos_iff annotation bad).mpr badNonplain
    simp only [pairRank]
    omega
  have firstBudget := SourceCurrentConstrainedCapNativeOccurrenceCompile.row_budget annotation domain bad bad
    badRow badRow bad_member bad_member
  have strict : edgeBudget annotation ⟨domain, badRow, badRow⟩ < pairRank annotation bad bad := by
    rcases firstBudget.2 with lower | impossible
    · exact lower
    · omega
  have lastBudget := SourceCurrentConstrainedCapNativeOccurrenceCompile.row_budget annotation domain leaf leaf
    leafRow leafRow leaf_row_member leaf_row_member
  have zeroBudget : edgeBudget annotation ⟨domain, leafRow, leafRow⟩ = 0 := by omega
  have bindings := SourceCurrentConstrainedCapOriginalSupport.empty annotation source
  have badInputs := SourceCurrentConstrainedCapOriginalSupport.closed_inputs source facts domain bad bad
    badAvailable badAvailable bad_closed bad_closed
  have rootInputs := SourceCurrentConstrainedCapOriginalSupport.closed_inputs source facts domain root bad
    physical badAvailable root_closed bad_closed
  have machineValid : Valid machine := ⟨facts, Cache.empty_valid⟩
  have rows := SourceCurrentConstrainedCapNativeOccurrenceCompile.rows_certified annotation source InternedStoredMuOrigins.Normal
    1 domain bad bad facts bindings badInputs badCap badCap machine machineValid semantic.1.normal
  have unions := SourceCurrentConstrainedCapNativeOccurrenceCompile.left_union_certified annotation source InternedStoredMuOrigins.Normal
    1 domain entry members level free bad facts bindings (same ▸ rootInputs) (same ▸ rootCap) badCap
    (fun _ normal => normal) machine machineValid semantic.1.normal
  exact ⟨entry, members, level, free, built, same, member, bindings, badInputs, rootInputs, rootCap, badCap,
    positive, zero, strict, zeroBudget, rows, same ▸ unions⟩

#print axioms constructed_source_support_and_certificates
#check @constructed_source_support_and_certificates
end MicroCFTA.OccurrenceIndependentKernels
