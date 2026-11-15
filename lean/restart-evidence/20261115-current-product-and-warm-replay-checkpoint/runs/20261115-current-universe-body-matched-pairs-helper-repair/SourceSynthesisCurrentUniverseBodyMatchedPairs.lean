import MicroCFTA.SourceSynthesisCurrentUniverseBodyChildClassification
import MicroCFTA.SourceRecursiveIntersectionKernel
import MicroCFTA.SourceQuotientEnvironment

/-!
# Matched rows of the current stored universe body

The current catalog escapes reserved arrow names.
Equal-symbol catalog rows have equal keys when their arities agree.
Canonical physical records then identify the complete rows.
Every other actual matched pair has an arity mismatch.
-/
namespace MicroCFTA.SourceSynthesisCurrentUniverseBodyMatchedPairs
open Cache Language InternedConstructorTemplates InternedProbeProvenance InternedNestedFacts
open InternedEdgeResidency
open InternedBinderProtocol (NodeKey Reference)
open SourceSynthesisTypeSyntax (Library Query)
open SourceSynthesisGeneralizeSyntax (Guard top)
open SourceSynthesisFirstOrderConstruction (Expression)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "literal" => SourceSynthesisLabelProgramBuildRoles.literal
local notation "ordinarySymbols" => SourceSynthesisUniverseCallerBoundary.ordinarySymbols

set_option autoImplicit false

private theorem descriptor_not_arrow (lib : Library) (query : Query)
    (descriptor : String × Nat)
    (included : descriptor ∈ SourceSynthesisUniverseBody.descriptors
      (SourceSynthesisCurrentContext.constructorCatalog lib query)) : descriptor.1 ≠ "->" := by
  rw [SourceSynthesisUniverseBody.descriptors, List.mem_append] at included
  rcases included with rigid | catalog
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at rigid
    rcases rigid with rfl | rfl | rfl | rfl <;> decide
  · exact (SourceSynthesisCurrentContext.constructorCatalog_separate lib query descriptor catalog).2.1

private theorem matching_keys
    (lib : Library) (query : Query) (name : Reference)
    (arrow : EdgeValue Symbol Guard) (rows : List (EdgeValue Symbol Guard))
    (arrowSymbol : arrow.entry.key.symbol = literal "->")
    (catalog : All₂ (fun (descriptor : String × Nat) (row : EdgeValue Symbol Guard) =>
      row.children = List.replicate descriptor.2 (.reference name) ∧
      row.entry.key = ⟨literal descriptor.1, List.replicate descriptor.2 (.ref name), top⟩)
      (SourceSynthesisUniverseBody.descriptors (SourceSynthesisCurrentContext.constructorCatalog lib query)) rows)
    (left right : EdgeValue Symbol Guard) (leftMember : left ∈ arrow :: rows)
    (rightMember : right ∈ arrow :: rows)
    (symbols : left.entry.key.symbol = right.entry.key.symbol)
    (lengths : left.children.length = right.children.length) : left.entry.key = right.entry.key := by
  rcases List.mem_cons.mp leftMember with rfl | leftMember
  · rcases List.mem_cons.mp rightMember with rfl | rightMember
    · rfl
    · obtain ⟨descriptor, included, _children, key⟩ := SourceQuotientEnvironment.member_right catalog right rightMember
      have names : literal "->" = literal descriptor.1 := by simpa only [arrowSymbol, key] using symbols
      have same : "->" = descriptor.1 := congrArg Prod.fst names
      exact (descriptor_not_arrow lib query descriptor included same.symm).elim
  · rcases List.mem_cons.mp rightMember with rfl | rightMember
    · obtain ⟨descriptor, included, _children, key⟩ := SourceQuotientEnvironment.member_right catalog left leftMember
      have names : literal descriptor.1 = literal "->" := by simpa only [arrowSymbol, key] using symbols
      have same : descriptor.1 = "->" := congrArg Prod.fst names
      exact (descriptor_not_arrow lib query descriptor included same).elim
    · obtain ⟨first, _includedFirst, firstChildren, firstKey⟩ := SourceQuotientEnvironment.member_right catalog left leftMember
      obtain ⟨second, _includedSecond, secondChildren, secondKey⟩ := SourceQuotientEnvironment.member_right catalog right rightMember
      have arities : first.2 = second.2 := by
        simpa only [firstChildren, secondChildren, List.length_replicate] using lengths
      have names : literal first.1 = literal second.1 := by simpa only [firstKey, secondKey] using symbols
      rw [firstKey, secondKey, names, arities]

/-- Actual current-body hash-join pairs are self pairs or arity mismatches. -/
theorem current_stored_universe_body_matching_pairs
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (lib : Library) (query : Query) (signed : Int) (whole : Expression)
    (accepted : SourceSynthesisCurrentConstruction.firstOrderRaw lib query signed = .ok whole)
    (rootValue : Value Symbol Guard) (sourceHeap : InternedConstructorTemplates.State Symbol Guard)
    (built : InternedFreshOrdinaryConstruction.build (ordinarySymbols whole) [] empty = .done rootValue sourceHeap)
    (key : NodeKey) (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (stored : sourceHeap.nodeRecords key = some (.mu entry body depth ordinary))
    (heap : InternedConstructorTemplates.State Symbol Guard) (facts : Facts heap) (growth : Grows sourceHeap heap) :
    ∃ (bodyEntry : Interned NodeKey) (rows : List (EdgeValue Symbol Guard)),
      body = .node bodyEntry rows 0 [.interned entry.identity] ∧
      (∀ pair ∈ SourceRecursiveIntersectionKernel.pairs rows rows,
        pair.1 = pair.2 ∨ pair.1.children.length ≠ pair.2.children.length) := by
  obtain ⟨bodyEntry, _marker, arrow, rows, bodyEq, _bodyAvailable, _markerRead, _arrowChildren,
      arrowKey, catalog, _markerClosed, _markerAvailable, _markerAtoms, residents, _retained⟩ :=
    SourceSynthesisCurrentUniverseBodyChildClassification.current_stored_universe_body_physical_children_after_growth
      lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored heap facts growth
  refine ⟨bodyEntry, canonicalEdges (arrow :: rows), bodyEq, ?_⟩
  intro pair member
  obtain ⟨left, leftMember, right, rightMember, symbols, same⟩ :=
    (SymbolicHashJoin.hashJoin_member (fun row : EdgeValue Symbol Guard => row.entry.key.symbol)
      Prod.mk (canonicalEdges (arrow :: rows)) (canonicalEdges (arrow :: rows)) pair).mp member
  rw [← same]
  by_cases arity : left.children.length = right.children.length
  · left
    have keys := matching_keys lib query (.interned entry.identity) arrow rows
      (by simp only [arrowKey]) catalog left right
      (canonicalEdges_member _ left leftMember) (canonicalEdges_member _ right rightMember) symbols arity
    apply Option.some.inj
    calc
      some left = heap.edgeRecords left.entry.key := (residents left leftMember).1.symm
      _ = heap.edgeRecords right.entry.key := congrArg heap.edgeRecords keys
      _ = some right := (residents right rightMember).1
  · exact .inr arity

end MicroCFTA.SourceSynthesisCurrentUniverseBodyMatchedPairs
